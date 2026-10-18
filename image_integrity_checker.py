#!/usr/bin/env python3
"""
Image Metadata Integrity Checker
================================
A GUI tool that looks for signs that an image's metadata (and the file itself)
has been edited, forged, damaged, or tampered with.

Checks performed
----------------
Container / structure
  * File signature vs. extension (disguised files)
  * JPEG: marker walk, truncation, missing EOI, data appended after EOI
    (hidden payloads / polyglots), duplicate EXIF blocks, Photoshop/Adobe blocks
  * PNG : CRC-32 validation of every chunk, chunk order, data after IEND
  * WebP / BMP / GIF: header size and trailer consistency
  * Full decode test (verify + load)

Metadata consistency
  * EXIF date logic (modified < captured, future dates, placeholders, FS time)
  * EXIF pixel dimensions vs. real dimensions
  * Editing-software tags (Software / XMP CreatorTool / comments / PNG text)
  * Make/Model coherence, missing camera tags, invalid Orientation
  * GPS validity and GPS-time vs. capture-time agreement
  * Embedded EXIF thumbnail vs. main image (aspect + pixel difference)
  * XMP: edit history, DocumentID vs OriginalDocumentID, date agreement
  * C2PA / Content Credentials presence

EXIF tampering forensics (manipulated / newly added fields)
  * Raw TIFF parse of the EXIF block: out-of-order or duplicate tags, wrong data
    types, tags in the wrong IFD, text overwritten in place (residue after NUL),
    overlapping regions, unreferenced "slack" bytes, broken MakerNote offsets
  * MakerNote brand vs. Make/Model, byte order vs. manufacturer
  * Fields newer than the declared ExifVersion (injected by other software)
  * Fields cameras never write (Rating, Windows XP* properties, embedded XMP/IPTC)
  * Cross-field logic: ExposureTime vs ShutterSpeedValue, FNumber vs ApertureValue,
    focal length vs 35mm equivalent and lens range, invalid enumerations
  * Field-level diff against a baseline or an original image (added / changed / removed)
  * Suspect fields are highlighted in the Metadata tab

Pixel forensics
  * Error Level Analysis (ELA) image + block outlier heuristic (JPEG)
  * Estimated JPEG quality from quantisation tables

Baseline integrity
  * Create a SHA-256 + metadata-hash manifest and verify files against it later

All checks are heuristics. A finding is a reason to look closer, not proof.

Requires:  pip install pillow      (tkinter ships with most Python installs)
"""

import hashlib
import html
import io
import json
import math
import os
import queue
import re
import statistics
import struct
import sys
import threading
import zlib
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from typing import Dict, List, Optional

try:
    from PIL import Image, ImageChops, ImageStat
    from PIL.ExifTags import GPSTAGS, TAGS

    Image.MAX_IMAGE_PIXELS = 250_000_000
    HAS_PIL = True
except ImportError:  # pragma: no cover
    HAS_PIL = False

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk

    HAS_TK = True
except ImportError:  # pragma: no cover
    HAS_TK = False

# --------------------------------------------------------------------------- #
# Constants
# --------------------------------------------------------------------------- #
SEVERITY_WEIGHT = {"INFO": 0, "LOW": 5, "MEDIUM": 15, "HIGH": 40}
SEVERITY_ORDER = {"HIGH": 0, "MEDIUM": 1, "LOW": 2, "INFO": 3}

EDITORS = (
    "photoshop", "gimp", "lightroom", "paint.net", "affinity", "snapseed",
    "pixelmator", "picsart", "canva", "facetune", "photoscape", "acdsee",
    "capture one", "darktable", "rawtherapee", "luminar", "fotor", "paint shop",
    "corel", "krita", "pixlr", "lightx", "vsco", "polarr", "photopea",
    "imagemagick", "gd-jpeg", "irfanview", "xnview", "stable diffusion",
    "midjourney", "dall-e", "firefly", "photodirector", "picmonkey",
)

BRANDS = (
    "canon", "nikon", "sony", "apple", "samsung", "fujifilm", "olympus",
    "panasonic", "google", "huawei", "xiaomi", "oneplus", "leica", "pentax",
    "gopro", "dji", "motorola", "casio", "kodak", "ricoh", "sigma", "hasselblad",
)

EXT_TYPES = {
    ".jpg": "JPEG", ".jpeg": "JPEG", ".jpe": "JPEG", ".jfif": "JPEG",
    ".png": "PNG", ".gif": "GIF", ".bmp": "BMP", ".webp": "WEBP",
    ".tif": "TIFF", ".tiff": "TIFF", ".heic": "HEIF", ".heif": "HEIF",
    ".avif": "HEIF",
}
IMAGE_EXTS = tuple(EXT_TYPES)

STD_LUMA_TABLE = [
    16, 11, 10, 16, 24, 40, 51, 61, 12, 12, 14, 19, 26, 58, 60, 55,
    14, 13, 16, 24, 40, 57, 69, 56, 14, 17, 22, 29, 51, 87, 80, 62,
    18, 22, 37, 56, 68, 109, 103, 77, 24, 35, 55, 64, 81, 104, 113, 92,
    49, 64, 78, 87, 103, 121, 120, 101, 72, 92, 95, 98, 112, 100, 103, 99,
]
STD_LUMA_SUM = sum(STD_LUMA_TABLE)

_SCAN_RE = re.compile(rb"\xff[^\x00\xd0-\xd7\xff]")


def _resample(name):
    return getattr(getattr(Image, "Resampling", Image), name)


# ---- EXIF forensics tables --------------------------------------------------
C_IFD0, C_EXIF, C_GPS, C_XMP = "EXIF (IFD0)", "EXIF (Exif)", "GPS", "XMP (key fields)"
IFD_CATEGORY = {"IFD0": C_IFD0, "IFD1": "EXIF (IFD1)", "Exif": C_EXIF, "GPS": C_GPS, "Interop": "EXIF (Interop)"}
TRACKED_CATEGORIES = (C_IFD0, C_EXIF, C_GPS, C_XMP, "JPEG comments", "PNG text")
DERIVED_FIELDS = {"Decimal coordinates", "Map link"}

TYPE_SIZES = {1: 1, 2: 1, 3: 2, 4: 4, 5: 8, 6: 1, 7: 1, 8: 2, 9: 4, 10: 8, 11: 4, 12: 8, 13: 4, 16: 8}
TYPE_NAMES = {1: "BYTE", 2: "ASCII", 3: "SHORT", 4: "LONG", 5: "RATIONAL", 6: "SBYTE", 7: "UNDEFINED",
              8: "SSHORT", 9: "SLONG", 10: "SRATIONAL", 11: "FLOAT", 12: "DOUBLE", 13: "IFD", 16: "LONG8"}

# tag id -> (allowed data types, required count or None)
EXPECTED_TYPES = {
    0x010F: ({2}, None), 0x0110: ({2}, None), 0x0112: ({3}, 1), 0x011A: ({5}, 1), 0x011B: ({5}, 1),
    0x0128: ({3}, 1), 0x0131: ({2}, None), 0x0132: ({2}, 20), 0x013B: ({2}, None), 0x8298: ({2}, None),
    0x829A: ({5}, 1), 0x829D: ({5}, 1), 0x8822: ({3}, 1), 0x8827: ({3, 4}, None), 0x9000: ({7}, 4),
    0x9003: ({2}, 20), 0x9004: ({2}, 20), 0x9201: ({10}, 1), 0x9202: ({5}, 1), 0x9204: ({10}, 1),
    0x9207: ({3}, 1), 0x9209: ({3}, 1), 0x920A: ({5}, 1), 0x9286: ({7}, None), 0x927C: ({7}, None),
    0xA000: ({7}, 4), 0xA001: ({3}, 1), 0xA002: ({3, 4}, 1), 0xA003: ({3, 4}, 1), 0xA434: ({2}, None),
}

# Tags that normally live in only one IFD
IFD0_ONLY = {0x010E, 0x010F, 0x0110, 0x0112, 0x011A, 0x011B, 0x0128, 0x0131, 0x0132, 0x013B, 0x0213, 0x8298}
EXIF_ONLY = {0x829A, 0x829D, 0x8822, 0x8827, 0x9000, 0x9003, 0x9004, 0x9201, 0x9202, 0x9204, 0x9207,
             0x9209, 0x920A, 0x927C, 0x9286, 0xA000, 0xA001, 0xA002, 0xA003, 0xA402, 0xA403, 0xA406, 0xA434}

# First EXIF version that defined a tag (x100): a tag newer than ExifVersion was injected by other software
TAG_INTRO = {
    0x9010: 231, 0x9011: 231, 0x9012: 231,
    0x8830: 230, 0x8831: 230, 0x8832: 230, 0x8833: 230, 0x8834: 230, 0x8835: 230,
    0xA430: 230, 0xA431: 230, 0xA432: 230, 0xA433: 230, 0xA434: 230, 0xA435: 230, 0xA500: 230,
    0xA460: 232, 0xA461: 232, 0xA462: 232,
    0x9400: 232, 0x9401: 232, 0x9402: 232, 0x9403: 232, 0x9404: 232, 0x9405: 232,
}
VALID_EXIF_VERSIONS = {200, 210, 220, 221, 230, 231, 232, 300}

# Tags cameras do not write: they come from photo managers / Windows Explorer / editors
SOFTWARE_ONLY_TAGS = {0x4746, 0x4749, 0x9C9B, 0x9C9C, 0x9C9D, 0x9C9E, 0x9C9F, 0x02BC, 0x83BB, 0x8649}

MAKERNOTE_SIGS = [
    (b"Nikon\x00", "nikon"), (b"SONY ", "sony"), (b"OLYMP", "olympus"), (b"Panasonic\x00", "panasonic"),
    (b"FUJIFILM", "fujifilm"), (b"PENTAX \x00", "pentax"), (b"AOC\x00", "pentax"), (b"Apple iOS\x00", "apple"),
    (b"LEICA", "leica"), (b"RICOH", "ricoh"), (b"Ricoh", "ricoh"), (b"SIGMA\x00", "sigma"),
    (b"FOVEON", "sigma"), (b"KDK", "kodak"),
]
BRAND_GROUPS = [{"pentax", "ricoh"}, {"panasonic", "leica"}, {"sony", "hasselblad"}]
MAKE_BYTE_ORDER = {"apple": ">", "canon": "<", "nikon": ">", "sony": "<", "fujifilm": "<",
                   "olympus": "<", "panasonic": "<", "pentax": ">"}

ENUM_RULES = (  # (ifd, tag name, allowed values)
    ("exif", "ExposureProgram", set(range(9))), ("exif", "MeteringMode", set(range(7)) | {255}),
    ("exif", "ColorSpace", {1, 0xFFFF}), ("exif", "WhiteBalance", {0, 1}), ("exif", "ExposureMode", {0, 1, 2}),
    ("exif", "SceneCaptureType", {0, 1, 2, 3, 4}), ("exif", "SensingMethod", set(range(1, 9))),
    ("ifd0", "ResolutionUnit", {1, 2, 3}), ("ifd0", "YCbCrPositioning", {1, 2}),
)


# --------------------------------------------------------------------------- #
# Data model
# --------------------------------------------------------------------------- #
@dataclass
class Finding:
    severity: str
    check: str
    detail: str
    fields: List[tuple] = field(default_factory=list)


@dataclass
class Result:
    path: str
    findings: List[Finding] = field(default_factory=list)
    metadata: Dict[str, Dict[str, str]] = field(default_factory=dict)
    structure: List[tuple] = field(default_factory=list)
    detected_type: str = "unknown"
    sha256: str = ""
    meta_sha256: str = ""
    score: int = 100
    verdict: str = ""
    ela: Optional[object] = None
    ela_stats: str = ""

    def add(self, severity, check, detail, fields=None):
        self.findings.append(Finding(severity, check, detail, list(fields or [])))

    def flagged(self):
        """{(category, field): (worst severity, [checks])} for every field named by a finding."""
        out = {}
        for f in self.findings:
            for key in f.fields:
                key = tuple(key)
                sev, checks = out.get(key, (f.severity, []))
                if SEVERITY_ORDER[f.severity] < SEVERITY_ORDER[sev]:
                    sev = f.severity
                if f.check not in checks:
                    checks.append(f.check)
                out[key] = (sev, checks)
        return out

    def rescore(self):
        penalty = sum(SEVERITY_WEIGHT[f.severity] for f in self.findings)
        self.score = max(0, 100 - penalty)
        if self.score >= 90:
            self.verdict = "Consistent"
        elif self.score >= 70:
            self.verdict = "Minor anomalies"
        elif self.score >= 45:
            self.verdict = "Suspicious"
        else:
            self.verdict = "Likely tampered / corrupted"

    def counts(self):
        c = {k: 0 for k in SEVERITY_ORDER}
        for f in self.findings:
            c[f.severity] += 1
        return c

    def to_dict(self):
        return {
            "path": self.path,
            "score": self.score,
            "verdict": self.verdict,
            "detected_type": self.detected_type,
            "sha256": self.sha256,
            "metadata_sha256": self.meta_sha256,
            "findings": [f.__dict__ for f in self.findings],
            "metadata": self.metadata,
            "structure": [list(r) for r in self.structure],
            "flagged_fields": [{"category": c, "field": fl, "severity": sv, "checks": ch}
                               for (c, fl), (sv, ch) in self.flagged().items()],
            "ela": self.ela_stats,
        }


# --------------------------------------------------------------------------- #
# Small helpers
# --------------------------------------------------------------------------- #
def fmt_size(n):
    size = float(n)
    for unit in ("B", "KB", "MB", "GB"):
        if size < 1024 or unit == "GB":
            return f"{int(size)} B" if unit == "B" else f"{size:.2f} {unit}"
        size /= 1024


def fmt_ts(ts):
    return datetime.fromtimestamp(ts).strftime("%Y-%m-%d %H:%M:%S")


def humanize(seconds):
    seconds = abs(int(seconds))
    for unit, span in (("day", 86400), ("hour", 3600), ("minute", 60)):
        if seconds >= span:
            v = seconds // span
            return f"{v} {unit}{'s' if v != 1 else ''}"
    return f"{seconds} s"


def clean(v):
    """Render any metadata value as a readable one-line string."""
    if isinstance(v, bytes):
        txt = v.decode("utf-8", "replace").replace("\x00", "")
        for prefix in ("ASCII", "UNICODE", "JIS"):
            if txt.startswith(prefix):
                txt = txt[len(prefix):]
                break
        if txt and len(v) < 2000 and sum(c.isprintable() for c in txt) / len(txt) > 0.9:
            return txt.strip()
        return f"<{len(v)} bytes> {v[:24].hex()}{'...' if len(v) > 24 else ''}"
    if isinstance(v, (bool, int)):
        return str(v)
    if hasattr(v, "numerator") and hasattr(v, "denominator"):
        try:
            return f"{float(v):.6g}"
        except Exception:
            return str(v)
    if isinstance(v, (tuple, list)):
        return ", ".join(clean(x) for x in list(v)[:32])
    if isinstance(v, dict):
        return json.dumps({str(k): clean(x) for k, x in v.items()})
    return str(v).replace("\x00", "").strip()


def to_degrees(dms):
    d, m, s = (float(x) for x in dms)
    return d + m / 60 + s / 3600


def parse_exif_dt(s):
    s = clean(s)
    for fmt in ("%Y:%m:%d %H:%M:%S", "%Y-%m-%d %H:%M:%S"):
        try:
            return datetime.strptime(s[:19], fmt)
        except ValueError:
            continue
    return None


def parse_iso(s):
    if not s:
        return None
    try:
        dt = datetime.fromisoformat(s.strip().replace("Z", "+00:00"))
        return dt.replace(tzinfo=None)
    except ValueError:
        return None


def sniff_type(head):
    if head.startswith(b"\xff\xd8\xff"):
        return "JPEG"
    if head.startswith(b"\x89PNG\r\n\x1a\n"):
        return "PNG"
    if head[:6] in (b"GIF87a", b"GIF89a"):
        return "GIF"
    if head[:2] == b"BM":
        return "BMP"
    if head[:4] == b"RIFF" and head[8:12] == b"WEBP":
        return "WEBP"
    if head[:4] in (b"II*\x00", b"MM\x00*"):
        return "TIFF"
    if head[4:8] == b"ftyp" and head[8:12] in (
        b"heic", b"heix", b"hevc", b"heim", b"heis", b"mif1", b"msf1", b"avif",
    ):
        return "HEIF"
    return "unknown"


def classify_trailing(res, tail, check, allow_jpeg=False):
    n = len(tail)
    head = tail[:16]
    if not tail.strip(b"\x00\r\n \xff"):
        res.add("LOW", check, f"{n} bytes of padding follow the end of the image data.")
        return
    kind, sev = "unidentified data", "MEDIUM"
    if head.startswith(b"\xff\xd8\xff"):
        kind, sev = "another embedded JPEG", ("INFO" if allow_jpeg else "MEDIUM")
    elif b"ftyp" in tail[:32]:
        kind, sev = "an embedded MP4/MOV video (e.g. Motion Photo)", "INFO"
    elif head.startswith(b"PK\x03\x04"):
        kind, sev = "a ZIP archive", "HIGH"
    elif head.startswith(b"Rar!"):
        kind, sev = "a RAR archive", "HIGH"
    elif head.startswith(b"7z\xbc\xaf"):
        kind, sev = "a 7-Zip archive", "HIGH"
    elif head.startswith(b"MZ"):
        kind, sev = "a Windows executable", "HIGH"
    elif head.startswith(b"\x7fELF"):
        kind, sev = "an ELF executable", "HIGH"
    elif head.startswith(b"%PDF"):
        kind, sev = "a PDF document", "HIGH"
    elif head.startswith(b"\x89PNG"):
        kind, sev = "an embedded PNG", "MEDIUM"
    else:
        sample = tail[:512]
        if sum(32 <= b < 127 or b in (9, 10, 13) for b in sample) / len(sample) > 0.9:
            kind = "plain text"
    if sev == "INFO":
        res.add(sev, check, f"{n:,} bytes of {kind} follow the image data (normal for this camera feature).")
    else:
        res.add(sev, check,
                f"{n:,} bytes of {kind} are appended after the end of the image. "
                "Possible hidden payload, steganography, or polyglot file.")


# --------------------------------------------------------------------------- #
# Container parsers
# --------------------------------------------------------------------------- #
def jpeg_name(m):
    if 0xE0 <= m <= 0xEF:
        return f"APP{m - 0xE0}"
    return {
        0xC0: "SOF0", 0xC1: "SOF1", 0xC2: "SOF2", 0xC3: "SOF3", 0xC4: "DHT",
        0xDA: "SOS", 0xDB: "DQT", 0xDD: "DRI", 0xFE: "COM", 0xDC: "DNL",
    }.get(m, f"0x{m:02X}")


def parse_jpeg(data, res):
    n = len(data)
    info = {"exif": None, "exif_count": 0, "xmp": [], "comments": [],
            "photoshop": False, "adobe": False, "mpf": False, "c2pa": False}
    res.structure.append(("SOI", 0, 2, ""))
    pos, eoi_end, flagged = 2, None, False

    while pos < n - 1:
        if data[pos] != 0xFF:
            res.add("MEDIUM", "JPEG structure",
                    f"Unexpected byte 0x{data[pos]:02X} between segments at offset {pos:,}.")
            flagged = True
            break
        marker = data[pos + 1]
        if marker == 0xFF:
            pos += 1
            continue
        if marker == 0xD9:
            res.structure.append(("EOI", pos, 2, ""))
            eoi_end = pos + 2
            break
        if marker == 0x01 or 0xD0 <= marker <= 0xD8:
            pos += 2
            continue
        if pos + 4 > n:
            res.add("HIGH", "JPEG structure", "File ends in the middle of a segment header (truncated).")
            flagged = True
            break
        seglen = struct.unpack(">H", data[pos + 2:pos + 4])[0]
        end = pos + 2 + seglen
        name = jpeg_name(marker)
        if end > n:
            res.structure.append((name, pos, seglen + 2, "TRUNCATED"))
            res.add("HIGH", "JPEG structure",
                    f"{name} segment at offset {pos:,} runs past the end of the file (truncated).")
            flagged = True
            break
        payload = data[pos + 4:end]
        note = ""
        if marker == 0xE1:
            if payload.startswith(b"Exif\x00\x00"):
                info["exif_count"] += 1
                note = "Exif"
                if info["exif"] is None:
                    info["exif"] = payload
            elif payload.startswith(b"http://ns.adobe.com/xap/1.0/\x00"):
                info["xmp"].append(payload[29:])
                note = "XMP"
            elif payload.startswith(b"http://ns.adobe.com/xmp/extension/"):
                note = "XMP extension"
        elif marker == 0xE0 and payload.startswith(b"JFIF"):
            note = "JFIF"
        elif marker == 0xE2:
            if payload.startswith(b"ICC_PROFILE"):
                note = "ICC profile"
            elif payload.startswith(b"MPF"):
                note, info["mpf"] = "Multi-Picture Format", True
        elif marker == 0xEB and (b"jumb" in payload[:16] or b"c2pa" in payload[:64]):
            note, info["c2pa"] = "C2PA / JUMBF", True
        elif marker == 0xED and payload.startswith(b"Photoshop 3.0"):
            note, info["photoshop"] = "Photoshop IRB", True
        elif marker == 0xEE and payload.startswith(b"Adobe"):
            note, info["adobe"] = "Adobe", True
        elif marker == 0xFE:
            text = payload.decode("utf-8", "replace").strip("\x00 \r\n")
            info["comments"].append(text)
            note = text[:40]
        res.structure.append((name, pos, seglen + 2, note))
        pos = end
        if marker == 0xDA:
            m = _SCAN_RE.search(data, pos)
            if not m:
                res.add("HIGH", "JPEG structure",
                        "No end-of-image (EOI) marker after the scan data. File is truncated or damaged.")
                flagged = True
                break
            pos = m.start()

    if eoi_end is None and not flagged:
        res.add("HIGH", "JPEG structure", "Missing end-of-image (EOI) marker. File is truncated or damaged.")
    if eoi_end is not None and eoi_end < n:
        classify_trailing(res, data[eoi_end:], "Appended data", allow_jpeg=info["mpf"])
    if info["exif_count"] > 1:
        res.add("MEDIUM", "Duplicate EXIF",
                f"{info['exif_count']} separate EXIF blocks found. Only the first is normally used; "
                "extra blocks can hide or replace metadata.")
    if info["photoshop"] or info["adobe"]:
        res.add("LOW", "Adobe blocks", "Photoshop/Adobe application segments present; "
                "the file was saved by an Adobe product.")
    if info["c2pa"]:
        res.add("INFO", "C2PA", "A C2PA / Content Credentials manifest is embedded. This tool does not "
                "validate its signature - use c2patool for that.")
    return info


def parse_png(data, res):
    n = len(data)
    pos, first, iend_end = 8, True, None
    out = {"text": {}, "xmp": None, "time": None, "c2pa": False, "exif": None}
    while pos + 12 <= n:
        length = struct.unpack(">I", data[pos:pos + 4])[0]
        ctype = data[pos + 4:pos + 8]
        name = ctype.decode("latin-1")
        cend = pos + 8 + length
        if cend + 4 > n:
            res.structure.append((name, pos, length + 12, "TRUNCATED"))
            res.add("HIGH", "PNG structure", f"Chunk {name} at offset {pos:,} is truncated.")
            break
        body = data[pos + 8:cend]
        crc = struct.unpack(">I", data[cend:cend + 4])[0]
        note = ""
        if zlib.crc32(ctype + body) & 0xFFFFFFFF != crc:
            note = "CRC MISMATCH"
            res.add("HIGH", "PNG CRC", f"Chunk {name} at offset {pos:,} fails its CRC-32 check - "
                    "the chunk was altered or corrupted.")
        if first and ctype != b"IHDR":
            res.add("HIGH", "PNG structure", f"First chunk is {name}, not IHDR.")
        first = False
        try:
            if ctype == b"tEXt":
                k, _, v = body.partition(b"\x00")
                out["text"][k.decode("latin-1")] = v.decode("latin-1")
            elif ctype == b"zTXt":
                k, _, rest = body.partition(b"\x00")
                txt = zlib.decompressobj().decompress(rest[1:], 1_000_000)
                out["text"][k.decode("latin-1")] = txt.decode("utf-8", "replace")
            elif ctype == b"iTXt":
                k, _, rest = body.partition(b"\x00")
                flag = rest[0]
                _lang, _tr, txt = rest[2:].split(b"\x00", 2)
                if flag:
                    txt = zlib.decompressobj().decompress(txt, 1_000_000)
                txt = txt.decode("utf-8", "replace")
                if k == b"XML:com.adobe.xmp":
                    out["xmp"] = txt
                else:
                    out["text"][k.decode("utf-8", "replace")] = txt
            elif ctype == b"eXIf":
                out["exif"] = body[6:] if body.startswith(b"Exif\x00\x00") else body
                note = "Exif"
            elif ctype == b"tIME" and len(body) == 7:
                y, mo, d, h, mi, s = struct.unpack(">HBBBBB", body)
                out["time"] = datetime(y, mo, d, h, mi, s)
            elif ctype == b"caBX":
                out["c2pa"] = True
                note = "C2PA"
        except Exception:
            note = note or "unparsed"
        res.structure.append((name, pos, length + 12, note))
        if ctype == b"IEND":
            iend_end = cend + 4
            break
        pos = cend + 4

    if iend_end is None:
        res.add("HIGH", "PNG structure", "Missing IEND chunk. File is truncated or damaged.")
    elif iend_end < n:
        classify_trailing(res, data[iend_end:], "Appended data")
    if out["time"] and out["time"] > datetime.now() + timedelta(days=1):
        res.add("MEDIUM", "PNG tIME", f"Modification time {out['time']} is in the future.")
    if out["c2pa"]:
        res.add("INFO", "C2PA", "A C2PA / Content Credentials manifest (caBX) is embedded; signature not validated here.")
    return out


def parse_webp(data, res):
    n = len(data)
    declared = struct.unpack("<I", data[4:8])[0] + 8
    xmp, exif = None, None
    if declared > n:
        res.add("HIGH", "WebP structure", f"RIFF header declares {declared:,} bytes but the file has {n:,} (truncated).")
    elif declared < n:
        classify_trailing(res, data[declared:], "Appended data")
    pos, limit = 12, min(n, declared)
    while pos + 8 <= limit:
        fourcc = data[pos:pos + 4].decode("latin-1")
        size = struct.unpack("<I", data[pos + 4:pos + 8])[0]
        res.structure.append((fourcc, pos, size + 8, ""))
        if pos + 8 + size > n:
            res.add("HIGH", "WebP structure", f"Chunk '{fourcc}' extends past the end of the file.")
            break
        if fourcc == "XMP ":
            xmp = data[pos + 8:pos + 8 + size].decode("utf-8", "replace")
        elif fourcc == "EXIF":
            blob = data[pos + 8:pos + 8 + size]
            exif = blob[6:] if blob.startswith(b"Exif\x00\x00") else blob
        pos += 8 + size + (size & 1)
    return xmp, exif


# --------------------------------------------------------------------------- #
# EXIF thumbnail, XMP, ELA
# --------------------------------------------------------------------------- #
def extract_exif_thumbnail(payload):
    """Return embedded thumbnail bytes from an APP1 Exif payload (IFD1), or None."""
    try:
        t = payload[6:]
        bo = "<" if t[:2] == b"II" else ">"
        ifd0 = struct.unpack(bo + "I", t[4:8])[0]
        cnt = struct.unpack(bo + "H", t[ifd0:ifd0 + 2])[0]
        nxt = struct.unpack(bo + "I", t[ifd0 + 2 + cnt * 12:ifd0 + 6 + cnt * 12])[0]
        if not nxt:
            return None
        cnt1 = struct.unpack(bo + "H", t[nxt:nxt + 2])[0]
        off = length = None
        for i in range(cnt1):
            tag, _typ, _count, val = struct.unpack(bo + "HHII", t[nxt + 2 + i * 12:nxt + 14 + i * 12])
            if tag == 0x0201:
                off = val
            elif tag == 0x0202:
                length = val
        if off is None or not length:
            return None
        return t[off:off + length]
    except Exception:
        return None


def xmp_field(xmp, name):
    m = re.search(rf'{re.escape(name)}="([^"]*)"', xmp)
    if m:
        return html.unescape(m.group(1))
    m = re.search(rf"<{re.escape(name)}[^>]*>\s*([^<]+?)\s*</{re.escape(name)}>", xmp)
    return html.unescape(m.group(1)) if m else None


def run_ela(img, quality=90):
    rgb = img.convert("RGB")
    w, h = rgb.size
    if w * h > 30_000_000:
        r = (30_000_000 / (w * h)) ** 0.5
        rgb = rgb.resize((max(1, int(w * r)), max(1, int(h * r))), _resample("LANCZOS"))
        w, h = rgb.size
    buf = io.BytesIO()
    rgb.save(buf, "JPEG", quality=quality)
    buf.seek(0)
    resaved = Image.open(buf).convert("RGB")
    diff = ImageChops.difference(rgb, resaved)
    mx = max(b[1] for b in diff.getextrema())
    scale = 255.0 / mx if mx else 1.0
    ela = diff.point(lambda p: min(255, int(p * scale)))
    gray = diff.convert("L")
    cw, ch = max(1, w // 16), max(1, h // 16)
    cells = list(gray.resize((cw, ch), _resample("BOX")).tobytes())
    return ela, {"max": mx, "cells": cells, "grid": (cw, ch), "size": (w, h)}


def largest_cluster(cells, cw, ch, thr):
    """Largest 8-connected group of blocks >= thr. Returns (size, fill_ratio, bbox, total_outliers)."""
    hot = {i for i, c in enumerate(cells) if c >= thr}
    best, seen = (0, 0.0, None), set()
    for start in hot:
        if start in seen:
            continue
        stack, comp = [start], []
        seen.add(start)
        while stack:
            i = stack.pop()
            comp.append(i)
            x, y = i % cw, i // cw
            for dx in (-1, 0, 1):
                for dy in (-1, 0, 1):
                    nx, ny = x + dx, y + dy
                    j = ny * cw + nx
                    if 0 <= nx < cw and 0 <= ny < ch and j in hot and j not in seen:
                        seen.add(j)
                        stack.append(j)
        if len(comp) > best[0]:
            xs, ys = [i % cw for i in comp], [i // cw for i in comp]
            bbox = (min(xs), min(ys), max(xs) + 1, max(ys) + 1)
            area = (bbox[2] - bbox[0]) * (bbox[3] - bbox[1])
            best = (len(comp), len(comp) / area, bbox)
    return best[0], best[1], best[2], len(hot)


# --------------------------------------------------------------------------- #
# EXIF forensics: raw TIFF structure + value-level consistency
# --------------------------------------------------------------------------- #
def tag_name(tag):
    return TAGS.get(tag, f"Tag 0x{tag:04X}")


def brand_of(text):
    low = (text or "").lower()
    return next((b for b in BRANDS if re.search(rf"\b{b}\b", low)), None)


def same_brand(a, b):
    return a == b or any(a in g and b in g for g in BRAND_GROUPS)


def preview(b, n=40):
    return "".join(chr(c) if 32 <= c < 127 else "." for c in b[:n])


def analyze_exif_structure(res, t):
    """Parse the raw TIFF block of the EXIF data and look for traces of editing."""
    n = len(t)
    if n < 8 or t[:2] not in (b"II", b"MM"):
        res.add("MEDIUM", "EXIF structure", "EXIF block has an invalid TIFF header (bad byte-order mark).")
        return
    bo = "<" if t[:2] == b"II" else ">"
    if struct.unpack(bo + "H", t[2:4])[0] != 42:
        res.add("MEDIUM", "EXIF structure", "EXIF block has an invalid TIFF magic number.")
        return

    spans = [(0, 8, "TIFF header")]
    ifds, seen = {}, set()
    queue = [("IFD0", struct.unpack(bo + "I", t[4:8])[0])]
    while queue:
        name, off = queue.pop(0)
        if not off or off in seen:
            continue
        seen.add(off)
        cat = IFD_CATEGORY.get(name, name)
        if off + 2 > n:
            res.add("HIGH", "EXIF structure", f"{name} offset {off:,} lies outside the EXIF block.")
            continue
        cnt = struct.unpack(bo + "H", t[off:off + 2])[0]
        end = off + 2 + cnt * 12 + 4
        if end > n:
            res.add("HIGH", "EXIF structure", f"{name} declares {cnt} entries but runs past the end of the EXIF block.")
            continue
        spans.append((off, end, f"{name} table"))
        entries = []
        for i in range(cnt):
            base = off + 2 + i * 12
            tag, typ, count, val = struct.unpack(bo + "HHII", t[base:base + 12])
            size = TYPE_SIZES.get(typ, 0) * count
            e = {"tag": tag, "typ": typ, "count": count, "val": val, "size": size, "off": None, "data": None}
            if typ not in TYPE_SIZES:
                res.add("MEDIUM", "EXIF structure", f"{tag_name(tag)} in {name} has an invalid data type ({typ}).",
                        fields=[(cat, tag_name(tag))])
            elif size <= 4:
                e["data"] = t[base + 8:base + 8 + size]
            elif val < 8 or val + size > n:
                res.add("HIGH", "EXIF structure",
                        f"The value of {tag_name(tag)} in {name} points outside the EXIF block "
                        f"(offset {val:,}, {size:,} bytes).", fields=[(cat, tag_name(tag))])
            else:
                e["off"], e["data"] = val, t[val:val + size]
                spans.append((val, val + size, f"{name}/{tag_name(tag)}"))
            entries.append(e)
        ifds[name] = entries
        nxt = struct.unpack(bo + "I", t[end - 4:end])[0]
        if name == "IFD0" and nxt:
            queue.append(("IFD1", nxt))
        if name != "IFD1":
            for e in entries:
                sub = {0x8769: "Exif", 0x8825: "GPS", 0xA005: "Interop"}.get(e["tag"])
                if sub:
                    queue.append((sub, e["val"]))
        else:
            e1 = {e["tag"]: e for e in entries}
            if 0x201 in e1 and 0x202 in e1 and e1[0x201]["val"] + e1[0x202]["val"] <= n:
                spans.append((e1[0x201]["val"], e1[0x201]["val"] + e1[0x202]["val"], "thumbnail"))

    ifd0 = {e["tag"]: e for e in ifds.get("IFD0", [])}
    exif = {e["tag"]: e for e in ifds.get("Exif", [])}
    make = ""
    if 0x010F in ifd0 and ifd0[0x010F]["data"]:
        make = ifd0[0x010F]["data"].split(b"\x00")[0].decode("latin-1").strip()
    make_brand = brand_of(make)

    # ---- per-IFD checks -----------------------------------------------------
    for name, entries in ifds.items():
        cat = IFD_CATEGORY.get(name, name)
        tags = [e["tag"] for e in entries]

        mx, out_of_order = -1, []
        for tg in tags:
            if tg in (0x8769, 0x8825, 0xA005):  # structural pointers, not metadata fields
                continue
            if tg < mx:
                out_of_order.append(tg)
            else:
                mx = tg
        if out_of_order:
            res.add("LOW", "EXIF tag order",
                    f"{name}: {len(out_of_order)} field(s) are out of order "
                    f"({', '.join(tag_name(x) for x in out_of_order[:6])}). The EXIF/TIFF specification requires "
                    "ascending tag order, so a tool probably inserted or rewrote these fields.",
                    fields=[(cat, tag_name(x)) for x in out_of_order])

        dups = sorted({tg for tg in tags if tags.count(tg) > 1})
        if dups:
            res.add("MEDIUM", "Duplicate EXIF tags",
                    f"{name} contains the same tag more than once ({', '.join(tag_name(x) for x in dups)}). "
                    "Readers use only one copy, so the other can hide the original value.",
                    fields=[(cat, tag_name(x)) for x in dups])

        if name in ("IFD0", "Exif"):
            bad_type, bad_count = [], []
            for e in entries:
                exp = EXPECTED_TYPES.get(e["tag"])
                if not exp or e["typ"] not in TYPE_SIZES:
                    continue
                types, need = exp
                if e["typ"] not in types:
                    bad_type.append((e["tag"], TYPE_NAMES[e["typ"]], "/".join(TYPE_NAMES[x] for x in sorted(types))))
                elif need and e["count"] != need:
                    bad_count.append((e["tag"], e["count"], need))
            if bad_type:
                res.add("MEDIUM", "EXIF data type",
                        f"{name}: " + "; ".join(f"{tag_name(a)} stored as {b}, expected {c}" for a, b, c in bad_type[:6])
                        + ". Cameras always use the specified type, so these fields were written by other software.",
                        fields=[(cat, tag_name(a)) for a, _, _ in bad_type])
            if bad_count:
                res.add("LOW", "EXIF data length",
                        f"{name}: " + "; ".join(f"{tag_name(a)} has {b} values, expected {c}" for a, b, c in bad_count[:6]) + ".",
                        fields=[(cat, tag_name(a)) for a, _, _ in bad_count])

            wrong = [tg for tg in tags if (name == "IFD0" and tg in EXIF_ONLY) or (name == "Exif" and tg in IFD0_ONLY)]
            if wrong:
                res.add("LOW", "EXIF placement",
                        f"{', '.join(tag_name(x) for x in wrong)} stored in the wrong IFD ({name}). Cameras place these "
                        "fields correctly, so a tool probably wrote them.",
                        fields=[(cat, tag_name(x)) for x in wrong])

        resid = []
        for e in entries:
            if e["typ"] == 2 and e["data"]:
                i = e["data"].find(b"\x00")
                tail = e["data"][i:].strip(b"\x00 ") if i != -1 else b""
                if tail:
                    resid.append((tag_name(e["tag"]), preview(tail, 24)))
        if resid:
            res.add("MEDIUM", "Overwritten text field",
                    f"{name}: text remains after the string terminator in "
                    + "; ".join(f"{a} ('{b}')" for a, b in resid[:5])
                    + ". The value was overwritten in place by a shorter string (typical of hex editing or naive EXIF editors).",
                    fields=[(cat, a) for a, _ in resid])

    # ---- fields that cameras do not write -------------------------------------
    sw_fields = [(C_IFD0, tag_name(tg)) for tg in SOFTWARE_ONLY_TAGS if tg in ifd0]
    if sw_fields:
        res.add("LOW", "Software-added fields",
                "Fields present that cameras do not write (ratings, Windows Explorer properties or embedded "
                "XMP/IPTC): " + ", ".join(f for _, f in sw_fields) + ". Added by a photo manager, Explorer or an editor.",
                fields=sw_fields)

    def txt(e, skip=0):
        return (e["data"] or b"")[skip:].replace(b"\x00", b"").strip()

    user_fields = []
    if 0x013B in ifd0 and txt(ifd0[0x013B]):
        user_fields.append((C_IFD0, tag_name(0x013B)))
    if 0x8298 in ifd0 and txt(ifd0[0x8298]):
        user_fields.append((C_IFD0, tag_name(0x8298)))
    if 0x9286 in exif and txt(exif[0x9286], 8):
        user_fields.append((C_EXIF, tag_name(0x9286)))
    if user_fields:
        res.add("INFO", "User-editable fields",
                "Free-text / ownership fields are present: " + ", ".join(f for _, f in user_fields)
                + ". They can be set in-camera but are also the fields most often added later. "
                "Compare with the original image or a baseline to know which.", fields=user_fields)

    # ---- EXIF version vs. tags present ------------------------------------------
    ver = None
    if 0x9000 in exif and exif[0x9000]["data"]:
        raw = exif[0x9000]["data"].decode("latin-1")
        if re.fullmatch(r"\d{4}", raw) and int(raw) in VALID_EXIF_VERSIONS:
            ver = int(raw)
        else:
            res.add("MEDIUM", "ExifVersion", f"ExifVersion '{preview(exif[0x9000]['data'])}' is not a valid EXIF version.",
                    fields=[(C_EXIF, tag_name(0x9000))])
    elif exif:
        res.add("LOW", "ExifVersion", "The mandatory ExifVersion tag is missing from the Exif IFD.")
    if ver:
        late = [(tg, intro) for tg, intro in TAG_INTRO.items() if tg in exif and intro > ver]
        if late:
            worst = max(i - ver for _, i in late)
            res.add("MEDIUM" if worst >= 10 else "LOW", "EXIF version mismatch",
                    f"ExifVersion is {ver / 100:.2f}, but the Exif IFD contains fields that were only defined later: "
                    + ", ".join(f"{tag_name(tg)} (EXIF {i / 100:.2f})" for tg, i in late[:6])
                    + ". The camera firmware could not have written them, so another tool added them.",
                    fields=[(C_EXIF, tag_name(tg)) for tg, _ in late])

    # ---- byte order vs. manufacturer --------------------------------------------
    want = MAKE_BYTE_ORDER.get(make_brand)
    if want and want != bo:
        res.add("MEDIUM", "EXIF byte order",
                f"{make} cameras write {'big' if want == '>' else 'little'}-endian EXIF but this block is "
                f"{'big' if bo == '>' else 'little'}-endian: it was rewritten by software.",
                fields=[(C_IFD0, "Make"), (C_IFD0, "Model")])

    # ---- MakerNote ---------------------------------------------------------------
    mn = exif.get(0x927C)
    mn_brand = None
    if mn and mn["data"]:
        mn_brand = next((b for sig, b in MAKERNOTE_SIGS if mn["data"].startswith(sig)), None)
        if mn_brand and make_brand and not same_brand(mn_brand, make_brand):
            res.add("HIGH", "MakerNote vs Make",
                    f"The MakerNote was written by a {mn_brand.title()} camera but the Make field says '{make}'. "
                    "Make/Model were edited, or the metadata was copied from another device.",
                    fields=[(C_IFD0, "Make"), (C_IFD0, "Model"), (C_EXIF, "MakerNote")])
        if make_brand == "canon" and mn["off"] is not None and len(mn["data"]) >= 14:
            mdata, cnt_mn = mn["data"], struct.unpack(bo + "H", mn["data"][:2])[0]
            if 1 <= cnt_mn <= 300 and 2 + cnt_mn * 12 <= len(mdata):
                bad = total = 0
                for i in range(cnt_mn):
                    _tg, ty, ct, vl = struct.unpack(bo + "HHII", mdata[2 + i * 12:14 + i * 12])
                    sz = TYPE_SIZES.get(ty, 0) * ct
                    if sz > 4:
                        total += 1
                        if not (mn["off"] <= vl and vl + sz <= mn["off"] + len(mdata)):
                            bad += 1
                if total >= 2 and bad / total >= 0.25:
                    res.add("MEDIUM", "MakerNote offsets",
                            f"{bad} of {total} Canon MakerNote entries point outside the MakerNote. The EXIF block was "
                            "rewritten by a tool that moved the MakerNote without fixing its internal offsets.",
                            fields=[(C_EXIF, "MakerNote")])

    # ---- overlaps and unreferenced ("slack") data ------------------------------
    spans.sort()
    cur_end, cur_label, overlaps = 0, "", []
    for s, e, label in spans:
        if s < cur_end and label != cur_label:
            overlaps.append((cur_label, label))
        if e > cur_end:
            cur_end, cur_label = e, label
    if overlaps:
        res.add("MEDIUM", "EXIF overlap",
                "Regions of the EXIF block overlap: " + "; ".join(f"{a} / {b}" for a, b in overlaps[:4])
                + ". Values should never share bytes; this is a sign of manual or tool-assisted editing.")

    merged = []
    for s, e, _ in spans:
        if merged and s <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], e)
        else:
            merged.append([s, e])
    gaps, pos = [], 0
    for s, e in merged:
        if s > pos:
            gaps.append((pos, s))
        pos = max(pos, e)
    if pos < n:
        gaps.append((pos, n))
    junk = [(a, b) for a, b in gaps if t[a:b].strip(b"\x00")]
    nz = sum(len(t[a:b].replace(b"\x00", b"")) for a, b in junk)
    if nz >= 8:
        a, b = max(junk, key=lambda g: g[1] - g[0])
        res.add("MEDIUM" if nz >= 32 else "LOW", "EXIF slack data",
                f"{nz} bytes inside the EXIF block are not referenced by any field (largest gap at offset {a:,}: "
                f"'{preview(t[a:b], 32)}'). This is left-over data from deleted or overwritten fields, or smuggled data.")

    # ---- summary shown in the Metadata tab -------------------------------------
    summary = {
        "Byte order": "little-endian (II)" if bo == "<" else "big-endian (MM)",
        "EXIF block size": f"{n:,} bytes",
        "IFDs": ", ".join(f"{k} ({len(v)} tags)" for k, v in ifds.items()),
    }
    if ver:
        summary["ExifVersion"] = f"{ver / 100:.2f}"
    if mn and mn["data"]:
        summary["MakerNote"] = f"{len(mn['data']):,} bytes" + (f", {mn_brand} signature" if mn_brand else ", no known signature")
    res.metadata["EXIF structure"] = summary


def _num(v):
    try:
        f = float(v[0] if isinstance(v, (tuple, list)) else v)
        return f if math.isfinite(f) else None
    except Exception:
        return None


def check_exif_values(res, ifd0, exif_ifd, gps):
    """Cross-field and value-level consistency checks on the parsed EXIF values."""
    et, sv = _num(exif_ifd.get("ExposureTime")), _num(exif_ifd.get("ShutterSpeedValue"))
    if et and et > 0 and sv is not None and abs(-math.log2(et) - sv) > 0.75:
        res.add("MEDIUM", "EXIF consistency",
                f"ExposureTime ({et:.6g} s) and ShutterSpeedValue ({sv:.2f} APEX) describe different shutter speeds.",
                fields=[(C_EXIF, "ExposureTime"), (C_EXIF, "ShutterSpeedValue")])
    fn, av = _num(exif_ifd.get("FNumber")), _num(exif_ifd.get("ApertureValue"))
    if fn and fn > 0 and av is not None and abs(2 * math.log2(fn) - av) > 0.75:
        res.add("MEDIUM", "EXIF consistency",
                f"FNumber (f/{fn:.3g}) and ApertureValue ({av:.2f} APEX) describe different apertures.",
                fields=[(C_EXIF, "FNumber"), (C_EXIF, "ApertureValue")])
    fl, f35 = _num(exif_ifd.get("FocalLength")), _num(exif_ifd.get("FocalLengthIn35mmFilm"))
    if fl and f35 and fl > 0 and f35 > 0 and not 0.5 <= f35 / fl <= 10:
        res.add("MEDIUM", "EXIF consistency",
                f"FocalLength {fl:.3g} mm vs 35mm-equivalent {f35:.3g} mm implies an impossible crop factor of {f35 / fl:.2f}.",
                fields=[(C_EXIF, "FocalLength"), (C_EXIF, "FocalLengthIn35mmFilm")])
    iso = _num(exif_ifd.get("ISOSpeedRatings", exif_ifd.get("PhotographicSensitivity")))
    if iso is not None and (iso < 3 or iso > 10_000_000):
        res.add("LOW", "EXIF consistency", f"ISO value {iso:g} is implausible.",
                fields=[(C_EXIF, k) for k in ("ISOSpeedRatings", "PhotographicSensitivity") if k in exif_ifd])

    # lens limits
    lens_text = clean(exif_ifd.get("LensModel", ""))
    lo = hi = fmin = None
    spec = exif_ifd.get("LensSpecification")
    if isinstance(spec, (tuple, list)) and len(spec) == 4:
        nums = [_num(x) for x in spec]
        if nums[0] and nums[1]:
            lo, hi = nums[0], nums[1]
            fs = [x for x in nums[2:] if x]
            fmin = min(fs) if fs else None
    if lo is None and lens_text:
        m = re.search(r"(\d+(?:\.\d+)?)(?:\s*-\s*(\d+(?:\.\d+)?))?\s*mm", lens_text)
        if m:
            lo, hi = float(m[1]), float(m[2] or m[1])
        m = re.search(r"f/\s?(\d+(?:\.\d+)?)", lens_text)
        if m:
            fmin = float(m[1])
    lens_fields = [(C_EXIF, k) for k in ("LensModel", "LensSpecification") if k in exif_ifd]
    if lo and fl and not (lo * 0.95 <= fl <= hi * 1.05 + 0.5):
        res.add("MEDIUM", "Lens consistency",
                f"FocalLength {fl:.3g} mm lies outside the range of the recorded lens ({lo:g}-{hi:g} mm).",
                fields=[(C_EXIF, "FocalLength")] + lens_fields)
    if fmin and fn and fn < fmin * 0.9:
        res.add("MEDIUM", "Lens consistency",
                f"FNumber f/{fn:.3g} is wider than the recorded lens can open (f/{fmin:g}).",
                fields=[(C_EXIF, "FNumber")] + lens_fields)

    # enumerated values
    bad = []
    for which, name, allowed in ENUM_RULES:
        src = exif_ifd if which == "exif" else ifd0
        if name in src:
            try:
                if int(src[name]) not in allowed:
                    bad.append((C_EXIF if which == "exif" else C_IFD0, name, src[name]))
            except (ValueError, TypeError):
                bad.append((C_EXIF if which == "exif" else C_IFD0, name, src[name]))
    if bad:
        res.add("MEDIUM", "Invalid EXIF value",
                "Values outside the range defined by the EXIF standard: "
                + "; ".join(f"{n} = {clean(v)}" for _, n, v in bad[:6]) + ".",
                fields=[(c, n) for c, n, _ in bad])

    # string formats
    bad_fmt = []
    for k in ("OffsetTime", "OffsetTimeOriginal", "OffsetTimeDigitized"):
        if k in exif_ifd and not re.fullmatch(r"[+-]\d\d:\d\d", clean(exif_ifd[k])):
            bad_fmt.append((k, clean(exif_ifd[k])))
    for k, v in exif_ifd.items():
        if k.lower().startswith("subsectime") and not clean(v).strip().isdigit():
            bad_fmt.append((k, clean(v)))
    if bad_fmt:
        res.add("MEDIUM", "Invalid EXIF value",
                "Malformed time fields: " + "; ".join(f"{k} = '{v}'" for k, v in bad_fmt) + ".",
                fields=[(C_EXIF, k) for k, _ in bad_fmt])
    for k in ("XResolution", "YResolution"):
        v = _num(ifd0.get(k))
        if v is not None and v <= 0:
            res.add("LOW", "Invalid EXIF value", f"{k} is {v:g}, which is not a valid resolution.", fields=[(C_IFD0, k)])

    # GPS value sanity
    for k in ("GPSLatitude", "GPSLongitude"):
        try:
            d, m, s = (float(x) for x in gps[k])
            if m >= 60 or s >= 60 or d < 0 or m < 0 or s < 0:
                res.add("MEDIUM", "GPS", f"{k} has invalid degrees/minutes/seconds ({d:g}, {m:g}, {s:g}).",
                        fields=[(C_GPS, k)])
        except (KeyError, ValueError, TypeError):
            pass
    try:
        hh, mm, ss = (float(x) for x in gps["GPSTimeStamp"])
        if hh >= 24 or mm >= 60 or ss >= 60:
            res.add("MEDIUM", "GPS", f"GPSTimeStamp {hh:g}:{mm:g}:{ss:g} is not a valid time.", fields=[(C_GPS, "GPSTimeStamp")])
    except (KeyError, ValueError, TypeError):
        pass
    alt = _num(gps.get("GPSAltitude"))
    if alt is not None and (alt > 9000 or alt < -500):
        res.add("LOW", "GPS", f"GPSAltitude {alt:g} m is implausible.", fields=[(C_GPS, "GPSAltitude")])


# --------------------------------------------------------------------------- #
# Main analysis
# --------------------------------------------------------------------------- #
def analyze_file(path, run_ela_flag=True, ela_quality=90):
    res = Result(path)
    try:
        with open(path, "rb") as f:
            data = f.read()
        st = os.stat(path)
    except OSError as e:
        res.add("HIGH", "File access", str(e))
        res.rescore()
        return res

    res.sha256 = hashlib.sha256(data).hexdigest()
    dtype = sniff_type(data[:32])
    res.detected_type = dtype
    ext = os.path.splitext(path)[1].lower()
    expected = EXT_TYPES.get(ext)

    res.metadata["File"] = {
        "Name": os.path.basename(path),
        "Path": os.path.abspath(path),
        "Size": f"{fmt_size(len(data))} ({len(data):,} bytes)",
        "Detected type": dtype,
        "Filesystem modified": fmt_ts(st.st_mtime),
        "Filesystem created/changed": fmt_ts(st.st_ctime),
        "MD5": hashlib.md5(data).hexdigest(),
        "SHA-256": res.sha256,
    }

    # ---- signature / extension ------------------------------------------------
    if not data:
        res.add("HIGH", "File signature", "File is empty.")
    elif dtype == "unknown":
        res.add("HIGH", "File signature", "Content does not match any recognised image format.")
    elif expected and expected != dtype:
        res.add("HIGH", "Extension mismatch",
                f"Extension '{ext}' implies {expected} but the content is {dtype} (renamed / disguised file).")
    elif not expected:
        res.add("LOW", "Extension", f"Unrecognised image extension '{ext or '(none)'}'.")

    # ---- container structure -------------------------------------------------
    jpeg_info, png_info, xmp_text, webp_exif = {}, {}, "", None
    try:
        if dtype == "JPEG":
            jpeg_info = parse_jpeg(data, res)
            xmp_text = b"".join(jpeg_info["xmp"]).decode("utf-8", "replace")
        elif dtype == "PNG":
            png_info = parse_png(data, res)
            xmp_text = png_info.get("xmp") or ""
        elif dtype == "WEBP":
            xmp_text, webp_exif = parse_webp(data, res)
            xmp_text = xmp_text or ""
        elif dtype == "BMP" and len(data) >= 6:
            declared = struct.unpack("<I", data[2:6])[0]
            if declared < len(data):
                res.add("MEDIUM", "BMP structure", f"Header declares {declared:,} bytes but file is {len(data):,}.")
            elif declared > len(data):
                res.add("HIGH", "BMP structure", f"Header declares {declared:,} bytes but file is {len(data):,} (truncated).")
        elif dtype == "GIF" and data[-1:] != b"\x3b":
            res.add("MEDIUM", "GIF structure", "Missing GIF trailer byte (0x3B): truncated or has appended data.")
    except Exception as e:
        res.add("MEDIUM", "Structure parser", f"Parser error: {type(e).__name__}: {e}")

    # ---- decode test --------------------------------------------------------------
    img, loaded, flagged = None, False, False
    if dtype != "unknown" and data:
        try:
            Image.open(io.BytesIO(data)).verify()
        except Exception as e:
            flagged = True
            res.add("INFO" if dtype == "HEIF" else "HIGH", "Image decode",
                    f"Verification failed: {type(e).__name__}: {e}")
        try:
            img = Image.open(io.BytesIO(data))
        except Exception as e:
            if not flagged:
                res.add("INFO" if dtype == "HEIF" else "HIGH", "Image decode", f"Cannot open image: {e}")
        if img is not None:
            try:
                img.load()
                loaded = True
            except Exception as e:
                if not flagged:
                    res.add("HIGH", "Pixel data", f"Pixel data cannot be fully decoded: {e}")

    ifd0, exif_ifd, gps = {}, {}, {}
    if img is not None:
        w, h = img.size
        info = {
            "Format": img.format or dtype,
            "Dimensions": f"{w} x {h} px ({w * h / 1e6:.2f} MP)",
            "Mode": img.mode,
        }
        if dtype == "JPEG":
            q = getattr(img, "quantization", None)
            if q and 0 in q:
                scale = sum(q[0]) * 100.0 / STD_LUMA_SUM
                quality = (200 - scale) / 2 if scale <= 100 else 5000 / scale
                info["Estimated JPEG quality"] = f"~{max(1, min(100, round(quality)))}"
            info["Progressive"] = str(bool(img.info.get("progressive") or img.info.get("progression")))
        if img.info.get("dpi"):
            info["DPI"] = clean(img.info["dpi"])
        info["ICC profile"] = "yes" if img.info.get("icc_profile") else "no"
        res.metadata["Image"] = info

        try:
            ex = img.getexif()
            ifd0 = {TAGS.get(k, f"Tag 0x{k:04X}"): v for k, v in ex.items()
                    if k not in (0x8769, 0x8825, 0xA005)}
            try:
                exif_ifd = {TAGS.get(k, f"Tag 0x{k:04X}"): v for k, v in ex.get_ifd(0x8769).items()}
            except Exception:
                pass
            try:
                gps = {GPSTAGS.get(k, f"Tag 0x{k:04X}"): v for k, v in ex.get_ifd(0x8825).items()}
            except Exception:
                pass
        except Exception as e:
            res.add("MEDIUM", "EXIF parse", f"EXIF block could not be parsed: {type(e).__name__}: {e}")

    if ifd0:
        res.metadata["EXIF (IFD0)"] = {k: clean(v) for k, v in ifd0.items()}
    if exif_ifd:
        res.metadata["EXIF (Exif)"] = {k: clean(v) for k, v in exif_ifd.items()}
    if gps:
        res.metadata["GPS"] = {k: clean(v) for k, v in gps.items()}
    if jpeg_info.get("comments"):
        res.metadata["JPEG comments"] = {f"COM #{i + 1}": c for i, c in enumerate(jpeg_info["comments"])}
    if png_info.get("text"):
        res.metadata["PNG text"] = dict(png_info["text"])
    if png_info.get("time"):
        res.metadata.setdefault("PNG text", {})["tIME (last modified)"] = str(png_info["time"])

    seen_editors = set()

    def check_editor(label, text, fields=None):
        low = (text or "").lower()
        for e in EDITORS:
            if e in low and e not in seen_editors:
                seen_editors.add(e)
                res.add("MEDIUM", "Editing software", f"{label} indicates post-processing: '{text.strip()[:80]}'.",
                        fields=fields)
                return

    # ---- EXIF logic --------------------------------------------------------------
    if img is not None and dtype in ("JPEG", "WEBP", "TIFF", "PNG", "HEIF") and not ifd0 and not exif_ifd:
        res.add("INFO", "EXIF presence", "No EXIF metadata. It was either stripped (social media, messengers, "
                "editors, privacy tools) or never existed (screenshots, renders).")
    if ifd0 or exif_ifd:
        _check_exif(res, img, st, ifd0, exif_ifd, gps, check_editor)
    if gps:
        _check_gps(res, gps, exif_ifd, parse_exif_dt(exif_ifd["DateTimeOriginal"])
                   if "DateTimeOriginal" in exif_ifd else None)
    if jpeg_info.get("exif") and img is not None:
        _check_thumbnail(res, img, jpeg_info["exif"])
    raw_tiff = None
    if jpeg_info.get("exif"):
        raw_tiff = jpeg_info["exif"][6:]
    elif png_info.get("exif"):
        raw_tiff = png_info["exif"]
    elif webp_exif:
        raw_tiff = webp_exif
    if raw_tiff:
        try:
            analyze_exif_structure(res, raw_tiff)
        except Exception as e:
            res.add("INFO", "EXIF structure", f"Raw EXIF analysis failed: {type(e).__name__}: {e}")
    if ifd0 or exif_ifd or gps:
        try:
            check_exif_values(res, ifd0, exif_ifd, gps)
        except Exception as e:
            res.add("INFO", "EXIF consistency", f"Value checks failed: {type(e).__name__}: {e}")
    for i, c in enumerate(jpeg_info.get("comments", [])):
        check_editor("JPEG comment", c, [("JPEG comments", f"COM #{i + 1}")])
    for k, v in png_info.get("text", {}).items():
        if k.lower() in ("software", "comment", "description", "parameters", "source"):
            check_editor(f"PNG text '{k}'", v, [("PNG text", k)])
    for k in png_info.get("text", {}):
        if k.lower() == "parameters":
            res.add("MEDIUM", "AI generation", "PNG 'parameters' text chunk is typical of Stable Diffusion front-ends.",
                    fields=[("PNG text", k)])
    if xmp_text:
        _check_xmp(res, xmp_text, exif_ifd, check_editor)

    # ---- ELA --------------------------------------------------------------------
    if run_ela_flag and dtype == "JPEG" and loaded:
        try:
            ela, stats = run_ela(img, ela_quality)
            cells = stats["cells"]
            if len(cells) >= 64:
                mean, sd = statistics.fmean(cells), statistics.pstdev(cells)
                thr = max(mean + 3 * sd, mean * 2.5, 2.0)
                cw, ch = stats["grid"]
                size, fill, bbox, total = largest_cluster(cells, cw, ch, thr)
                res.ela_stats = (f"ELA @ Q{ela_quality}: max diff {stats['max']}, mean block {mean:.2f}, "
                                 f"std {sd:.2f}, high-error blocks {total}/{len(cells)}, "
                                 f"largest cluster {size} blocks (fill {fill:.0%})")
                if size >= 8 and fill >= 0.5 and size >= 0.5 * total:
                    sx, sy = stats["size"][0] / cw, stats["size"][1] / ch
                    res.add("LOW", "ELA cluster",
                            f"A compact cluster of {size} high-error 16x16 blocks (about x {int(bbox[0] * sx)}-{int(bbox[2] * sx)}, "
                            f"y {int(bbox[1] * sy)}-{int(bbox[3] * sy)}) has a different compression history from the rest "
                            "of the image. This can indicate a pasted, retouched or re-compressed region. Inspect the ELA tab; "
                            "flat colour areas and logos can also cause this.")
            ela.thumbnail((2000, 2000))
            res.ela = ela
        except Exception as e:
            res.add("INFO", "ELA", f"ELA could not be computed: {e}")

    # ---- metadata fingerprint --------------------------------------------------
    fp = {k: v for k, v in res.metadata.items() if k not in ("File", "Image", "EXIF structure")}
    if xmp_text:
        fp["_xmp"] = xmp_text
    res.meta_sha256 = hashlib.sha256(json.dumps(fp, sort_keys=True).encode()).hexdigest()
    if xmp_text:
        res.metadata["XMP (key fields)"] = {
            k: v for k, v in (
                (n, xmp_field(xmp_text, n)) for n in (
                    "xmp:CreatorTool", "xmp:CreateDate", "xmp:ModifyDate", "xmp:MetadataDate",
                    "xmpMM:DocumentID", "xmpMM:OriginalDocumentID", "xmpMM:InstanceID",
                    "dc:format", "photoshop:DateCreated")
            ) if v
        }

    res.rescore()
    return res


def _check_exif(res, img, st, ifd0, exif_ifd, gps, check_editor):
    F = {"DateTimeOriginal": (C_EXIF, "DateTimeOriginal"), "DateTimeDigitized": (C_EXIF, "DateTimeDigitized"),
         "DateTime (modify)": (C_IFD0, "DateTime")}
    # --- dates
    dts = {}
    for label, raw in (("DateTimeOriginal", exif_ifd.get("DateTimeOriginal")),
                       ("DateTimeDigitized", exif_ifd.get("DateTimeDigitized")),
                       ("DateTime (modify)", ifd0.get("DateTime"))):
        if raw is None:
            continue
        dt = parse_exif_dt(raw)
        if dt is None:
            res.add("MEDIUM", "EXIF dates", f"{label} is invalid or a placeholder: '{clean(raw)}'.", fields=[F[label]])
        else:
            dts[label] = dt
    now = datetime.now()
    for label, dt in dts.items():
        if dt > now + timedelta(days=1):
            res.add("MEDIUM", "EXIF dates", f"{label} ({dt}) is in the future.", fields=[F[label]])
        elif dt.year < 1995:
            res.add("MEDIUM", "EXIF dates", f"{label} ({dt}) predates consumer digital photography.", fields=[F[label]])
    o, d, m = dts.get("DateTimeOriginal"), dts.get("DateTimeDigitized"), dts.get("DateTime (modify)")
    if o and m:
        delta = (m - o).total_seconds()
        if delta < -1:
            res.add("MEDIUM", "EXIF dates",
                    f"Modify date is {humanize(delta)} EARLIER than the capture date - impossible for an untouched file.",
                    fields=[F["DateTime (modify)"], F["DateTimeOriginal"]])
        elif delta > 60:
            res.add("LOW", "EXIF dates", f"File was modified {humanize(delta)} after it was captured (re-saved/edited).",
                    fields=[F["DateTime (modify)"]])
    if o and d and abs((d - o).total_seconds()) > 2:
        res.add("LOW", "EXIF dates",
                f"DateTimeDigitized differs from DateTimeOriginal by {humanize((d - o).total_seconds())}.",
                fields=[F["DateTimeDigitized"], F["DateTimeOriginal"]])
    if o:
        fm = datetime.fromtimestamp(st.st_mtime)
        if fm < o - timedelta(days=1):
            res.add("MEDIUM", "Filesystem vs EXIF",
                    f"File's modified time ({fm:%Y-%m-%d %H:%M}) is {humanize((o - fm).total_seconds())} "
                    "before the EXIF capture time: clock or timestamp manipulation.", fields=[F["DateTimeOriginal"]])

    # --- dimensions
    try:
        ew, eh = int(exif_ifd["ExifImageWidth"]), int(exif_ifd["ExifImageHeight"])
        w, h = img.size
        if (ew, eh) not in ((w, h), (h, w)):
            res.add("MEDIUM", "Dimensions",
                    f"EXIF says {ew}x{eh} but the image is {w}x{h}: resized/cropped after capture, "
                    "or metadata copied from another image.",
                    fields=[(C_EXIF, "ExifImageWidth"), (C_EXIF, "ExifImageHeight")])
        elif (ew, eh) != (w, h):
            res.add("INFO", "Dimensions", "EXIF width/height are swapped relative to pixel data (rotation).")
    except (KeyError, ValueError, TypeError, AttributeError):
        pass

    # --- software
    sw = clean(ifd0.get("Software", ""))
    if sw:
        check_editor("EXIF Software tag", sw, [(C_IFD0, "Software")])

    # --- make / model
    make, model = clean(ifd0.get("Make", "")), clean(ifd0.get("Model", ""))
    mm_fields = [(C_IFD0, k) for k, v in (("Make", make), ("Model", model)) if v]
    cam_tags = [k for k in ("ExposureTime", "FNumber", "ISOSpeedRatings", "PhotographicSensitivity",
                            "LensModel", "FocalLength") if k in exif_ifd]
    if cam_tags and not make and not model:
        res.add("MEDIUM", "Camera tags", "Exposure/lens tags exist but Make and Model are missing "
                "(partially stripped or fabricated metadata).", fields=[(C_EXIF, k) for k in cam_tags])
    elif make and not cam_tags:
        res.add("LOW", "Camera tags", "Make/Model present but there is no exposure data (ISO, aperture, shutter).",
                fields=mm_fields)
    mk = brand_of(make)
    model_brands = {b for b in BRANDS if re.search(rf"\b{b}\b", model.lower())}
    if mk and model_brands and not any(same_brand(mk, b) for b in model_brands):
        res.add("MEDIUM", "Make/Model", f"Make '{make}' conflicts with Model '{model}'.", fields=mm_fields)

    ori = ifd0.get("Orientation")
    if ori is not None:
        try:
            if int(ori) not in range(1, 9):
                res.add("MEDIUM", "Orientation", f"Invalid Orientation value {ori}.", fields=[(C_IFD0, "Orientation")])
        except (ValueError, TypeError):
            res.add("MEDIUM", "Orientation", f"Non-numeric Orientation value '{clean(ori)}'.",
                    fields=[(C_IFD0, "Orientation")])


def _check_gps(res, gps, exif_ifd, orig_dt):
    lat = lon = None
    ll_fields = [(C_GPS, k) for k in ("GPSLatitude", "GPSLatitudeRef", "GPSLongitude", "GPSLongitudeRef") if k in gps]
    try:
        if "GPSLatitude" in gps and "GPSLongitude" in gps:
            lat, lon = to_degrees(gps["GPSLatitude"]), to_degrees(gps["GPSLongitude"])
            latref, lonref = clean(gps.get("GPSLatitudeRef", "")), clean(gps.get("GPSLongitudeRef", ""))
            if latref not in ("N", "S") or lonref not in ("E", "W"):
                res.add("MEDIUM", "GPS", f"Invalid hemisphere reference ('{latref}', '{lonref}').", fields=ll_fields)
            if latref == "S":
                lat = -lat
            if lonref == "W":
                lon = -lon
    except Exception:
        res.add("MEDIUM", "GPS", "Malformed GPS coordinate values.", fields=ll_fields)
    if lat is not None:
        res.metadata["GPS"]["Decimal coordinates"] = f"{lat:.6f}, {lon:.6f}"
        res.metadata["GPS"]["Map link"] = f"https://www.google.com/maps?q={lat:.6f},{lon:.6f}"
        if abs(lat) > 90 or abs(lon) > 180:
            res.add("HIGH", "GPS", f"Coordinates ({lat:.4f}, {lon:.4f}) are outside the valid range.", fields=ll_fields)
        elif lat == 0 and lon == 0:
            res.add("LOW", "GPS", "Coordinates are exactly 0,0 ('Null Island'): usually a failed fix or placeholder.",
                    fields=ll_fields)
    t_fields = [(C_GPS, "GPSTimeStamp"), (C_GPS, "GPSDateStamp"), (C_EXIF, "DateTimeOriginal")]
    try:
        if orig_dt and "GPSDateStamp" in gps and "GPSTimeStamp" in gps:
            gd = datetime.strptime(clean(gps["GPSDateStamp"])[:10], "%Y:%m:%d")
            hh, mm, ss = (float(x) for x in gps["GPSTimeStamp"])
            gps_utc = gd + timedelta(hours=hh, minutes=mm, seconds=ss)
            off = re.match(r"([+-])(\d\d):(\d\d)", clean(exif_ifd.get("OffsetTimeOriginal", "")))
            if off:
                delta = timedelta(hours=int(off[2]), minutes=int(off[3]))
                local = orig_dt - delta if off[1] == "+" else orig_dt + delta
                diff = abs((gps_utc - local).total_seconds())
                if diff > 3600:
                    res.add("LOW", "GPS time",
                            f"GPS UTC time differs from the capture time (converted with the stored offset) by {humanize(diff)}.",
                            fields=t_fields)
            else:
                diff = abs((gps_utc - orig_dt).total_seconds())
                if diff > 15 * 3600:
                    res.add("MEDIUM", "GPS time",
                            f"GPS timestamp differs from capture time by {humanize(diff)}, more than any time-zone offset allows.",
                            fields=t_fields)
    except Exception:
        pass


def _check_thumbnail(res, img, exif_payload):
    raw = extract_exif_thumbnail(exif_payload)
    if not raw:
        return
    try:
        th = Image.open(io.BytesIO(raw))
        th.load()
    except Exception:
        res.add("LOW", "EXIF thumbnail", "An EXIF thumbnail is present but cannot be decoded.")
        return
    w, h = img.size
    tw, thh = th.size
    res.metadata.setdefault("Image", {})["EXIF thumbnail"] = f"{tw} x {thh} px"
    ar_main, ar_th = w / h, tw / thh
    if abs(ar_main - 1 / ar_th) < 0.03 and abs(ar_main - ar_th) >= 0.03:
        return  # rotated thumbnail: skip pixel comparison
    if abs(ar_main - ar_th) / ar_main > 0.03:
        res.add("MEDIUM", "EXIF thumbnail",
                f"Thumbnail aspect ratio ({ar_th:.3f}) differs from the main image ({ar_main:.3f}): "
                "the image was cropped/edited without the thumbnail being regenerated.")
        return
    try:
        main_small = img.convert("RGB").resize(th.size, _resample("LANCZOS"))
        diff = ImageChops.difference(main_small, th.convert("RGB"))
        mean = sum(ImageStat.Stat(diff).mean) / 3
        res.metadata["Image"]["Thumbnail difference"] = f"{mean:.1f} / 255"
        if mean > 30:
            res.add("MEDIUM", "EXIF thumbnail",
                    f"Embedded thumbnail looks very different from the main image (mean diff {mean:.1f}/255): "
                    "the picture was probably replaced or heavily edited after capture.")
        elif mean > 18:
            res.add("LOW", "EXIF thumbnail", f"Embedded thumbnail differs noticeably from the main image (mean diff {mean:.1f}/255).")
    except Exception:
        pass


def _check_xmp(res, xmp, exif_ifd, check_editor):
    agents = [a or b for a, b in re.findall(r'stEvt:softwareAgent="([^"]*)"|<stEvt:softwareAgent>([^<]*)<', xmp)]
    actions = [a or b for a, b in re.findall(r'stEvt:action="([^"]*)"|<stEvt:action>([^<]*)<', xmp)]
    if agents or actions:
        res.add("LOW", "XMP history",
                f"XMP edit history present: actions [{', '.join(dict.fromkeys(actions))}] "
                f"by [{', '.join(dict.fromkeys(agents))}].")
    tool = xmp_field(xmp, "xmp:CreatorTool")
    if tool:
        check_editor("XMP CreatorTool", tool, [(C_XMP, "xmp:CreatorTool")])
    for a in dict.fromkeys(agents):
        check_editor("XMP history agent", a)
    created, modified = parse_iso(xmp_field(xmp, "xmp:CreateDate")), parse_iso(xmp_field(xmp, "xmp:ModifyDate"))
    if created and modified and modified < created - timedelta(seconds=1):
        res.add("MEDIUM", "XMP dates", f"xmp:ModifyDate ({modified}) is earlier than xmp:CreateDate ({created}).",
                fields=[(C_XMP, "xmp:ModifyDate"), (C_XMP, "xmp:CreateDate")])
    doc, orig = xmp_field(xmp, "xmpMM:DocumentID"), xmp_field(xmp, "xmpMM:OriginalDocumentID")
    if doc and orig and doc != orig:
        res.add("LOW", "XMP IDs", "DocumentID differs from OriginalDocumentID: this file is derived from another document.",
                fields=[(C_XMP, "xmpMM:DocumentID"), (C_XMP, "xmpMM:OriginalDocumentID")])
    exif_o = parse_exif_dt(exif_ifd["DateTimeOriginal"]) if "DateTimeOriginal" in exif_ifd else None
    if created and exif_o and abs((created - exif_o).total_seconds()) > 120:
        res.add("LOW", "XMP vs EXIF",
                f"xmp:CreateDate and EXIF DateTimeOriginal disagree by {humanize((created - exif_o).total_seconds())}.",
                fields=[(C_XMP, "xmp:CreateDate"), (C_EXIF, "DateTimeOriginal")])


# --------------------------------------------------------------------------- #
# Field-level diff, baseline manifest and comparison
# --------------------------------------------------------------------------- #
def snapshot_fields(res):
    """Tracked metadata fields of a result, as {category: {field: value}}."""
    return {cat: {k: v for k, v in res.metadata[cat].items() if k not in DERIVED_FIELDS}
            for cat in TRACKED_CATEGORIES if cat in res.metadata}


def diff_fields(old, new):
    """Rows of (change, category, field, old_value, new_value)."""
    rows = []
    for cat in TRACKED_CATEGORIES:
        o, n = old.get(cat, {}), new.get(cat, {})
        for k in sorted(set(o) | set(n)):
            if k not in o:
                rows.append(("ADDED", cat, k, "", n[k]))
            elif k not in n:
                rows.append(("REMOVED", cat, k, o[k], ""))
            elif o[k] != n[k]:
                rows.append(("CHANGED", cat, k, o[k], n[k]))
    return rows


def _trunc(s, n=50):
    s = str(s)
    return s if len(s) <= n else s[:n - 3] + "..."


def add_diff_findings(res, check, rows, source, report_empty=False):
    """Turn diff rows into findings (added/changed = HIGH, removed = MEDIUM) that flag the fields."""
    groups = {"ADDED": [], "CHANGED": [], "REMOVED": []}
    for r in rows:
        groups[r[0]].append(r)
    spec = {"ADDED": ("HIGH", "added since"), "CHANGED": ("HIGH", "changed since"), "REMOVED": ("MEDIUM", "removed since")}
    for kind, items in groups.items():
        if not items:
            continue
        sev, verb = spec[kind]
        shown = []
        for _, _cat, fld, old, new in items[:10]:
            if kind == "ADDED":
                shown.append(f"{fld} = '{_trunc(new)}'")
            elif kind == "REMOVED":
                shown.append(f"{fld} (was '{_trunc(old)}')")
            else:
                shown.append(f"{fld}: '{_trunc(old)}' -> '{_trunc(new)}'")
        more = f" (+{len(items) - 10} more)" if len(items) > 10 else ""
        res.add(sev, f"{check}: {kind.lower()} fields",
                f"{len(items)} metadata field(s) {verb} {source}: " + "; ".join(shown) + more + ".",
                fields=[] if kind == "REMOVED" else [(c, f) for _, c, f, _, _ in items])
    if report_empty and not rows:
        res.add("INFO", check, f"All tracked metadata fields are identical to {source}.")


def build_manifest(results):
    return {
        "version": 2,
        "created": datetime.now().isoformat(timespec="seconds"),
        "files": {
            os.path.abspath(p): {
                "name": os.path.basename(p), "sha256": r.sha256, "metadata_sha256": r.meta_sha256,
                "size": os.path.getsize(p) if os.path.exists(p) else None,
                "fields": snapshot_fields(r),
            } for p, r in results.items()
        },
    }


def verify_against_manifest(res, manifest):
    res.findings = [f for f in res.findings if not f.check.startswith("Baseline")]
    files = manifest.get("files", {})
    entry = files.get(os.path.abspath(res.path)) or next(
        (v for v in files.values() if v.get("name") == os.path.basename(res.path)), None)
    if not entry:
        res.add("INFO", "Baseline", "File is not listed in the baseline manifest.")
    elif entry["sha256"] == res.sha256:
        res.add("INFO", "Baseline", "File is byte-identical to the baseline (SHA-256 match).")
    else:
        if entry["metadata_sha256"] == res.meta_sha256:
            res.add("HIGH", "Baseline", "File content changed since the baseline, but the metadata is unchanged: "
                    "pixel data was altered or the file was re-encoded.")
        else:
            res.add("HIGH", "Baseline", "File content AND metadata changed since the baseline was created.")
        if entry.get("fields") is not None:
            add_diff_findings(res, "Baseline", diff_fields(entry["fields"], snapshot_fields(res)), "the baseline")
        else:
            res.add("INFO", "Baseline", "This baseline has no per-field snapshot (created by an older version). "
                    "Re-create it to detect added or changed fields.")
    res.rescore()


# --------------------------------------------------------------------------- #
# Reports
# --------------------------------------------------------------------------- #
def build_html_report(results):
    colors = {"HIGH": "#f8d7da", "MEDIUM": "#fde2c8", "LOW": "#fff3cd", "INFO": "#e7f1ff"}
    parts = ["<!doctype html><meta charset='utf-8'><title>Image Integrity Report</title>"
             "<style>body{font:14px system-ui;margin:2rem;max-width:1000px}table{border-collapse:collapse;width:100%;margin:.5rem 0 1.5rem}"
             "td,th{border:1px solid #ccc;padding:4px 8px;text-align:left;vertical-align:top}h2{margin-bottom:0}"
             "code{font-size:12px;word-break:break-all}</style>",
             f"<h1>Image Metadata Integrity Report</h1><p>Generated {datetime.now():%Y-%m-%d %H:%M:%S}. "
             "Findings are heuristics and not proof of tampering.</p>"]
    for r in results.values():
        parts.append(f"<h2>{html.escape(os.path.basename(r.path))}</h2>"
                     f"<p>Score <b>{r.score}/100</b> - {html.escape(r.verdict)} - type {r.detected_type}<br>"
                     f"SHA-256 <code>{r.sha256}</code></p><table><tr><th>Severity</th><th>Check</th><th>Detail</th></tr>")
        for f in sorted(r.findings, key=lambda f: SEVERITY_ORDER[f.severity]):
            parts.append(f"<tr style='background:{colors[f.severity]}'><td>{f.severity}</td>"
                         f"<td>{html.escape(f.check)}</td><td>{html.escape(f.detail)}</td></tr>")
        parts.append("</table>")
        fl = r.flagged()
        if fl:
            parts.append("<h3>Flagged metadata fields</h3><table><tr><th>Severity</th><th>Category</th>"
                         "<th>Field</th><th>Value</th><th>Reason</th></tr>")
            for (cat, fld), (sev, checks) in sorted(fl.items(), key=lambda kv: SEVERITY_ORDER[kv[1][0]]):
                val = r.metadata.get(cat, {}).get(fld, "")
                parts.append(f"<tr style='background:{colors[sev]}'><td>{sev}</td><td>{html.escape(cat)}</td>"
                             f"<td>{html.escape(fld)}</td><td>{html.escape(str(val))}</td>"
                             f"<td>{html.escape('; '.join(checks))}</td></tr>")
            parts.append("</table>")
    return "".join(parts)


# --------------------------------------------------------------------------- #
# GUI
# --------------------------------------------------------------------------- #
if HAS_TK and HAS_PIL:
    try:
        from PIL import ImageTk
    except ImportError:  # pragma: no cover
        ImageTk = None

    class DiffWindow(tk.Toplevel):
        COLORS = {"ADDED": "#f8d7da", "CHANGED": "#fde2c8", "REMOVED": "#e7f1ff"}

        def __init__(self, master, title, rows):
            super().__init__(master)
            self.title(f"Metadata differences: {title}")
            self.geometry("1000x480")
            tree = ttk.Treeview(self, columns=("change", "cat", "field", "old", "new"), show="headings")
            for c, t, w in (("change", "Change", 80), ("cat", "Category", 120), ("field", "Field", 170),
                            ("old", "Original", 300), ("new", "Current", 300)):
                tree.heading(c, text=t)
                tree.column(c, width=w)
            for k, col in self.COLORS.items():
                tree.tag_configure(k, background=col)
            for r in rows:
                tree.insert("", "end", values=r, tags=(r[0],))
            sb = ttk.Scrollbar(self, command=tree.yview)
            tree.configure(yscrollcommand=sb.set)
            tree.pack(side="left", fill="both", expand=True)
            sb.pack(side="right", fill="y")

    class App(tk.Tk):
        SEV_COLORS = {"HIGH": "#f8d7da", "MEDIUM": "#fde2c8", "LOW": "#fff3cd", "INFO": "#e7f1ff"}

        def __init__(self):
            super().__init__()
            self.title("Image Metadata Integrity Checker")
            self.geometry("1280x800")
            self.minsize(980, 620)
            self.results: Dict[str, Result] = {}
            self.iid_of: Dict[str, str] = {}
            self.path_of: Dict[str, str] = {}
            self.current: Optional[str] = None
            self.queue = queue.Queue()
            self.pending = self.total = 0
            self.run_ela_var = tk.BooleanVar(value=True)
            self.ela_q_var = tk.IntVar(value=90)
            self._photo = None
            self._ffields = {}
            self._build()
            self.after(100, self._poll)

        # ---------- layout ----------
        def _build(self):
            style = ttk.Style(self)
            try:
                style.theme_use("clam")
            except tk.TclError:
                pass
            style.configure("Treeview", rowheight=24)
            style.configure("Big.TLabel", font=("TkDefaultFont", 28, "bold"))
            style.configure("Verdict.TLabel", font=("TkDefaultFont", 13, "bold"))

            bar = ttk.Frame(self, padding=(8, 8, 8, 4))
            bar.pack(fill="x")
            for text, cmd in (("Add images...", self.add_files), ("Add folder...", self.add_folder),
                              ("Remove", self.remove_selected), ("Clear", self.clear_all),
                              ("Re-analyze", self.reanalyze)):
                ttk.Button(bar, text=text, command=cmd).pack(side="left", padx=(0, 6))
            ttk.Separator(bar, orient="vertical").pack(side="left", fill="y", padx=6)
            ttk.Button(bar, text="Create baseline", command=self.create_baseline).pack(side="left", padx=(0, 6))
            ttk.Button(bar, text="Verify baseline", command=self.verify_baseline).pack(side="left", padx=(0, 6))
            ttk.Button(bar, text="Compare with original...", command=self.compare_original).pack(side="left", padx=(0, 6))
            ttk.Button(bar, text="Export HTML", command=lambda: self.export("html")).pack(side="right")
            ttk.Button(bar, text="Export JSON", command=lambda: self.export("json")).pack(side="right", padx=(0, 6))
            ttk.Spinbox(bar, from_=50, to=98, width=4, textvariable=self.ela_q_var).pack(side="right", padx=(0, 10))
            ttk.Label(bar, text="ELA quality").pack(side="right", padx=(0, 4))
            ttk.Checkbutton(bar, text="Run ELA (JPEG)", variable=self.run_ela_var).pack(side="right", padx=(0, 10))

            paned = ttk.PanedWindow(self, orient="horizontal")
            paned.pack(fill="both", expand=True, padx=8, pady=4)

            left = ttk.Frame(paned)
            self.files = ttk.Treeview(left, columns=("score", "verdict"), selectmode="browse")
            self.files.heading("#0", text="Image")
            self.files.heading("score", text="Score")
            self.files.heading("verdict", text="Verdict")
            self.files.column("#0", width=190)
            self.files.column("score", width=50, anchor="center", stretch=False)
            self.files.column("verdict", width=130)
            for sev, col in (("good", "#d7f0dd"), ("warn", "#fff3cd"), ("bad", "#fde2c8"), ("worst", "#f8d7da")):
                self.files.tag_configure(sev, background=col)
            sb = ttk.Scrollbar(left, command=self.files.yview)
            self.files.configure(yscrollcommand=sb.set)
            self.files.pack(side="left", fill="both", expand=True)
            sb.pack(side="right", fill="y")
            self.files.bind("<<TreeviewSelect>>", self._on_select)
            paned.add(left, weight=1)

            right = ttk.Frame(paned)
            head = ttk.Frame(right, padding=(4, 0, 4, 6))
            head.pack(fill="x")
            self.score_lbl = ttk.Label(head, text="-", style="Big.TLabel", width=4, anchor="center")
            self.score_lbl.pack(side="left", padx=(0, 12))
            info = ttk.Frame(head)
            info.pack(side="left", fill="x", expand=True)
            self.verdict_lbl = ttk.Label(info, text="Add images to begin", style="Verdict.TLabel")
            self.verdict_lbl.pack(anchor="w")
            self.counts_lbl = ttk.Label(info, text="")
            self.counts_lbl.pack(anchor="w")
            self.hash_lbl = ttk.Label(info, text="", foreground="#555")
            self.hash_lbl.pack(anchor="w")
            self.gauge = ttk.Progressbar(head, maximum=100, length=160)
            self.gauge.pack(side="right")

            self.nb = ttk.Notebook(right)
            self.nb.pack(fill="both", expand=True)

            # findings
            t1 = ttk.Frame(self.nb)
            self.find_tree = ttk.Treeview(t1, columns=("sev", "check", "detail"), show="headings", selectmode="browse")
            for c, t, w in (("sev", "Severity", 80), ("check", "Check", 150), ("detail", "Detail", 600)):
                self.find_tree.heading(c, text=t)
                self.find_tree.column(c, width=w, stretch=(c == "detail"))
            for sev, col in self.SEV_COLORS.items():
                self.find_tree.tag_configure(sev, background=col)
            self.find_tree.pack(fill="both", expand=True)
            self.find_tree.bind("<<TreeviewSelect>>", self._on_finding)
            self.detail = tk.Text(t1, height=4, wrap="word", state="disabled", background="#fafafa")
            self.detail.pack(fill="x")
            self.nb.add(t1, text="Findings")

            # metadata
            t2 = ttk.Frame(self.nb)
            fbar = ttk.Frame(t2, padding=4)
            fbar.pack(fill="x")
            ttk.Label(fbar, text="Filter:").pack(side="left")
            self.filter_var = tk.StringVar()
            self.filter_var.trace_add("write", lambda *_: self._fill_metadata())
            ttk.Entry(fbar, textvariable=self.filter_var, width=28).pack(side="left", padx=4)
            ttk.Button(fbar, text="Copy value", command=self.copy_value).pack(side="right")
            self.flag_only = tk.BooleanVar(value=False)
            ttk.Checkbutton(fbar, text="Flagged fields only", variable=self.flag_only,
                            command=self._fill_metadata).pack(side="left", padx=(12, 0))
            self.meta_tree = ttk.Treeview(t2, columns=("field", "value", "flag"), show="tree headings")
            self.meta_tree.heading("#0", text="Category")
            self.meta_tree.heading("field", text="Field")
            self.meta_tree.heading("value", text="Value")
            self.meta_tree.heading("flag", text="Suspicion")
            self.meta_tree.column("#0", width=140, stretch=False)
            self.meta_tree.column("field", width=170, stretch=False)
            self.meta_tree.column("value", width=330)
            self.meta_tree.column("flag", width=300)
            for sev, col in self.SEV_COLORS.items():
                self.meta_tree.tag_configure(sev, background=col)
            self.meta_tree.pack(fill="both", expand=True)
            self.meta_tree.bind("<Double-1>", self._open_link)
            self.nb.add(t2, text="Metadata")

            # structure
            t3 = ttk.Frame(self.nb)
            self.struct_tree = ttk.Treeview(t3, columns=("seg", "off", "len", "note"), show="headings")
            for c, t, w in (("seg", "Segment / chunk", 140), ("off", "Offset", 100), ("len", "Length", 100), ("note", "Notes", 400)):
                self.struct_tree.heading(c, text=t)
                self.struct_tree.column(c, width=w, stretch=(c == "note"))
            self.struct_tree.tag_configure("bad", background="#f8d7da")
            self.struct_tree.pack(fill="both", expand=True)
            self.nb.add(t3, text="Structure")

            # ELA
            t4 = ttk.Frame(self.nb)
            eb = ttk.Frame(t4, padding=4)
            eb.pack(fill="x")
            self.ela_lbl = ttk.Label(eb, text="Select a JPEG to view its Error Level Analysis.")
            self.ela_lbl.pack(side="left")
            ttk.Button(eb, text="Save ELA image", command=self.save_ela).pack(side="right")
            self.canvas = tk.Canvas(t4, background="#202020", highlightthickness=0)
            self.canvas.pack(fill="both", expand=True)
            self.canvas.bind("<Configure>", lambda e: self._draw_ela())
            self.nb.add(t4, text="ELA")

            paned.add(right, weight=4)

            bottom = ttk.Frame(self)
            bottom.pack(fill="x", side="bottom")
            self.status = tk.StringVar(value="Ready. Findings are heuristics, not proof of tampering.")
            ttk.Label(bottom, textvariable=self.status, relief="sunken", anchor="w", padding=(6, 2)).pack(
                side="left", fill="x", expand=True)
            self.progress = ttk.Progressbar(bottom, length=180)
            self.progress.pack(side="right")

        # ---------- file management ----------
        def add_files(self):
            paths = filedialog.askopenfilenames(
                title="Select images",
                filetypes=[("Images", " ".join(f"*{e}" for e in IMAGE_EXTS)), ("All files", "*.*")])
            self._analyze(list(paths))

        def add_folder(self):
            folder = filedialog.askdirectory(title="Select a folder")
            if not folder:
                return
            paths = [os.path.join(r, f) for r, _, fs in os.walk(folder) for f in fs
                     if f.lower().endswith(IMAGE_EXTS)]
            if not paths:
                messagebox.showinfo("No images", "No image files were found in that folder.")
                return
            self._analyze(sorted(paths))

        def remove_selected(self):
            sel = self.files.selection()
            if not sel:
                return
            path = self.path_of.pop(sel[0])
            self.iid_of.pop(path, None)
            self.results.pop(path, None)
            self.files.delete(sel[0])
            self.current = None
            self._clear_view()

        def clear_all(self):
            self.files.delete(*self.files.get_children())
            self.results.clear()
            self.iid_of.clear()
            self.path_of.clear()
            self.current = None
            self._clear_view()

        def reanalyze(self):
            sel = self.files.selection()
            self._analyze([self.path_of[sel[0]]] if sel else list(self.iid_of))

        def _analyze(self, paths):
            paths = [p for p in paths if p]
            if not paths:
                return
            if self.pending <= 0:
                self.total = self.pending = 0
            for p in paths:
                if p in self.iid_of:
                    self.files.item(self.iid_of[p], values=("...", "Analyzing..."), tags=())
                else:
                    iid = self.files.insert("", "end", text=os.path.basename(p), values=("...", "Analyzing..."))
                    self.iid_of[p], self.path_of[iid] = iid, p
            self.total += len(paths)
            self.pending += len(paths)
            self.progress.configure(maximum=self.total)
            self.status.set(f"Analyzing {len(paths)} file(s)...")
            threading.Thread(target=self._worker,
                             args=(paths, self.run_ela_var.get(), self.ela_q_var.get()),
                             daemon=True).start()

        def _worker(self, paths, ela, quality):
            for p in paths:
                try:
                    res = analyze_file(p, ela, quality)
                except Exception as e:  # never let a bad file kill the batch
                    res = Result(p)
                    res.add("HIGH", "Analyzer error", f"{type(e).__name__}: {e}")
                    res.rescore()
                self.queue.put((p, res))

        def _poll(self):
            try:
                while True:
                    path, res = self.queue.get_nowait()
                    if path not in self.iid_of:
                        continue  # removed while analysing
                    self.results[path] = res
                    self._update_row(path)
                    self.pending -= 1
                    self.progress["value"] = self.total - self.pending
                    if self.pending <= 0:
                        self.status.set(f"Done. {len(self.results)} file(s) analysed.")
                    sel = self.files.selection()
                    if not sel:
                        self.files.selection_set(self.iid_of[path])
                    elif self.path_of.get(sel[0]) == path:
                        self._show(path)
            except queue.Empty:
                pass
            self.after(100, self._poll)

        def _update_row(self, path):
            r = self.results[path]
            tag = "good" if r.score >= 90 else "warn" if r.score >= 70 else "bad" if r.score >= 45 else "worst"
            self.files.item(self.iid_of[path], values=(r.score, r.verdict), tags=(tag,))

        # ---------- display ----------
        def _on_select(self, _e=None):
            sel = self.files.selection()
            if sel:
                self.current = self.path_of.get(sel[0])
                if self.current in self.results:
                    self._show(self.current)

        def _clear_view(self):
            self.score_lbl.config(text="-", foreground="")
            self.verdict_lbl.config(text="Add images to begin")
            self.counts_lbl.config(text="")
            self.hash_lbl.config(text="")
            self.gauge["value"] = 0
            for t in (self.find_tree, self.meta_tree, self.struct_tree):
                t.delete(*t.get_children())
            self.canvas.delete("all")
            self.ela_lbl.config(text="Select a JPEG to view its Error Level Analysis.")

        def _show(self, path):
            r = self.results[path]
            color = "#1a7f37" if r.score >= 90 else "#9a6700" if r.score >= 70 else "#bc4c00" if r.score >= 45 else "#cf222e"
            self.score_lbl.config(text=str(r.score), foreground=color)
            self.verdict_lbl.config(text=f"{r.verdict}  ({r.detected_type})", foreground=color)
            c = r.counts()
            self.counts_lbl.config(text="   ".join(f"{k} {c[k]}" for k in SEVERITY_ORDER))
            self.hash_lbl.config(text=f"SHA-256 {r.sha256[:32]}...")
            self.gauge["value"] = r.score

            self.find_tree.delete(*self.find_tree.get_children())
            self._ffields = {}
            for f in sorted(r.findings, key=lambda f: SEVERITY_ORDER[f.severity]):
                iid = self.find_tree.insert("", "end", values=(f.severity, f.check, f.detail), tags=(f.severity,))
                self._ffields[iid] = f.fields
            self._set_detail("")
            self._fill_metadata()

            self.struct_tree.delete(*self.struct_tree.get_children())
            for name, off, ln, note in r.structure:
                tag = ("bad",) if "MISMATCH" in note or "TRUNCATED" in note else ()
                self.struct_tree.insert("", "end", values=(name, f"{off:,}", f"{ln:,}", note), tags=tag)
            self._draw_ela()

        def _set_detail(self, text):
            self.detail.config(state="normal")
            self.detail.delete("1.0", "end")
            self.detail.insert("1.0", text)
            self.detail.config(state="disabled")

        def _on_finding(self, _e=None):
            sel = self.find_tree.selection()
            if sel:
                sev, check, detail = self.find_tree.item(sel[0], "values")
                flds = self._ffields.get(sel[0], [])
                extra = "\nFlagged fields: " + ", ".join(f"{c} / {n}" for c, n in flds) if flds else ""
                self._set_detail(f"[{sev}] {check}\n{detail}{extra}")

        def _fill_metadata(self):
            self.meta_tree.delete(*self.meta_tree.get_children())
            r = self.results.get(self.current)
            if not r:
                return
            needle = self.filter_var.get().strip().lower()
            flags = r.flagged()
            only = self.flag_only.get()
            for cat, fields in r.metadata.items():
                items = []
                for k, v in fields.items():
                    fl = flags.get((cat, k))
                    if only and not fl:
                        continue
                    if needle and needle not in k.lower() and needle not in str(v).lower():
                        continue
                    items.append((k, v, fl))
                if items:
                    parent = self.meta_tree.insert("", "end", text=cat, open=True)
                    for k, v, fl in items:
                        why = f"{fl[0]}: {'; '.join(fl[1])}" if fl else ""
                        self.meta_tree.insert(parent, "end", values=(k, v, why), tags=(fl[0],) if fl else ())

        def _open_link(self, _e):
            sel = self.meta_tree.selection()
            if sel:
                vals = self.meta_tree.item(sel[0], "values")
                if len(vals) >= 2 and str(vals[1]).startswith("http"):
                    import webbrowser
                    webbrowser.open(vals[1])

        def copy_value(self):
            sel = self.meta_tree.selection()
            if sel:
                vals = self.meta_tree.item(sel[0], "values")
                if len(vals) >= 2:
                    self.clipboard_clear()
                    self.clipboard_append(vals[1])
                    self.status.set("Value copied to clipboard.")

        def _draw_ela(self):
            self.canvas.delete("all")
            r = self.results.get(self.current)
            if not r or r.ela is None:
                self.ela_lbl.config(text="No ELA available (JPEG only, and ELA must be enabled).")
                return
            self.ela_lbl.config(text=r.ela_stats or "Error Level Analysis")
            cw, ch = max(self.canvas.winfo_width(), 50), max(self.canvas.winfo_height(), 50)
            im = r.ela.copy()
            im.thumbnail((cw, ch))
            self._photo = ImageTk.PhotoImage(im)
            self.canvas.create_image(cw // 2, ch // 2, image=self._photo)

        def save_ela(self):
            r = self.results.get(self.current)
            if not r or r.ela is None:
                messagebox.showinfo("No ELA", "There is no ELA image for the selected file.")
                return
            out = filedialog.asksaveasfilename(defaultextension=".png", filetypes=[("PNG", "*.png")],
                                               initialfile=os.path.splitext(os.path.basename(r.path))[0] + "_ela.png")
            if out:
                r.ela.save(out)
                self.status.set(f"ELA image saved to {out}")

        # ---------- baseline / export ----------
        def create_baseline(self):
            if not self.results:
                messagebox.showinfo("Nothing loaded", "Analyse at least one image first.")
                return
            out = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON", "*.json")],
                                               initialfile="image_baseline.json")
            if out:
                with open(out, "w", encoding="utf-8") as f:
                    json.dump(build_manifest(self.results), f, indent=2)
                self.status.set(f"Baseline for {len(self.results)} file(s) saved to {out}")

        def verify_baseline(self):
            if not self.results:
                messagebox.showinfo("Nothing loaded", "Analyse at least one image first.")
                return
            src = filedialog.askopenfilename(title="Select baseline manifest", filetypes=[("JSON", "*.json")])
            if not src:
                return
            try:
                with open(src, encoding="utf-8") as f:
                    manifest = json.load(f)
                if "files" not in manifest:
                    raise ValueError("not a baseline manifest")
            except Exception as e:
                messagebox.showerror("Invalid baseline", str(e))
                return
            for p, r in self.results.items():
                verify_against_manifest(r, manifest)
                self._update_row(p)
            if self.current:
                self._show(self.current)
            self.status.set("Baseline verification complete. See the 'Baseline' rows in each Findings tab.")

        def compare_original(self):
            if not self.current or self.current not in self.results:
                messagebox.showinfo("No image selected", "Select an analysed image first.")
                return
            src = filedialog.askopenfilename(
                title="Select the ORIGINAL image to compare against",
                filetypes=[("Images", " ".join(f"*{e}" for e in IMAGE_EXTS)), ("All files", "*.*")])
            if not src:
                return
            self.config(cursor="watch")
            self.update_idletasks()
            try:
                orig = analyze_file(src, run_ela_flag=False)
            finally:
                self.config(cursor="")
            cur = self.results[self.current]
            rows = diff_fields(snapshot_fields(orig), snapshot_fields(cur))
            cur.findings = [f for f in cur.findings if not f.check.startswith("Compare")]
            add_diff_findings(cur, "Compare", rows, f"the original '{os.path.basename(src)}'", report_empty=True)
            cur.rescore()
            self._update_row(self.current)
            self._show(self.current)
            self.status.set(f"Compared with {os.path.basename(src)}: {len(rows)} metadata difference(s).")
            if rows:
                DiffWindow(self, f"{os.path.basename(src)}  ->  {os.path.basename(cur.path)}", rows)
            else:
                messagebox.showinfo("No differences", "All tracked metadata fields are identical to the original.")

        def export(self, kind):
            if not self.results:
                messagebox.showinfo("Nothing to export", "Analyse at least one image first.")
                return
            out = filedialog.asksaveasfilename(defaultextension=f".{kind}", filetypes=[(kind.upper(), f"*.{kind}")],
                                               initialfile=f"integrity_report.{kind}")
            if not out:
                return
            with open(out, "w", encoding="utf-8") as f:
                if kind == "json":
                    json.dump([r.to_dict() for r in self.results.values()], f, indent=2, ensure_ascii=False)
                else:
                    f.write(build_html_report(self.results))
            self.status.set(f"Report exported to {out}")


# --------------------------------------------------------------------------- #
# Entry point
# --------------------------------------------------------------------------- #
def cli(paths):
    for p in paths:
        r = analyze_file(p)
        print(f"\n{p}\n  score {r.score}/100 - {r.verdict} ({r.detected_type})")
        for f in sorted(r.findings, key=lambda f: SEVERITY_ORDER[f.severity]):
            print(f"  [{f.severity:6}] {f.check}: {f.detail}")


def main():
    if not HAS_PIL:
        msg = "Pillow is required.  Install it with:  pip install pillow"
        if HAS_TK:
            root = tk.Tk()
            root.withdraw()
            messagebox.showerror("Missing dependency", msg)
        else:
            print(msg)
        return 1
    if len(sys.argv) > 1 and sys.argv[1] == "--cli":
        cli(sys.argv[2:])
        return 0
    if not HAS_TK:
        print("tkinter is not available. Use --cli <files> for command-line mode.")
        return 1
    App().mainloop()
    return 0


if __name__ == "__main__":
    sys.exit(main())
