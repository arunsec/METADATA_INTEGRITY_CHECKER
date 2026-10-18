# Image Metadata Integrity Checker

A Python/Tkinter GUI that looks for signs that an image or its metadata has been edited, forged, damaged or tampered with. Each image gets an integrity score (0-100) and a list of findings. Suspect metadata fields are highlighted in the Metadata tab.

> Findings are heuristics, not proof. Stripped or rewritten EXIF is normal for images that passed through social media, messengers or editors.

## Features

- **Structure checks:** file signature vs. extension, JPEG marker walk, truncation, data appended after the image (hidden payloads), PNG chunk CRC validation, WebP/BMP/GIF consistency, full decode test.
- **EXIF tampering forensics:** raw TIFF parsing to find overwritten text, out-of-order or duplicate tags, wrong data types, tags in the wrong IFD, fields newer than the declared `ExifVersion`, overlapping regions, unreferenced slack bytes, MakerNote brand vs. `Make`, byte order vs. manufacturer, broken Canon MakerNote offsets.
- **Value logic:** date consistency, EXIF vs. real dimensions, ExposureTime vs. ShutterSpeedValue, FNumber vs. ApertureValue, focal length vs. lens range, invalid enumerations, GPS validity.
- **Other sources:** XMP edit history and ID mismatches, embedded thumbnail vs. main image, editing-software tags, C2PA presence (signature not validated).
- **Pixel forensics:** Error Level Analysis (JPEG) with block-cluster detection, estimated JPEG quality.
- **Baselines:** create a SHA-256 + per-field metadata baseline and verify later, or compare against an original image to list added / changed / removed fields.
- **Reports:** export HTML or JSON.

## Install

```bash
git clone https://github.com/<your-username>/image-integrity-checker.git
cd image-integrity-checker
pip install -r requirements.txt
```

Tkinter ships with most Python installs. On some Linux distributions install it separately, e.g. `sudo apt install python3-tk`.

## Usage

```bash
python image_integrity_checker.py
```

Add images or a folder, select a file to see its findings, metadata, file structure and ELA image.

Command-line mode (no GUI):

```bash
python image_integrity_checker.py --cli photo1.jpg photo2.png
```

## Requirements

- Python 3.8+
- Pillow

## License

Add a license of your choice (for example MIT) via GitHub's "Add file > Create new file > LICENSE".
