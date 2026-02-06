#!/usr/bin/env python3
"""Check which OCR engines are available for Docling."""

import shutil
import sys
from importlib.util import find_spec


def check_tesseract():
    """Check Tesseract OCR availability."""
    # Check system binary
    binary = shutil.which("tesseract")
    if not binary:
        return False, "tesseract binary not found in PATH"

    # Check Python binding
    if not find_spec("tesserocr"):
        return False, f"tesseract binary found at {binary}, but tesserocr not installed (pip install tesserocr)"

    return True, f"Available (binary: {binary})"


def check_easyocr():
    """Check EasyOCR availability."""
    if not find_spec("easyocr"):
        return False, "easyocr not installed (pip install easyocr)"
    return True, "Available"


def check_rapidocr():
    """Check RapidOCR availability."""
    if not find_spec("rapidocr_onnxruntime"):
        return False, "rapidocr not installed (pip install rapidocr-onnxruntime)"
    return True, "Available"


def check_ocrmac():
    """Check OcrMac availability (macOS only)."""
    if sys.platform != "darwin":
        return False, "OcrMac only available on macOS"
    if not find_spec("ocrmac"):
        return False, "ocrmac not installed (pip install ocrmac)"
    return True, "Available"


def check_docling():
    """Check Docling installation."""
    if not find_spec("docling"):
        return False, "docling not installed (pip install docling)"
    return True, "Available"


def main():
    print("=" * 60)
    print("Docling OCR Engine Availability Check")
    print("=" * 60)
    print()

    # Check Docling first
    docling_ok, docling_msg = check_docling()
    print(f"Docling:     {'[OK]' if docling_ok else '[MISSING]':10} {docling_msg}")
    print()

    if not docling_ok:
        print("Install Docling first: pip install docling")
        sys.exit(1)

    print("OCR Engines:")
    print("-" * 60)

    engines = [
        ("Tesseract", check_tesseract),
        ("EasyOCR", check_easyocr),
        ("RapidOCR", check_rapidocr),
        ("OcrMac", check_ocrmac),
    ]

    available = []
    for name, check_fn in engines:
        ok, msg = check_fn()
        status = "[OK]" if ok else "[MISSING]"
        print(f"  {name:12} {status:10} {msg}")
        if ok:
            available.append(name)

    print()
    print("-" * 60)

    if available:
        print(f"Available engines: {', '.join(available)}")
        print("\nTo use OCR with Docling:")
        print("  docling --ocr document.pdf")
    else:
        print("No OCR engines available.")
        print("\nTo install an OCR engine:")
        print('  pip install "docling[easyocr]"    # Easiest, pure Python')
        print('  pip install "docling[tesserocr]"  # Requires tesseract binary')
        print('  pip install "docling[rapidocr]"   # CPU-optimized')

    print()


if __name__ == "__main__":
    main()
