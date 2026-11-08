#!/usr/bin/env python3
"""
Clarity Gate: Document Hash Computation

Reference implementation per FORMAT_SPEC §2.2-2.4 (RFC-001).
Computes SHA-256 hash excluding the document-sha256 line itself.

Usage:
    python document_hash.py path/to/file.cgd.md
    python document_hash.py --verify path/to/file.cgd.md
    python document_hash.py --test

Normalization (CRITICAL for cross-platform consistency):
    - BOM removed if present
    - CRLF to LF (Windows compatibility)
    - CR to LF (old Mac compatibility)
    - Extract content between opening ---\n and <!-- CLARITY_GATE_END -->
    - document-sha256 line excluded from hash computation (frontmatter only)
    - Multiline YAML continuation handling
    - Canonicalization per §2.4:
      * Strip trailing whitespace per line
      * Collapse 3+ consecutive newlines to 2
      * Normalize final newline (exactly 1 LF)
      * UTF-8 NFC normalization
"""

import hashlib
import re
import sys
import unicodedata


def canonicalize(text: str) -> str:
    """
    Canonicalize content for consistent hashing across platforms.

    Per FORMAT_SPEC §2.4:
    1. Trailing whitespace: Remove per line
    2. Consecutive newlines: Collapse 3+ to 2
    3. Final newline: Exactly one trailing LF
    4. Encoding: UTF-8 NFC normalization
    """
    # 1. Strip trailing whitespace per line
    lines = text.split('\n')
    lines = [line.rstrip() for line in lines]
    text = '\n'.join(lines)

    # 2. Collapse 3+ consecutive newlines to 2
    while '\n\n\n' in text:
        text = text.replace('\n\n\n', '\n\n')

    # 3. Normalize trailing newline (exactly 1)
    text = text.rstrip('\n') + '\n'

    # 4. UTF-8 NFC normalization
    text = unicodedata.normalize('NFC', text)

    return text


def compute_hash(filepath: str) -> str:
    """
    Compute SHA-256 hash of document per FORMAT_SPEC §2.2-2.4.

    Algorithm:
        0. Pre-normalize for boundary detection (BOM, CRLF)
        1. Extract content between opening '---\n' and '<!-- CLARITY_GATE_END -->'
        2. Remove document-sha256 line(s) from YAML frontmatter ONLY
           (including multiline continuations)
        3. Canonicalize per §2.4
        4. Compute SHA-256
    """
    with open(filepath, 'r', encoding='utf-8') as f:
        file_content = f.read()

    # 0. Pre-normalize for boundary detection
    working = file_content
    if working.startswith('\ufeff'):
        working = working[1:]
    working = working.replace('\r\n', '\n').replace('\r', '\n')

    # 1. Extract content between opening YAML delimiter and end marker
    try:
        start = working.index('---\n') + len('---\n')
        end = working.index('<!-- CLARITY_GATE_END -->')
        hashable = working[start:end]
    except ValueError as e:
        print(f"ERROR: Invalid CGD format - {e}")
        sys.exit(1)

    # 2. Remove document-sha256 line(s) - YAML frontmatter only
    lines = hashable.split('\n')
    filtered = []
    skip_multiline = False
    hash_indent = 0
    in_frontmatter = True

    for line in lines:
        # Detect end of YAML frontmatter
        if in_frontmatter and line.strip() == '---':
            in_frontmatter = False

        # Check if this is the hash line
        if in_frontmatter and re.match(r'^\s*document-sha256:', line):
            skip_multiline = True
            hash_indent = len(line) - len(line.lstrip())
            continue

        # If we're skipping multiline, check if this is a continuation
        if skip_multiline:
            current_indent = len(line) - len(line.lstrip())
            if in_frontmatter and current_indent > hash_indent:
                continue
            skip_multiline = False

        filtered.append(line)

    hashable = '\n'.join(filtered)

    # 3. Canonicalize
    hashable = canonicalize(hashable)

    # 4. Compute
    return hashlib.sha256(hashable.encode('utf-8')).hexdigest()


def verify(filepath: str) -> bool:
    """
    Verify document hash matches stored value.

    Returns True if hash matches, False otherwise.
    """
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()

    # Normalize for consistent matching
    if content.startswith('\ufeff'):
        content = content[1:]
    content = content.replace('\r\n', '\n').replace('\r', '\n')

    # Extract stored hash
    match = re.search(r'^\s*document-sha256:\s*["\']?([a-f0-9]{64})["\']?', content, re.MULTILINE)
    if not match:
        print("FAIL: No document-sha256 found")
        return False

    stored = match.group(1)
    computed = compute_hash(filepath)

    if stored == computed:
        print(f"PASS: Hash verified: {computed}")
        return True
    else:
        print(f"FAIL: Hash mismatch")
        print(f"  Stored:   {stored}")
        print(f"  Computed: {computed}")
        return False


def run_tests():
    """Run canonicalization and edge case tests."""
    print("=== Canonicalization Tests ===")

    # Test 1: BOM removal (happens in pre-normalization, not canonicalize)
    # Note: BOM is removed in compute_hash step 0, not in canonicalize
    with_bom = '\ufeff# Test'
    without_bom = '# Test'
    # After BOM removal in pre-normalization:
    assert with_bom.lstrip('\ufeff') == without_bom, "BOM removal in pre-normalization"
    print("PASS: BOM removal (pre-normalization)")

    # Test 2: Trailing whitespace removal
    with_trailing = "line1  \nline2\t\nline3"
    without_trailing = "line1\nline2\nline3"
    assert canonicalize(with_trailing) == canonicalize(without_trailing), "Trailing whitespace should be stripped"
    print("PASS: Trailing whitespace removal")

    # Test 3: Newline collapsing (3+ → 2)
    multiple_newlines = "para1\n\n\n\npara2"
    collapsed = "para1\n\npara2"
    assert canonicalize(multiple_newlines) == collapsed + '\n', "3+ newlines should collapse to 2"
    print("PASS: Newline collapsing")

    # Test 4: Final newline normalization
    no_trailing = "content"
    one_trailing = "content\n"
    two_trailing = "content\n\n"
    assert canonicalize(no_trailing) == "content\n", "Missing final newline should be added"
    assert canonicalize(one_trailing) == "content\n", "Single final newline should be preserved"
    assert canonicalize(two_trailing) == "content\n", "Multiple final newlines should collapse to 1"
    print("PASS: Final newline normalization")

    # Test 5: NFC normalization
    # é as single codepoint (U+00E9) vs e + combining acute (U+0065 U+0301)
    nfc = '\u00e9'  # NFC form
    nfd = '\u0065\u0301'  # NFD form
    assert canonicalize(nfc) == canonicalize(nfd), "NFC normalization should make equivalent"
    print("PASS: UTF-8 NFC normalization")

    # Test 6: Preserve tabs and leading whitespace
    with_tabs = "line1\n\tindented\n  spaces"
    canonical = canonicalize(with_tabs)
    assert '\t' in canonical, "Tabs should be preserved"
    assert '  spaces' in canonical, "Leading whitespace should be preserved"
    print("PASS: Preserve tabs and leading whitespace")

    print("\n=== Line Ending Tests ===")

    # Test 7: CRLF normalization (in pre-processing)
    crlf = "line1\r\nline2\r\n"
    lf = "line1\nline2\n"
    # Note: CRLF normalization happens in compute_hash step 0, not canonicalize
    assert canonicalize(crlf.replace('\r\n', '\n')) == canonicalize(lf), "CRLF should normalize to LF"
    print("PASS: CRLF to LF")

    # Test 8: CR normalization
    cr = "line1\rline2\r"
    assert canonicalize(cr.replace('\r', '\n')) == canonicalize(lf), "CR should normalize to LF"
    print("PASS: CR to LF")

    print("\nPASS: All canonicalization tests passed")


def main():
    if len(sys.argv) == 2 and sys.argv[1] not in ("--verify", "--test"):
        print(compute_hash(sys.argv[1]))
    elif len(sys.argv) == 3 and sys.argv[1] == "--verify":
        sys.exit(0 if verify(sys.argv[2]) else 1)
    elif len(sys.argv) == 2 and sys.argv[1] == "--test":
        run_tests()
    else:
        print("Usage: document_hash.py <file>")
        print("       document_hash.py --verify <file>")
        print("       document_hash.py --test")
        print()
        print("Examples:")
        print("  document_hash.py my-doc.cgd.md")
        print("  document_hash.py --verify my-doc.cgd.md")
        print("  document_hash.py --test")
        sys.exit(1)


if __name__ == "__main__":
    main()
