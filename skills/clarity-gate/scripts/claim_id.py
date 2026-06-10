#!/usr/bin/env python3
"""
Clarity Gate: Claim ID Computation

Reference implementation per FORMAT_SPEC §1.3.4 (RFC-001).
Produces stable, hash-based claim IDs for HITL tracking.

Usage:
    python claim_id.py "Base price is $99/mo" "api-pricing/1"
    # Output: claim-75fb137a

Test Vectors (FORMAT_SPEC §18.2):
    claim_id("Base price is $99/mo", "api-pricing/1") == "claim-75fb137a"
    claim_id("The API supports GraphQL", "features/1") == "claim-eb357742"

Normalization (per RFC-001 §3.4):
    - Text: strip outer whitespace, collapse internal whitespace to single space
    - Location: strip outer whitespace
    
    This ensures stable IDs regardless of formatting variations:
    "Price is  $99" (2 spaces) → same hash as "Price is $99" (1 space)
"""

import hashlib
import sys


def normalize_text(text: str) -> str:
    """
    Normalize claim text for consistent hashing.
    
    Per RFC-001 §3.4:
    - Strip leading/trailing whitespace
    - Collapse multiple internal spaces to single space
    """
    return ' '.join(text.strip().split())


def claim_id(text: str, location: str) -> str:
    """
    Compute a stable claim ID from claim text and location.
    
    Args:
        text: The full claim text (e.g., "Base price is $99/mo")
        location: The heading_slug/ordinal (e.g., "api-pricing/1")
    
    Returns:
        Claim ID in format "claim-XXXXXXXX" (8-char hex hash)
    
    Algorithm:
        1. Normalize text (strip + collapse whitespace)
        2. Strip location whitespace
        3. Concatenate with pipe delimiter
        4. SHA-256 hash the UTF-8 encoded payload
        5. Take first 8 hex characters
        6. Prefix with "claim-"
    """
    normalized_text = normalize_text(text)
    normalized_location = location.strip()
    
    payload = f"{normalized_text}|{normalized_location}"
    hash_hex = hashlib.sha256(payload.encode('utf-8')).hexdigest()
    return f"claim-{hash_hex[:8]}"


def main():
    if len(sys.argv) == 3:
        text = sys.argv[1]
        location = sys.argv[2]
        print(claim_id(text, location))
    elif len(sys.argv) == 2 and sys.argv[1] == "--test":
        # Run test vectors
        print("=== Test Vectors ===")
        tests = [
            ("Base price is $99/mo", "api-pricing/1", "claim-75fb137a"),
            ("The API supports GraphQL", "features/1", "claim-eb357742"),
        ]
        all_pass = True
        for text, location, expected in tests:
            result = claim_id(text, location)
            status = "PASS" if result == expected else "FAIL"
            if result != expected:
                all_pass = False
            print(f"{status} claim_id({text!r}, {location!r})")
            print(f"    Expected: {expected}")
            print(f"    Got:      {result}")
        
        print("\n=== Normalization Tests ===")
        # These should all produce the same hash
        norm_tests = [
            ("Price is $99", "loc/1"),
            ("Price is  $99", "loc/1"),      # double space
            ("  Price is $99  ", "loc/1"),   # outer spaces
            ("Price is $99", "  loc/1  "),   # location spaces
        ]
        base_result = claim_id(norm_tests[0][0], norm_tests[0][1])
        print(f"Base: {base_result}")
        for text, location in norm_tests[1:]:
            result = claim_id(text, location)
            status = "PASS" if result == base_result else "FAIL"
            if result != base_result:
                all_pass = False
            print(f"{status} claim_id({text!r}, {location!r}) == base")
        
        print()
        sys.exit(0 if all_pass else 1)
    else:
        print("Usage: python claim_id.py <text> <location>")
        print("       python claim_id.py --test")
        print()
        print("Example:")
        print('  python claim_id.py "Base price is $99/mo" "api-pricing/1"')
        print("  # Output: claim-75fb137a")
        sys.exit(1)


if __name__ == "__main__":
    main()
