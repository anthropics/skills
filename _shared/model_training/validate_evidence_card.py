"""
Evidence Card Validator - Deterministic validation
NO subprocesses. NO LLM interpretation. Pure pass/fail.
"""
import json
import sys
from pathlib import Path

REQUIRED_FIELDS = [
    "uid", "Location", "claim", "parties_involved",
    "description_of_evidence", "depiction_quote",
    "significance", "precedence", "citation", "source"
]

CLAIM_ELEMENTS = [
    "Fourth Amendment", "Sixth Amendment", "Fourteenth Amendment",
    "Malicious Prosecution", "Conspiracy", "Deliberate Indifference",
    "Due Process", "Equal Protection", "Brady", "Monell",
    "Prosecutorial Misconduct", "Judicial Misconduct"
]

def validate_card(card_path):
    """
    Validate an evidence card.
    Returns: (pass: bool, errors: list)
    """
    card_path = Path(card_path)
    
    if not card_path.exists():
        return False, [f"File not found: {card_path}"]
    
    try:
        with open(card_path, 'r', encoding='utf-8') as f:
            card = json.load(f)
    except json.JSONDecodeError as e:
        return False, [f"Invalid JSON: {e}"]
    except Exception as e:
        return False, [f"Read error: {e}"]

    errors = []

    # Check required fields
    for field in REQUIRED_FIELDS:
        if field not in card:
            errors.append(f"Missing required field: {field}")
        elif not card[field]:
            errors.append(f"Empty field: {field}")

    # Validate UID format (should be numeric or alphanumeric)
    uid = card.get("uid", "")
    if not uid:
        errors.append("UID is empty")
    
    # Check claim references a valid legal element
    claim_text = str(card.get("claim", ""))
    if claim_text and not any(element.lower() in claim_text.lower() for element in CLAIM_ELEMENTS):
        errors.append(f"Claim should reference a constitutional violation or legal theory")

    # Validate parties_involved structure
    parties = card.get("parties_involved", [])
    if not isinstance(parties, list):
        errors.append("parties_involved must be a list")
    elif len(parties) == 0:
        errors.append("parties_involved must have at least one party")

    # Check Location has required structure
    location = card.get("Location", [])
    if not isinstance(location, list):
        errors.append("Location must be a list")

    # Check precedence exists
    precedence = card.get("precedence", [])
    if not precedence:
        errors.append("Must cite at least one case in precedence")

    # Check depiction_quote is not empty placeholder
    quote = card.get("depiction_quote", "")
    if quote and quote.startswith("{{"):
        errors.append("depiction_quote contains unfilled placeholder")

    return len(errors) == 0, errors


def validate_card_dict(card_dict):
    """Validate a card from a dictionary (no file)"""
    errors = []
    
    for field in REQUIRED_FIELDS:
        if field not in card_dict:
            errors.append(f"Missing required field: {field}")
    
    return len(errors) == 0, errors


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python validate_evidence_card.py <card.json>")
        sys.exit(1)
    
    passed, errors = validate_card(sys.argv[1])
    
    if passed:
        print("✓ VALID")
        sys.exit(0)
    else:
        print("✗ INVALID")
        for error in errors:
            print(f"  - {error}")
        sys.exit(1)
