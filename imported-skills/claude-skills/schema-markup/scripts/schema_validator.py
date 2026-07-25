#!/usr/bin/env python3
"""
schema_validator.py — Extracts and validates JSON-LD structured data from HTML.

Usage:
    python3 schema_validator.py [file.html]
    cat page.html | python3 schema_validator.py

If no file is provided, runs on embedded sample HTML for demonstration.

Output: Human-readable validation report + JSON summary.
Scoring: 0-100 per schema block based on required/recommended field coverage.
"""

import json
import sys
import re
import select
from html.parser import HTMLParser
from typing import List, Dict, Any, Optional


# ─── Required and recommended fields per schema type ─────────────────────────

SCHEMA_RULES: Dict[str, Dict[str, List[str]]] = {
    "Article": {
        "required": ["headline", "image", "datePublished", "author"],
        "recommended": ["dateModified", "publisher", "description", "url", "mainEntityOfPage"],
    },
    "BlogPosting": {
        "required": ["headline", "image", "datePublished", "author"],
        "recommended": ["dateModified", "publisher", "description", "url", "mainEntityOfPage"],
    },
    "NewsArticle": {
        "required": ["headline", "image", "datePublished", "author"],
        "recommended": ["dateModified", "publisher", "description", "url"],
    },
    "HowTo": {
        "required": ["name", "step"],
        "recommended": ["description", "image", "totalTime", "tool", "supply", "estimatedCost"],
    },
    "FAQPage": {
        "required": ["mainEntity"],
        "recommended": [],
    },
    "Product": {
        "required": ["name", "offers"],
        "recommended": ["description", "image", "sku", "brand", "aggregateRating"],
    },
    "Organization": {
        "required": ["name", "url"],
        "recommended": ["logo", "sameAs", "contactPoint", "description", "foundingDate"],
    },
    "LocalBusiness": {
        "required": ["name", "address"],
        "recommended": ["telephone", "openingHoursSpecification", "geo", "priceRange", "image", "url"],
    },
    "BreadcrumbList": {
        "required": ["itemListElement"],
        "recommended": [],
    },
    "VideoObject": {
        "required": ["name", "description", "thumbnailUrl", "uploadDate"],
        "recommended": ["duration", "contentUrl", "embedUrl", "interactionStatistic", "hasPart"],
    },
    "WebSite": {
        "required": ["url"],
        "recommended": ["name", "potentialAction"],
    },
    "Event": {
        "required": ["name", "startDate", "location"],
        "recommended": ["endDate", "description", "image", "organizer", "offers"],
    },
    "Recipe": {
        "required": ["name", "image", "author", "datePublished"],
        "recommended": ["description", "cookTime", "prepTime", "totalTime", "recipeYield",
                        "recipeIngredient", "recipeInstructions", "aggregateRating"],
    },
}

KNOWN_TYPES = set(SCHEMA_RULES.keys())


# ─── HTML Parser to extract JSON-LD blocks ───────────────────────────────────

class JSONLDExtractor(HTMLParser):
    """Extracts all <script type="application/ld+json"> blocks from HTML."""

    def __init__(self):
        super().__init__()
        self.blocks: List[str] = []
        self._in_ld_json = False
        self._current = []

    def handle_starttag(self, tag: str, attrs: list):
        if tag.lower() == "script":
            attr_dict = dict(attrs)
            if attr_dict.get("type", "").lower() == "application/ld+json":
                self._in_ld_json = True
                self._current = []

    def handle_endtag(self, tag: str):
        if tag.lower() == "script" and self._in_ld_json:
            self._in_ld_json = False
            self.blocks.append("".join(self._current).strip())

    def handle_data(self, data: str):
        if self._in_ld_json:
            self._current.append(data)


# ─── Validation logic ────────────────────────────────────────────────────────

def detect_type(obj: Dict) -> Optional[str]:
    """Determine the @type of a schema object."""
    t = obj.get("@type")
    if isinstance(t, list):
        # Return first known type
        for item in t:
            if item in KNOWN_TYPES:
                return item
        return t[0] if t else None
    return t


def score_schema(schema_type: str, obj: Dict) -> Dict:
    """Score a single schema object against known rules. Returns 0-100."""
    if schema_type not in SCHEMA_RULES:
        return {
            "score": 50,
            "status": "unknown_type",
            "required_present": [],
            "required_missing": [],
            "recommended_present": [],
            "recommended_missing": [],
            "notes": [f"No validation rules defined for '{schema_type}' — manual check recommended."],
        }

    rules = SCHEMA_RULES[schema_type]
    required = rules.get("required", [])
    recommended = rules.get("recommended", [])

    required_present = [f for f in required if f in obj and obj[f]]
    required_missing = [f for f in required if f not in obj or not obj[f]]
    recommended_present = [f for f in recommended if f in obj and obj[f]]
    recommended_missing = [f for f in recommended if f not in obj or not obj[f]]

    # Score: required fields = 70 points, recommended = 30 points
    req_score = (len(required_present) / len(required) * 70) if required else 70
    rec_score = (len(recommended_present) / len(recommended) * 30) if recommended else 30
    total_score = int(req_score + rec_score)

    notes = []

    # Type-specific checks
    if schema_type in ("Article", "BlogPosting", "NewsArticle"):
        image = obj.get("image")
        if image:
            img_url = image if isinstance(image, str) else image.get("url", "") if isinstance(image, dict) else ""
            if img_url and not img_url.startswith("http"):
                notes.append("⚠️  'image' URL appears to be relative — must be absolute (https://...)")
        if "datePublished" in obj:
            dp = obj["datePublished"]
            if not re.match(r"\d{4}-\d{2}-\d{2}", str(dp)):
                notes.append("⚠️  'datePublished' should be ISO 8601 format: YYYY-MM-DD")

    if schema_type == "Product":
        offers = obj.get("offers", {})
        if isinstance(offers, dict):
            price = offers.get("price")
            if isinstance(price, str) and any(c in price for c in "$€£¥"):
                notes.append("⚠️  'offers.price' should be numeric (49.99), not a string with currency symbol.")
            avail = offers.get("availability", "")
            if avail and not avail.startswith("https://schema.org/"):
                notes.append("⚠️  'offers.availability' must use full URL: https://schema.org/InStock")

    if schema_type == "FAQPage":
        entities = obj.get("mainEntity", [])
        if isinstance(entities, list):
            for i, q in enumerate(entities):
                if not q.get("acceptedAnswer", {}).get("text"):
                    notes.append(f"⚠️  Question #{i+1} has empty 'acceptedAnswer.text'")

    if schema_type == "BreadcrumbList":
        items = obj.get("itemListElement", [])
        if isinstance(items, list):
            positions = [item.get("position") for item in items if isinstance(item, dict)]
            if sorted(positions) != list(range(1, len(positions) + 1)):
                notes.append("⚠️  'itemListElement' positions must be sequential integers starting at 1.")

    return {
        "score": total_score,
        "status": "valid" if not required_missing else "missing_required",
        "required_present": required_present,
        "required_missing": required_missing,
        "recommended_present": recommended_present,
        "recommended_missing": recommended_missing,
        "notes": notes,
    }


def validate_block(raw_json: str, block_index: int) -> List[Dict]:
    """Parse and validate a single JSON-LD block. Returns list of results (may contain @graph)."""
    results = []
    try:
        data = json.loads(raw_json)
    except json.JSONDecodeError as e:
        return [{
            "block": block_index,
            "type": "PARSE_ERROR",
            "score": 0,
            "status": "parse_error",
            "error": str(e),
            "notes": ["❌ JSON is malformed — fix syntax before validation."],
        }]

    # Handle @graph
    objects = data.get("@graph", [data]) if isinstance(data, dict) else [data]

    for obj in objects:
        if not isinstance(obj, dict):
            continue
        schema_type = detect_type(obj)
        if not schema_type:
            results.append({
                "block": block_index,
                "type": "UNKNOWN",
                "score": 0,
                "status": "no_type",
                "notes": ["❌ No '@type' found in schema object."],
            })
            continue

        validation = score_schema(schema_type, obj)
        results.append({
            "block": block_index,
            "type": schema_type,
            **validation,
        })

    return results


def grade(score: int) -> str:
    if score >= 90:
        return "🟢 Excellent"
    if score >= 70:
        return "🟡 Good"
    if score >= 50:
        return "🟠 Needs Work"
    return "🔴 Poor"


# ─── Report printer ──────────────────────────────────────────────────────────

def print_report(all_results: List[Dict], html_source: str) -> None:
    print("\n" + "═" * 60)
    print("  SCHEMA MARKUP VALIDATION REPORT")
    print("═" * 60)

    if not all_results:
        print("\n❌ No JSON-LD blocks found in this HTML.")
        print("   Add structured data in <script type=\"application/ld+json\"> tags.\n")
        return

    total_score = 0
    for r in all_results:
        print(f"\n── Block {r['block']} · @type: {r['type']} ──")
        score = r.get("score", 0)
        total_score += score
        print(f"   Score: {score}/100  {grade(score)}")

        if r.get("status") == "parse_error":
            print(f"   ❌ Parse error: {r.get('error')}")
            continue

        if r.get("required_missing"):
            print(f"   Missing required: {', '.join(r['required_missing'])}")
        else:
            print(f"   Required fields: ✅ All present ({', '.join(r.get('required_present', []))})")

        if r.get("recommended_missing"):
            print(f"   Missing recommended: {', '.join(r['recommended_missing'])}")
        if r.get("recommended_present"):
            print(f"   Recommended present: {', '.join(r['recommended_present'])}")

        for note in r.get("notes", []):
            print(f"   {note}")

    avg = total_score // len(all_results) if all_results else 0
    print(f"\n{'═' * 60}")
    print(f"  OVERALL SCORE: {avg}/100  {grade(avg)}")
    print(f"  Blocks analyzed: {len(all_results)}")
    print("═" * 60)

    print("\n📋 TESTING CHECKLIST")
    print("  □ Google Rich Results Test: https://search.google.com/test/rich-results")
    print("  □ Schema.org Validator: https://validator.schema.org")
    print("  □ After deploy: Check Search Console → Enhancements\n")


# ─── Sample HTML ─────────────────────────────────────────────────────────────

SAMPLE_HTML = """<!DOCTYPE html>
<html>
<head>
  <title>How to Write Cold Emails That Get Replies</title>

  <!-- Article schema — headline present, but image is relative URL -->
  <script type="application/ld+json">
  {
    "@context": "https://schema.org",
    "@type": "BlogPosting",
    "headline": "How to Write Cold Emails That Get Replies",
    "image": "/images/cold-email-guide.jpg",
    "datePublished": "2024-03-01",
    "dateModified": "2024-03-15",
    "author": {
      "@type": "Person",
      "name": "Reza Rezvani"
    },
    "publisher": {
      "@type": "Organization",
      "name": "Growth Lab",
      "logo": {
        "@type": "ImageObject",
        "url": "https://growthlab.com/logo.png"
      }
    }
  }
  </script>

  <!-- FAQPage schema — complete and valid -->
  <script type="application/ld+json">
  {
    "@context": "https://schema.org",
    "@type": "FAQPage",
    "mainEntity": [
      {
        "@type": "Question",
        "name": "What is the ideal length for a cold email?",
        "acceptedAnswer": {
          "@type": "Answer",
          "text": "Keep cold emails under 150 words. Busy professionals scan, not read. If your email needs scrolling, it will not get a reply."
        }
      },
      {
        "@type": "Question",
        "name": "How many follow-ups should I send?",
        "acceptedAnswer": {
          "@type": "Answer",
          "text": "Send 3-5 follow-ups with increasing gaps (3 days, 5 days, 7 days, 14 days). Each follow-up must add new value — never just check in."
        }
      }
    ]
  }
  </script>

  <!-- BreadcrumbList — position gap (jumps from 1 to 3) -->
  <script type="application/ld+json">
  {
    "@context": "https://schema.org",
    "@type": "BreadcrumbList",
    "itemListElement": [
      {
        "@type": "ListItem",
        "position": 1,
        "name": "Home",
        "item": "https://growthlab.com"
      },
      {
        "@type": "ListItem",
        "position": 3,
        "name": "How to Write Cold Emails",
        "item": "https://growthlab.com/blog/cold-email-guide"
      }
    ]
  }
  </script>

</head>
<body>
  <h1>How to Write Cold Emails That Get Replies</h1>
  <p>Cold email works when it sounds human...</p>
</body>
</html>
"""


# ─── Main ─────────────────────────────────────────────────────────────────────

def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Extracts and validates JSON-LD structured data from HTML. "
                    "Scores 0-100 per schema block based on required/recommended field coverage."
    )
    parser.add_argument(
        "file", nargs="?", default=None,
        help="Path to an HTML file to validate. "
             "Use '-' to read from stdin. If omitted, runs embedded sample."
    )
    args = parser.parse_args()

    if args.file:
        if args.file == "-":
            html = sys.stdin.read()
        else:
            try:
                with open(args.file, "r", encoding="utf-8") as f:
                    html = f.read()
            except FileNotFoundError:
                print(f"Error: File not found: {args.file}", file=sys.stderr)
                sys.exit(1)
    else:
        print("No file provided — running on embedded sample HTML.\n")
        html = SAMPLE_HTML

    extractor = JSONLDExtractor()
    extractor.feed(html)

    all_results = []
    for i, block in enumerate(extractor.blocks, start=1):
        results = validate_block(block, i)
        all_results.extend(results)

    print_report(all_results, html)

    # JSON output for programmatic use
    summary = {
        "blocks_found": len(extractor.blocks),
        "schemas_validated": len(all_results),
        "average_score": (sum(r.get("score", 0) for r in all_results) // len(all_results)) if all_results else 0,
        "results": all_results,
    }
    print("\n── JSON Output ──")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
