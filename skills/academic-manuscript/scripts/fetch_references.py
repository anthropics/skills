#!/usr/bin/env python3
"""
Fetch real citation metadata from CrossRef API and format references.

Usage:
  python3 fetch_references.py --input refs_input.json --output references.json [--style vancouver]
  python3 fetch_references.py --input refs_input.json --output refs.bib --format bibtex

Input JSON format:
  [{"id": 1, "doi": "10.1016/...", "fallback": "Author et al., Journal, Year"}, ...]

Supported styles: vancouver (default), apa, nature
Supported output formats: json (default), bibtex
"""

import argparse
import json
import re
import requests
import sys
import time


def fetch_crossref(doi, email="user@example.com"):
    """Fetch metadata from CrossRef API for a given DOI."""
    url = f"https://api.crossref.org/works/{doi}"
    headers = {"User-Agent": f"AcademicManuscriptSkill/1.0 (mailto:{email})"}
    try:
        r = requests.get(url, headers=headers, timeout=15)
        if r.status_code == 200:
            return r.json()["message"]
    except Exception as e:
        print(f"  Error for {doi}: {e}", file=sys.stderr)
    return None


def format_authors(authors_list, style="vancouver", max_authors=6):
    """Format author list according to citation style."""
    if not authors_list:
        return ""

    formatted = []
    for a in authors_list[:max_authors]:
        family = a.get("family", "")
        given = a.get("given", "")

        if style == "vancouver":
            initials = ". ".join([p[0] for p in given.split() if p]) + "." if given else ""
            formatted.append(f"{family} {initials}".strip())
        elif style == "apa":
            initials = " ".join([f"{p[0]}." for p in given.split() if p]) if given else ""
            formatted.append(f"{family}, {initials}".strip())
        elif style == "nature":
            initials = " ".join([f"{p[0]}." for p in given.split() if p]) if given else ""
            formatted.append(f"{family}, {initials}".strip())

    if style == "apa" and len(formatted) > 1:
        result = ", ".join(formatted[:-1]) + ", & " + formatted[-1]
    else:
        result = ", ".join(formatted)

    if len(authors_list) > max_authors:
        result += ", et al." if style != "apa" else ", ... et al."

    return result


def extract_journal(data):
    """Safely extract journal name from CrossRef data."""
    sct = data.get("short-container-title", [])
    ct = data.get("container-title", [])
    return sct[0] if sct else ct[0] if ct else ""


def extract_year(data):
    """Extract publication year from CrossRef data."""
    issued = data.get("issued", {}).get("date-parts", [[None]])[0]
    return str(issued[0]) if issued and issued[0] else ""


def format_vancouver(data):
    """Format reference in Vancouver/NLM style."""
    authors = format_authors(data.get("author", []), "vancouver")
    title = data.get("title", [""])[0].rstrip(".")
    journal = extract_journal(data)
    year = extract_year(data)
    vol = data.get("volume", "")
    issue = data.get("issue", "")
    pages = data.get("page", "")
    doi = data.get("DOI", "")

    parts = []
    if authors:
        parts.append(authors)
    if title:
        parts.append(title)

    journal_part = ""
    if journal:
        journal_part = f"{journal}."
        if year:
            journal_part += f" {year}"
        if vol:
            journal_part += f";{vol}"
            if issue:
                journal_part += f"({issue})"
        if pages:
            journal_part += f":{pages}"
        journal_part += "."
    elif year:
        journal_part = f"{year}."

    if journal_part:
        parts.append(journal_part)
    if doi:
        parts.append(f"doi:{doi}")

    return " ".join(parts)


def format_apa(data):
    """Format reference in APA 7th style."""
    authors = format_authors(data.get("author", []), "apa")
    title = data.get("title", [""])[0]
    journal = extract_journal(data)
    year = extract_year(data)
    vol = data.get("volume", "")
    issue = data.get("issue", "")
    pages = data.get("page", "")
    doi = data.get("DOI", "")

    ref = f"{authors} ({year}). {title}."
    if journal:
        ref += f" *{journal}*"
        if vol:
            ref += f", *{vol}*"
            if issue:
                ref += f"({issue})"
        if pages:
            ref += f", {pages}"
        ref += "."
    if doi:
        ref += f" https://doi.org/{doi}"

    return ref


def format_nature(data):
    """Format reference in Nature style."""
    authors = format_authors(data.get("author", []), "nature")
    title = data.get("title", [""])[0]
    journal = extract_journal(data)
    year = extract_year(data)
    vol = data.get("volume", "")
    pages = data.get("page", "")

    ref = f"{authors} {title}."
    if journal:
        ref += f" *{journal}*"
        if vol:
            ref += f" **{vol}**"
        if pages:
            ref += f", {pages}"
        if year:
            ref += f" ({year})"
        ref += "."

    return ref


def format_bibtex_entry(ref_id, data, fallback=""):
    """Generate a BibTeX entry from CrossRef data."""
    if data is None:
        # Generate minimal entry from fallback
        key = f"ref{ref_id}"
        return f"@article{{{key},\n  note = {{{fallback}}}\n}}\n"

    authors_raw = data.get("author", [])
    authors = " and ".join(
        [f"{a.get('family', '')}, {a.get('given', '')}" for a in authors_raw]
    )
    title = data.get("title", [""])[0]
    journal = extract_journal(data)
    year = extract_year(data)
    vol = data.get("volume", "")
    issue = data.get("issue", "")
    pages = data.get("page", "")
    doi = data.get("DOI", "")

    # Generate citation key: FirstAuthorYear
    first_author = authors_raw[0].get("family", "Unknown") if authors_raw else "Unknown"
    key = re.sub(r"[^a-zA-Z]", "", first_author) + year

    lines = [f"@article{{{key},"]
    if authors:
        lines.append(f"  author = {{{authors}}},")
    if title:
        lines.append(f"  title = {{{title}}},")
    if journal:
        lines.append(f"  journal = {{{journal}}},")
    if year:
        lines.append(f"  year = {{{year}}},")
    if vol:
        lines.append(f"  volume = {{{vol}}},")
    if issue:
        lines.append(f"  number = {{{issue}}},")
    if pages:
        lines.append(f"  pages = {{{pages}}},")
    if doi:
        lines.append(f"  doi = {{{doi}}},")
    lines.append("}\n")

    return "\n".join(lines)


FORMATTERS = {
    "vancouver": format_vancouver,
    "apa": format_apa,
    "nature": format_nature,
}


def main():
    parser = argparse.ArgumentParser(description="Fetch citation metadata from CrossRef")
    parser.add_argument("--input", required=True, help="Input JSON file with DOIs and fallbacks")
    parser.add_argument("--output", required=True, help="Output file path")
    parser.add_argument("--style", default="vancouver", choices=["vancouver", "apa", "nature"],
                        help="Citation style (default: vancouver)")
    parser.add_argument("--format", default="json", choices=["json", "bibtex"],
                        help="Output format (default: json)")
    parser.add_argument("--email", default="user@example.com",
                        help="Email for CrossRef API polite pool")
    parser.add_argument("--delay", type=float, default=0.3,
                        help="Delay between API requests in seconds")
    args = parser.parse_args()

    formatter = FORMATTERS[args.style]

    with open(args.input) as f:
        refs_input = json.load(f)

    print(f"Fetching {len(refs_input)} references from CrossRef...")
    results = []
    bibtex_entries = []

    for ref in refs_input:
        doi = ref.get("doi")
        rid = ref["id"]
        fallback = ref.get("fallback", f"Reference {rid}")

        if doi:
            print(f"  [{rid}] Fetching {doi}...", end=" ")
            data = fetch_crossref(doi, args.email)
            if data:
                formatted = formatter(data)
                source = "crossref"
                print("OK")
            else:
                formatted = fallback
                source = "fallback"
                print("FALLBACK")

            if args.format == "bibtex":
                bibtex_entries.append(format_bibtex_entry(rid, data, fallback))

            time.sleep(args.delay)
        else:
            formatted = fallback
            source = "fallback"
            data = None
            print(f"  [{rid}] No DOI, using fallback")

            if args.format == "bibtex":
                bibtex_entries.append(format_bibtex_entry(rid, None, fallback))

        results.append({
            "id": rid,
            "doi": doi,
            "formatted": formatted,
            "source": source,
        })

    # Write output
    if args.format == "json":
        with open(args.output, "w") as f:
            json.dump(results, f, indent=2, ensure_ascii=False)
    elif args.format == "bibtex":
        with open(args.output, "w") as f:
            f.write("% Auto-generated BibTeX file\n")
            f.write(f"% {len(bibtex_entries)} references\n\n")
            f.write("\n".join(bibtex_entries))

    crossref_count = sum(1 for r in results if r["source"] == "crossref")
    print(f"\nDone! {crossref_count}/{len(results)} fetched from CrossRef")
    print(f"Output: {args.output}")


if __name__ == "__main__":
    main()
