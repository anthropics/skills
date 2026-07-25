# Copyright 2026 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Europe PMC API CLI — search, download, full text, citations & references.

Usage examples:
  uv run europepmc_api.py search "CRISPR" --max_results 5 --output results.json
  uv run europepmc_api.py get_fulltext PMC8371605 --output fulltext.txt
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import urllib.parse
import xml.etree.ElementTree as ET

from polite_http import http_client

_API_BASE = "https://www.ebi.ac.uk/europepmc/webservices/rest/"
_PDF_BASE = "https://europepmc.org/"

_API_CLIENT = http_client.HttpClient(
    _API_BASE,
    qps=1.0,
    referer="https://github.com/google-deepmind/science-skills/tree/main/literature-search-europepmc",
)
_PDF_CLIENT = http_client.HttpClient(
    _PDF_BASE,
    qps=1.0,
    referer="https://github.com/google-deepmind/science-skills/tree/main/literature-search-europepmc",
)


def write_output(data, output_file, *, write_as_json=True):
  """Writes data to a file, optionally as JSON.

  Args:
    data: The data to write. Serialized as JSON when write_as_json is True.
    output_file: Path to the output file.
    write_as_json: If True (default), serialize data with json.dump. If False,
      write data directly as text.
  """
  try:
    with open(output_file, "w", encoding="utf-8") as f:
      if write_as_json:
        json.dump(data, f, indent=2)
      else:
        f.write(data)
    print(f"Success! Data written to: {output_file}")
  except (OSError, TypeError) as e:
    print(f"Error writing to file {output_file}: {e}")
    sys.exit(1)


def _extract_all_text(elem):
  """Recursively extract all text content from an XML element."""
  parts = []
  if elem.text:
    parts.append(elem.text)
  for child in elem:
    parts.append(_extract_all_text(child))
    if child.tail:
      parts.append(child.tail)
  return "".join(parts)


def _xml_to_plain_text(xml_string):
  """Extract article title, abstract, and body text from JATS XML."""
  try:
    root = ET.fromstring(xml_string)
  except ET.ParseError:
    # If XML parsing fails, fall back to regex-based tag stripping.
    text = re.sub(r"<[^>]+>", " ", xml_string)
    return re.sub(r"\s+", " ", text).strip()

  sections = []

  # Extract article title.
  for title in root.iter("article-title"):
    t = _extract_all_text(title).strip()
    if t:
      sections.append(f"# {t}")
    break

  # Extract abstract(s).
  for abstract in root.iter("abstract"):
    text = _extract_all_text(abstract).strip()
    if text:
      sections.append(f"## Abstract\n\n{text}")

  # Extract body paragraphs.
  for body in root.iter("body"):
    body_parts = []
    for elem in body.iter():
      tag = elem.tag.split("}")[-1] if "}" in elem.tag else elem.tag
      if tag == "title":
        title_text = _extract_all_text(elem).strip()
        if title_text:
          body_parts.append(f"\n## {title_text}\n")
      elif tag == "p":
        para = _extract_all_text(elem).strip()
        if para:
          body_parts.append(para)
    if body_parts:
      sections.append("\n\n".join(body_parts))
    break  # Only the first <body> element.

  return "\n\n".join(sections)


# ---------------------------------------------------------------------------
# Subcommands
# ---------------------------------------------------------------------------


def search(query, max_results=10, result_type="core", cursor="*", sort=""):
  """Search Europe PMC and return open-access article metadata."""
  # Enforce open-access only: append filter if not already present.
  if "OPEN_ACCESS:" not in query.upper():
    query = f"({query}) AND OPEN_ACCESS:y"
  params = {
      "query": query,
      "format": "json",
      "resultType": result_type,
      "pageSize": min(max_results, 1000),
      "cursorMark": cursor,
  }
  if sort:
    params["sort"] = sort

  url = f"search?{urllib.parse.urlencode(params)}"
  print(f"Searching Europe PMC (open access): {query}", file=sys.stderr)
  data = _API_CLIENT.fetch_json(url)
  results = data.get("resultList", {}).get("result", [])
  hit_count = data.get("hitCount", 0)
  next_cursor = data.get("nextCursorMark", "")

  return {
      "hitCount": hit_count,
      "nextCursorMark": next_cursor if next_cursor != cursor else "",
      "results": results[:max_results],
  }


def download_pdf(pmcid, output):
  """Download an open-access PDF from Europe PMC."""
  url = f"articles/{pmcid}?pdf=render"
  print(f"Downloading PDF for {pmcid}...", file=sys.stderr)

  content = _PDF_CLIENT.fetch_bytes(url, timeout=60)

  if not content[:5].startswith(b"%PDF"):
    sys.exit(
        f"Error: Response for {pmcid} is not a valid PDF."
        " The article may not be available in open access."
    )

  out_dir = os.path.dirname(output)
  if out_dir:
    os.makedirs(out_dir, exist_ok=True)

  with open(output, "wb") as f:
    f.write(content)

  print(f"Saved {len(content)} bytes to {output}", file=sys.stderr)


def get_fulltext(pmcid, fmt="text"):
  """Retrieve the full text of an open-access article by PMCID."""
  url = f"{pmcid}/fullTextXML"
  print(f"Fetching full text for {pmcid}...", file=sys.stderr)
  xml_content = _API_CLIENT.fetch_text(url, timeout=60)

  if fmt == "xml":
    return xml_content
  else:
    return _xml_to_plain_text(xml_content)


def get_citations(source, article_id, page=1, page_size=25):
  """Retrieve articles citing a given paper."""
  params = urllib.parse.urlencode({
      "page": page,
      "pageSize": min(page_size, 1000),
      "format": "json",
  })
  url = f"{source}/{article_id}/citations?{params}"
  print(f"Fetching citations for {source}/{article_id}...", file=sys.stderr)
  data = _API_CLIENT.fetch_json(url)
  hit_count = data.get("hitCount", 0)
  citations = data.get("citationList", {}).get("citation", [])
  return {"hitCount": hit_count, "citations": citations}


def get_references(source, article_id, page=1, page_size=25):
  """Retrieve the reference list of a given paper."""
  params = urllib.parse.urlencode({
      "page": page,
      "pageSize": min(page_size, 1000),
      "format": "json",
  })
  url = f"{source}/{article_id}/references?{params}"
  print(f"Fetching references for {source}/{article_id}...", file=sys.stderr)
  data = _API_CLIENT.fetch_json(url)
  hit_count = data.get("hitCount", 0)
  references = data.get("referenceList", {}).get("reference", [])
  return {"hitCount": hit_count, "references": references}


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main():
  parser = argparse.ArgumentParser(
      description=(
          "Europe PMC API: search, download, full text, citations & references."
      )
  )
  sub = parser.add_subparsers(dest="command", required=True)

  # search -------------------------------------------------------------------
  p_search = sub.add_parser("search", help="Search Europe PMC")
  p_search.add_argument("query", help="Search query")
  p_search.add_argument(
      "--max_results", type=int, default=10, help="Max results (default 10)"
  )
  p_search.add_argument(
      "--result_type",
      default="core",
      choices=["core", "lite"],
      help="Result detail level (default: core)",
  )
  p_search.add_argument(
      "--cursor",
      default="*",
      help="Cursor mark for pagination (default: first page)",
  )
  p_search.add_argument(
      "--sort",
      default="",
      help="Sort order, e.g. 'CITED desc' or 'P_PDATE_D desc'",
  )
  p_search.add_argument("--output", required=True, help="Output JSON file path")

  # download_pdf -------------------------------------------------------------
  p_dl = sub.add_parser("download_pdf", help="Download PDF by PMCID")
  p_dl.add_argument("pmcid", help="PubMed Central ID (e.g. PMC10462087)")
  p_dl.add_argument("--output", required=True, help="Output filepath")

  # get_fulltext -------------------------------------------------------------
  p_ft = sub.add_parser("get_fulltext", help="Retrieve full text by PMCID")
  p_ft.add_argument("pmcid", help="PubMed Central ID (e.g. PMC8371605)")
  p_ft.add_argument(
      "--format",
      dest="fmt",
      default="text",
      choices=["text", "xml"],
      help="Output format: 'text' (stripped plain text) or 'xml' (raw XML)",
  )
  p_ft.add_argument("--output", required=True, help="Output file path")

  # get_citations ------------------------------------------------------------
  p_cit = sub.add_parser("get_citations", help="Get articles citing a paper")
  p_cit.add_argument("source", help="Source database (e.g. MED, PMC, PPR)")
  p_cit.add_argument("article_id", help="Article ID (e.g. PMID or PMCID)")
  p_cit.add_argument("--page", type=int, default=1, help="Page number")
  p_cit.add_argument(
      "--page_size", type=int, default=25, help="Results per page"
  )
  p_cit.add_argument("--output", required=True, help="Output JSON file path")

  # get_references -----------------------------------------------------------
  p_ref = sub.add_parser("get_references", help="Get reference list of a paper")
  p_ref.add_argument("source", help="Source database (e.g. MED, PMC, PPR)")
  p_ref.add_argument("article_id", help="Article ID (e.g. PMID or PMCID)")
  p_ref.add_argument("--page", type=int, default=1, help="Page number")
  p_ref.add_argument(
      "--page_size", type=int, default=25, help="Results per page"
  )
  p_ref.add_argument("--output", required=True, help="Output JSON file path")

  args = parser.parse_args()

  if args.command == "search":
    result = search(
        args.query, args.max_results, args.result_type, args.cursor, args.sort
    )
    write_output(result, args.output)
    print(
        f"{len(result['results'])} of {result['hitCount']} result(s).",
        file=sys.stderr,
    )
    if result["nextCursorMark"]:
      print(f"Next cursor: {result['nextCursorMark']}", file=sys.stderr)
  elif args.command == "download_pdf":
    download_pdf(args.pmcid, args.output)
  elif args.command == "get_fulltext":
    text = get_fulltext(args.pmcid, args.fmt)
    write_output(text, args.output, write_as_json=False)
  elif args.command == "get_citations":
    result = get_citations(
        args.source, args.article_id, args.page, args.page_size
    )
    write_output(result, args.output)
    print(
        f"{len(result['citations'])} of {result['hitCount']} citation(s).",
        file=sys.stderr,
    )
  elif args.command == "get_references":
    result = get_references(
        args.source, args.article_id, args.page, args.page_size
    )
    write_output(result, args.output)
    print(
        f"{len(result['references'])} of {result['hitCount']} reference(s).",
        file=sys.stderr,
    )


if __name__ == "__main__":
  main()
