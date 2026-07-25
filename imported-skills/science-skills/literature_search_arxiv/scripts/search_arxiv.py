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

"""Searches the arXiv API and returns results in a clean JSON format.

This script allows querying the arXiv API using either a search query string
or a list of arXiv IDs. It parses the XML response and outputs a JSON object
containing the search results.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import json
import sys
import urllib.parse
import xml.etree.ElementTree as ET

from polite_http import http_client

_BASE_URL = "http://export.arxiv.org/api/query?"
_CLIENT = http_client.HttpClient(_BASE_URL, qps=1.0 / 3.0)


def parse_args() -> argparse.Namespace:
  """Parses command-line arguments for the arXiv search script.

  Returns:
    argparse.Namespace: An object containing the parsed command-line arguments.
  """
  parser = argparse.ArgumentParser(
      description="Search arXiv API and return clean JSON"
  )
  parser.add_argument(
      "--query",
      type=str,
      help="Search query string (e.g., 'au:einstein AND ti:relativity')",
  )
  parser.add_argument(
      "--id_list", type=str, help="Comma-separated list of arXiv IDs"
  )
  parser.add_argument("--start", type=int, default=0, help="Pagination offset")
  parser.add_argument(
      "--max_results", type=int, default=10, help="Number of results to return"
  )
  parser.add_argument(
      "--sort_by",
      type=str,
      choices=["relevance", "lastUpdatedDate", "submittedDate"],
      help="Sort by",
  )
  parser.add_argument(
      "--sort_order",
      type=str,
      choices=["ascending", "descending"],
      help="Sort order",
  )
  return parser.parse_args()


def strip_namespace(tag: str) -> str:
  if tag.startswith("{"):
    return tag.split("}", 1)[1]
  return tag


def search_arxiv(args: argparse.Namespace):
  """Searches the arXiv API and prints results as a JSON string.

  Constructs a query to the arXiv API based on the provided arguments,
  fetches the XML response, parses it, and prints a JSON object containing
  the extracted paper information.

  Args:
    args: An argparse.Namespace object containing the search parameters (query,
      id_list, start, max_results, sort_by, sort_order).
  """
  params = {"start": args.start, "max_results": args.max_results}
  if args.query:
    params["search_query"] = args.query
  if args.id_list:
    params["id_list"] = args.id_list
  if args.sort_by:
    params["sortBy"] = args.sort_by
  if args.sort_order:
    params["sortOrder"] = args.sort_order

  # Use quote_plus to ensure spaces become '+' as required by arXiv API
  query_string = urllib.parse.urlencode(
      params, quote_via=urllib.parse.quote_plus
  )
  url = _BASE_URL + query_string

  results = []
  xml_data = _CLIENT.fetch_bytes(url)
  root = ET.fromstring(xml_data)

  for entry in root.findall("{http://www.w3.org/2005/Atom}entry"):
    paper = {}
    authors = []

    for child in entry:
      tag = strip_namespace(child.tag)
      if tag == "id":
        # Extract just the ID part (e.g., http://arxiv.org/abs/2305.10601v1
        # -> 2305.10601v1)
        if child.text:
          paper["id"] = child.text.split("/abs/")[-1]
      elif tag == "title":
        paper["title"] = (
            child.text.replace("\n", " ").strip() if child.text else ""
        )
      elif tag == "summary":
        paper["summary"] = (
            child.text.replace("\n", " ").strip() if child.text else ""
        )
      elif tag == "published":
        paper["published"] = child.text
      elif tag == "author":
        for name_node in child.findall("{http://www.w3.org/2005/Atom}name"):
          authors.append(name_node.text)
      elif tag == "link":
        if child.get("title") == "pdf":
          paper["pdf_url"] = child.get("href")
      elif tag == "primary_category":
        paper["primary_category"] = child.get("term")
      elif tag in {"doi", "journal_ref", "comment"}:
        paper[tag] = child.text

    paper["authors"] = authors
    results.append(paper)

    print(
        json.dumps(
            {
                "status": "success",
                "results_count": len(results),
                "papers": results,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
  main_args = parse_args()
  if not main_args.query and not main_args.id_list:
    print(
        json.dumps(
            {
                "status": "error",
                "message": "Must provide either --query or --id_list",
            },
            indent=2,
        )
    )
    sys.exit(1)
  search_arxiv(main_args)
