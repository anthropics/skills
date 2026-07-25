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

"""Search bioRxiv/medRxiv by date range with local filtering."""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import json
import sys
from polite_http import http_client

client = http_client.HttpClient(base_url="https://api.biorxiv.org/", qps=1.0)

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

BIORXIV_PAGE_SIZE = 30
BIORXIV_CATEGORIES = [
    "animal_behavior_and_cognition",
    "biochemistry",
    "bioengineering",
    "bioinformatics",
    "biophysics",
    "cancer_biology",
    "cell_biology",
    "clinical_trials",
    "developmental_biology",
    "ecology",
    "epidemiology",
    "evolutionary_biology",
    "genetics",
    "genomics",
    "immunology",
    "microbiology",
    "molecular_biology",
    "neuroscience",
    "paleontology",
    "pathology",
    "pharmacology_and_toxicology",
    "physiology",
    "plant_biology",
    "scientific_communication_and_education",
    "synthetic_biology",
    "systems_biology",
    "zoology",
]

MEDRXIV_CATEGORIES = [
    "addiction_medicine",
    "allergy_and_immunology",
    "anesthesia",
    "cardiovascular_medicine",
    "dentistry_and_oral_medicine",
    "dermatology",
    "emergency_medicine",
    "endocrinology",
    "epidemiology",
    "forensic_medicine",
    "gastroenterology",
    "genetic_and_genomic_medicine",
    "health_informatics",
    "health_economics_and_outcomes_research",
    "health_policy",
    "health_systems_and_quality_improvement",
    "hematology",
    "hiv_aids",
    "infectious_diseases",
    "intensive_care_and_critical_care_medicine",
    "medical_education",
    "medical_ethics",
    "nephrology",
    "neurology",
    "nursing",
    "nutrition",
    "obstetrics_and_gynecology",
    "occupational_and_environmental_health",
    "oncology",
    "ophthalmology",
    "orthopedics",
    "otolaryngology",
    "pain_medicine",
    "palliative_care",
    "pathology",
    "pediatrics",
    "pharmacology_and_therapeutics",
    "primary_care_research",
    "psychiatry_and_clinical_psychology",
    "public_and_global_health",
    "radiology_and_imaging",
    "rehabilitation_medicine_and_physical_therapy",
    "respiratory_medicine",
    "rheumatology",
    "sexual_and_reproductive_health",
    "sports_medicine",
    "surgery",
    "toxicology",
    "transplantation",
    "urology",
]


def search_biorxiv(args):
  """Searches bioRxiv/medRxiv for preprints in the given date range."""
  # Strict Category Validation
  if args.category:
    if args.server == "biorxiv" and args.category not in BIORXIV_CATEGORIES:
      sys.exit(
          f"Error: Invalid category '{args.category}' for bioRxiv.\n"
          f"Valid categories are: {', '.join(BIORXIV_CATEGORIES)}"
      )
    elif args.server == "medrxiv" and args.category not in MEDRXIV_CATEGORIES:
      sys.exit(
          f"Error: Invalid category '{args.category}' for medRxiv.\n"
          f"Valid categories are: {', '.join(MEDRXIV_CATEGORIES)}"
      )

  base_url = (
      f"https://api.biorxiv.org/details/{args.server}"
      f"/{args.start_date}/{args.end_date}"
  )
  cursor = 0
  all_results = []
  total_fetched = 0
  total_after_category = 0
  page_num = 0

  print(
      f"Fetching metadata for {args.server} from {args.start_date}"
      f" to {args.end_date}...",
      file=sys.stderr,
  )
  if args.category:
    print(f"  Category filter: {args.category}", file=sys.stderr)
  if args.keywords:
    print(
        f"  Keyword filter ({args.match_logic}): {', '.join(args.keywords)}",
        file=sys.stderr,
    )
  if args.author:
    print(f"  Author filter: {args.author}", file=sys.stderr)

  while True:
    url = f"{base_url}/{cursor}"
    page_num += 1
    data = client.fetch_json(url)

    collection = data.get("collection", [])
    if not collection:
      break

    total_fetched += len(collection)

    # Print pagination progress to stderr
    print(
        f"  [Page {page_num}] Fetched {total_fetched} papers...",
        file=sys.stderr,
    )

    for paper in collection:
      # Local Category Filtering
      # The API may ignore the category query parameter, so we always
      # enforce category filtering locally as a reliable fallback.
      if args.category:
        paper_category = paper.get("category", "").lower().replace(" ", "_")
        if paper_category != args.category.lower():
          continue

      total_after_category += 1

      # Local Author Filtering
      if args.author:
        author_list = paper.get("authors", "").lower().split(";")
        if not any(args.author.lower() in a for a in author_list):
          continue

      # Local Keyword Filtering (checks title and abstract)
      if args.keywords:
        title = paper.get("title", "").lower()
        abstract = paper.get("abstract", "").lower()
        text_to_search = f"{title} {abstract}"

        kw_lower = [k.lower() for k in args.keywords]
        if args.match_logic == "AND":
          if not all(kw in text_to_search for kw in kw_lower):
            continue
        else:  # OR logic
          if not any(kw in text_to_search for kw in kw_lower):
            continue

      # Strip abstract if not requested
      if not args.include_abstracts and "abstract" in paper:
        del paper["abstract"]

      all_results.append(paper)

    # The bioRxiv API returns results in pages of up to `BIORXIV_PAGE_SIZE`
    # items. We advance `cursor` by the page size and stop once we get a short
    # page.  NOTE: We intentionally do NOT use `total_count` for
    # termination because the API sometimes reports `BIORXIV_PAGE_SIZE` (the
    # page size) rather than the true total, which causes premature stopping.
    cursor += len(collection)

    if len(collection) < BIORXIV_PAGE_SIZE:
      # A short page is the only reliable signal that we've fetched everything.
      break

  # Print summary to stderr so the agent can assess results
  print("\n--- Search Summary ---", file=sys.stderr)
  print(
      f"  Total papers in date range: {total_fetched}"
      + (f" (across {page_num} page(s))" if page_num > 1 else ""),
      file=sys.stderr,
  )
  if args.category:
    print(
        f"  After category filter ('{args.category}'): {total_after_category}",
        file=sys.stderr,
    )
  print(
      f"  Final results after all filters: {len(all_results)}",
      file=sys.stderr,
  )
  if not all_results:
    print(
        "  Tip: No results found. Try widening the date range, removing keyword"
        " filters, or changing the category. If searching for a specific paper,"
        " consider using search_by_doi.py with the paper's DOI instead.",
        file=sys.stderr,
    )

  print(json.dumps(all_results, indent=2))


def main():
  """Parses arguments and searches bioRxiv/medRxiv."""
  parser = argparse.ArgumentParser(
      description="Search bioRxiv/medRxiv by date range with local filtering."
  )
  parser.add_argument(
      "--server",
      choices=["biorxiv", "medrxiv"],
      default="biorxiv",
      help="The preprint server to query.",
  )
  parser.add_argument(
      "--start_date",
      required=True,
      help="Start date (YYYY-MM-DD)",
  )
  parser.add_argument(
      "--end_date",
      required=True,
      help="End date (YYYY-MM-DD)",
  )
  parser.add_argument("--category", help="Strict server-side category filter")
  parser.add_argument("--author", help="Local author filter (case-insensitive)")
  parser.add_argument(
      "--keywords",
      nargs="+",
      help="Local keyword filters applied to title and abstract",
  )
  parser.add_argument(
      "--match_logic",
      choices=["AND", "OR"],
      default="AND",
      help="Keyword matching logic",
  )
  parser.add_argument(
      "--include_abstracts",
      action="store_true",
      help="Include full abstracts in the JSON output",
  )

  args = parser.parse_args()
  search_biorxiv(args)


if __name__ == "__main__":
  main()
