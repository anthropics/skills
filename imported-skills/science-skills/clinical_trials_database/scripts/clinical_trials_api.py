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

"""CLI tool for interacting with the ClinicalTrials.gov API v2.

This script provides command-line access to various endpoints of the
ClinicalTrials.gov API, including fetching study details, searching for studies,
and counting matching studies.
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

from polite_http import http_client

BASE_URL = "https://clinicaltrials.gov/api/v2"
_CLIENT = http_client.HttpClient(BASE_URL + "/", qps=1.0)

DEFAULT_STUDY_FIELDS = (
    "NCTId,BriefTitle,OverallStatus,Phase,BriefSummary,"
    "ConditionsModule,ArmsInterventionsModule,EligibilityModule"
)


def write_output(data, output_file):
  """Writes data to a JSON file.

  Args:
    data: The data to serialize as JSON.
    output_file: Path to the output file.
  """
  try:
    with open(output_file, "w", encoding="utf-8") as f:
      json.dump(data, f, indent=2)
    print(f"Success! Data written to: {output_file}")
  except (OSError, TypeError) as e:
    print(f"Error writing to file {output_file}: {e}")
    sys.exit(1)


def _build_advanced_filter(args):
  """Builds an Essie advanced filter string from parsed CLI arguments.

  Args:
    args: Parsed argparse namespace with optional phase, age_group, study_type,
      sponsor, and advanced attributes.

  Returns:
    A combined Essie filter string joined by AND, or None if no
    filter clauses apply.
  """
  clauses = []
  if getattr(args, "phase", None):
    clauses.append(f"AREA[Phase]{args.phase}")
  if getattr(args, "age_group", None):
    clauses.append(f"AREA[StdAge]{args.age_group}")
  if getattr(args, "study_type", None):
    clauses.append(f"AREA[StudyType]{args.study_type}")
  if getattr(args, "sponsor", None):
    clauses.append(f"AREA[LeadSponsorName]{args.sponsor}")
  if getattr(args, "has_results", False):
    clauses.append("AREA[HasResults]true")
  if getattr(args, "advanced", None):
    clauses.append(args.advanced)
  if not clauses:
    return None
  return " AND ".join(clauses)


def _build_search_params(args):
  """Builds a list of (key, value) query-string pairs from CLI arguments.

  Args:
    args: Parsed argparse namespace containing search filter attributes.

  Returns:
    A list of (key, value) tuples suitable for urllib.parse.urlencode.
  """
  params = []
  if getattr(args, "condition", None):
    params.append(("query.cond", args.condition))
  if getattr(args, "intervention", None):
    params.append(("query.intr", args.intervention))
  if getattr(args, "term", None):
    params.append(("query.term", args.term))
  if getattr(args, "title", None):
    params.append(("query.titles", args.title))
  if getattr(args, "location", None):
    params.append(("query.locn", args.location))
  if getattr(args, "id_filter", None):
    params.append(("query.id", args.id_filter))
  if getattr(args, "status", None):
    params.append(("filter.overallStatus", args.status))
  advanced = _build_advanced_filter(args)
  if advanced:
    params.append(("filter.advanced", advanced))
  if getattr(args, "fields", None):
    params.append(("fields", args.fields))
  limit = getattr(args, "limit", None)
  if limit:
    params.append(("pageSize", str(limit)))
  if getattr(args, "sort", None):
    params.append(("sort", args.sort))
  if getattr(args, "count_total", False):
    params.append(("countTotal", "true"))
  if getattr(args, "page_token", None):
    params.append(("pageToken", args.page_token))
  return params


def _add_search_arguments(parser):
  """Registers common search/filter flags on the given argument parser.

  Args:
    parser: An argparse.ArgumentParser or subparser to add arguments to.
  """
  parser.add_argument(
      "--condition", help="Condition or disease (maps to query.cond)"
  )
  parser.add_argument(
      "--intervention", help="Intervention or treatment (maps to query.intr)"
  )
  parser.add_argument(
      "--term",
      help="General search across all text fields (maps to query.term)",
  )
  parser.add_argument(
      "--title", help="Search within study titles (maps to query.titles)"
  )
  parser.add_argument(
      "--location", help="Search location fields (maps to query.locn)"
  )
  parser.add_argument(
      "--id", dest="id_filter", help="Search by study ID (maps to query.id)"
  )
  parser.add_argument(
      "--status",
      help=(
          "Filter by recruitment status. Comma-separated. "
          "Values: RECRUITING, COMPLETED, ACTIVE_NOT_RECRUITING, "
          "NOT_YET_RECRUITING, ENROLLING_BY_INVITATION, SUSPENDED, "
          "TERMINATED, WITHDRAWN"
      ),
  )
  parser.add_argument(
      "--phase",
      help=(
          "Filter by trial phase. "
          "Values: EARLY_PHASE1, PHASE1, PHASE2, PHASE3, PHASE4, NA"
      ),
  )
  parser.add_argument(
      "--age-group",
      dest="age_group",
      help="Filter by age group. Values: CHILD, ADULT, OLDER_ADULT",
  )
  parser.add_argument(
      "--study-type",
      dest="study_type",
      help=(
          "Filter by study type. Values: INTERVENTIONAL, OBSERVATIONAL,"
          " EXPANDED_ACCESS"
      ),
  )
  parser.add_argument(
      "--sponsor", help="Filter by lead sponsor name (Essie AREA expression)"
  )
  parser.add_argument(
      "--has-results",
      dest="has_results",
      action="store_true",
      help="Filter for studies that have results available",
  )
  parser.add_argument(
      "--advanced",
      help="Raw Essie filter expression (combined with other flags via AND)",
  )
  parser.add_argument(
      "--fields", help="Comma-separated list of fields to return"
  )
  parser.add_argument(
      "--sort",
      help=(
          "Sort results, e.g. 'LastUpdatePostDate:desc' or"
          " 'EnrollmentCount:asc'"
      ),
  )
  parser.add_argument(
      "--count-total",
      dest="count_total",
      action="store_true",
      help="Include total count of matching studies in the response",
  )
  parser.add_argument(
      "--page-token",
      dest="page_token",
      help="Token for fetching the next page of results",
  )
  parser.add_argument(
      "--limit",
      type=int,
      default=10,
      help="Number of results per page (max 1000)",
  )


def get_study(args):
  """Retrieves a single study by NCT ID and writes it to a JSON file.

  Args:
    args: Parsed argparse namespace with nct_id, optional fields, and output.
  """
  url = f"{BASE_URL}/studies/{urllib.parse.quote(args.nct_id)}"
  fields = args.fields if args.fields else DEFAULT_STUDY_FIELDS
  url += f"?fields={urllib.parse.quote(fields)}"
  data = _CLIENT.fetch_json(url)
  write_output(data, args.output)


def get_eligibility(args):
  """Retrieves the eligibility module for a study and writes it to a JSON file.

  Args:
    args: Parsed argparse namespace with nct_id and output.
  """
  url = f"{BASE_URL}/studies/{urllib.parse.quote(args.nct_id)}"
  url += f"?fields={urllib.parse.quote('NCTId,BriefTitle,EligibilityModule')}"
  data = _CLIENT.fetch_json(url)
  write_output(data, args.output)


def search(args):
  """Searches for studies and writes results to a JSON file.

  Matches studies based on the given filters.

  Args:
    args: Parsed argparse namespace with search filter attributes and output.
  """
  params = _build_search_params(args)
  query_string = urllib.parse.urlencode(params)
  url = f"{BASE_URL}/studies" + (f"?{query_string}" if query_string else "")
  data = _CLIENT.fetch_json(url)
  write_output(data, args.output)


def count(args):
  """Counts studies matching the given filters and prints the total as JSON.

  Args:
    args: Parsed argparse namespace with search filter attributes.
  """
  params = _build_search_params(args)
  params.append(("countTotal", "true"))
  params.append(("pageSize", "0"))
  params = [(k, v) for k, v in params if k not in ("pageSize",) or v == "0"]
  final_params = []
  seen_keys = {}
  for k, v in params:
    if k == "pageSize":
      if k not in seen_keys:
        seen_keys[k] = True
        final_params.append((k, "0"))
    elif k == "countTotal":
      if k not in seen_keys:
        seen_keys[k] = True
        final_params.append((k, "true"))
    else:
      final_params.append((k, v))

  query_string = urllib.parse.urlencode(final_params)
  url = f"{BASE_URL}/studies" + (f"?{query_string}" if query_string else "")
  data = _CLIENT.fetch_json(url)
  write_output({"totalCount": data.get("totalCount", 0)}, args.output)


def raw_query(args):
  """Executes a raw API request against an arbitrary endpoint.

  Args:
    args: Parsed argparse namespace with endpoint and optional params.
  """
  endpoint = args.endpoint.lstrip("/")
  params_dict = {}
  if args.params:
    try:
      params_dict = json.loads(args.params)
    except json.JSONDecodeError:
      print(json.dumps({"error": "Invalid JSON string provided for params."}))
      sys.exit(1)
  query_string = urllib.parse.urlencode(params_dict, doseq=True)
  url = f"{BASE_URL}/{endpoint}" + (f"?{query_string}" if query_string else "")
  data = _CLIENT.fetch_json(url)
  write_output(data, args.output)


def main():
  """Parses CLI arguments and dispatches to the appropriate command handler."""
  parser = argparse.ArgumentParser(description="ClinicalTrials.gov API v2 CLI")
  subparsers = parser.add_subparsers(dest="command", required=True)

  p_get = subparsers.add_parser("get-study", help="Retrieve a study by NCT ID")
  p_get.add_argument("nct_id", help="NCT ID of the study (e.g. NCT04886804)")
  p_get.add_argument(
      "--fields",
      help=(
          "Comma-separated fields to return. "
          "Defaults to a useful subset if omitted."
      ),
  )
  p_get.add_argument("--output", required=True, help="Output JSON file path")

  p_elig = subparsers.add_parser(
      "get-eligibility",
      help="Retrieve just the eligibility/inclusion criteria for a study",
  )
  p_elig.add_argument("nct_id", help="NCT ID of the study")
  p_elig.add_argument("--output", required=True, help="Output JSON file path")

  p_search = subparsers.add_parser(
      "search", help="Search for studies with filters"
  )
  _add_search_arguments(p_search)
  p_search.add_argument("--output", required=True, help="Output JSON file path")

  p_count = subparsers.add_parser(
      "count",
      help="Count matching studies without returning records",
  )
  _add_search_arguments(p_count)
  p_count.add_argument("--output", required=True, help="Output JSON file path")

  p_raw = subparsers.add_parser(
      "raw-query", help="Execute a raw API request (escape hatch)"
  )
  p_raw.add_argument("--endpoint", required=True, help="API endpoint path")
  p_raw.add_argument("--params", help="JSON-encoded dict of query parameters")
  p_raw.add_argument("--output", required=True, help="Output JSON file path")

  args = parser.parse_args()

  commands = {
      "get-study": get_study,
      "get-eligibility": get_eligibility,
      "search": search,
      "count": count,
      "raw-query": raw_query,
  }
  commands[args.command](args)


if __name__ == "__main__":
  main()
