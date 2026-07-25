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

"""Queries the Open Targets Platform GraphQL API.

This script provides a command-line interface to query various endpoints of the
Open Targets GraphQL API, including GWAS studies, QTL credible sets, L2G
predictions, target druggability, and disease/target associations.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import json
import re
import sys
from typing import Any

from polite_http import http_client

BASE_URL = "https://api.platform.opentargets.org/api/v4/graphql"
_CLIENT = http_client.HttpClient(BASE_URL, qps=1.0)

CLINICAL_STAGES = ["PHASE_0", "PHASE_1", "PHASE_2", "PHASE_3", "APPROVAL"]
STAGE_ORDER = {stage: i for i, stage in enumerate(CLINICAL_STAGES)}


def normalize_variant_id(variant_id: str) -> str:
  """Normalize variant ID by stripping 'chr' prefix if present."""
  return re.sub(r"^chr", "", variant_id, flags=re.IGNORECASE)


def truncate_data(data: Any, limit: int = 50) -> Any:
  """Recursively truncates lists within a dictionary or list to a given limit.

  This function is designed to limit the size of potentially large lists within
  the JSON response from the OpenTargets API, making the output more manageable.
  Specifically handles the "rows" field within dictionaries that also have a
  "count" field, common in OpenTargets GraphQL responses.

  Args:
    data: The data structure (dict or list) to potentially truncate.
    limit: The maximum number of items to keep in any list.

  Returns:
    The truncated data structure.
  """
  if isinstance(data, list):
    if len(data) > limit:
      result = [truncate_data(item, limit) for item in data[:limit]]
      result.append({"_truncated": f"(Showing {limit} of {len(data)} items)"})
      return result
    return [truncate_data(item, limit) for item in data]
  elif isinstance(data, dict):
    result = {}
    for k, v in data.items():
      if k == "rows" and isinstance(v, list) and "count" in data:
        # specific to Open Targets GraphQL
        count = data.get("count", len(v))
        if len(v) > limit:
          result[k] = [truncate_data(item, limit) for item in v[:limit]]
          result[k].append({"_truncated": f"(Showing {limit} of {count} rows)"})
        else:
          result[k] = [truncate_data(item, limit) for item in v]
      else:
        result[k] = truncate_data(v, limit)
    return result
  else:
    return data


def execute_query(
    query: str,
    variables: dict[str, Any],
    output_file: str,
    limit: int = 50,
    page_size: int = 200,
):
  """Executes a GraphQL query against the Open Targets API.

  This function sends a POST request to the Open Targets GraphQL API. It
  automatically injects pagination variables if the query supports it and
  pagination is not already specified. The response is checked for errors,
  truncated to a manageable size, and then written to the specified output file
  as JSON.

  Args:
    query: The GraphQL query string.
    variables: A dictionary of variables to pass with the query.
    output_file: The path to the file where the JSON output will be written.
    limit: The maximum number of items to keep in lists within the response
      (used by truncate_data). Defaults to 50.
    page_size: The size of each page for API pagination. If provided and the
      query supports "$page", pagination variables will be added. Defaults to
      200.
  """
  # Inject pagination into variables the query supports it and not already set
  if "page" not in variables and page_size and "$page" in query:
    variables["page"] = {"index": 0, "size": page_size}

  data = _CLIENT.fetch_json(
      BASE_URL,
      method="POST",
      json_body={"query": query, "variables": variables},
  )

  if "errors" in data:
    print(
        f"GraphQL Errors: {json.dumps(data['errors'], indent=2)}",
        file=sys.stderr,
    )
    sys.exit(1)

  truncated_data = truncate_data(data.get("data", {}), limit)
  with open(output_file, "w", encoding="utf-8") as f:
    f.write(json.dumps(truncated_data, indent=2))


def main():
  parser = argparse.ArgumentParser(
      description="Query Open Targets Platform GraphQL API"
  )
  parser.add_argument(
      "--limit",
      type=int,
      default=50,
      help="Limit list sizes in response (default: 50)",
  )
  parser.add_argument(
      "--page-size",
      type=int,
      default=200,
      help=(
          "API pagination size (default: 200). Set higher if results are"
          " truncated."
      ),
  )
  parser.add_argument(
      "--output",
      required=True,
      help="Path to write the JSON output file",
  )
  subparsers = parser.add_subparsers(dest="command", required=True)

  # get-gwas-studies
  p_gwas = subparsers.add_parser(
      "get-gwas-studies", help="Get GWAS studies for a specific disease EFO ID"
  )
  p_gwas.add_argument(
      "disease_id",
      help="Disease ID (EFO or MONDO, e.g., MONDO_0005011)",
  )

  # get-qtl-credible-sets
  p_qtl = subparsers.add_parser(
      "get-qtl-credible-sets",
      help="Get QTL credible sets for a specific variant",
  )
  p_qtl.add_argument("variant_id", help="Variant ID (e.g., 19_44908822_C_T)")

  # get-l2g
  p_l2g = subparsers.add_parser(
      "get-l2g",
      help=(
          "Get L2G prioritisation scores for a variant, optionally filtered by"
          " study"
      ),
  )
  p_l2g.add_argument(
      "variant_id",
      help="Lead variant ID (e.g., 1_113834946_A_G or chr1_113834946_A_G)",
  )
  p_l2g.add_argument(
      "--study-id",
      help="Optional study ID to filter results (e.g., GCST90204201)",
      default=None,
  )

  # get-target-druggability
  p_drug = subparsers.add_parser(
      "get-target-druggability",
      help="Get druggability and safety info for a target",
  )
  p_drug.add_argument(
      "ensembl_id", help="Target Ensembl ID (e.g., ENSG00000169083)"
  )

  # get-associated-targets
  p_assoc_tgt = subparsers.add_parser(
      "get-associated-targets",
      help="Get targets associated with a disease EFO ID",
  )
  p_assoc_tgt.add_argument(
      "disease_id",
      help="Disease ID (EFO or MONDO, e.g., MONDO_0005005)",
  )

  # get-associated-diseases
  p_assoc_dis = subparsers.add_parser(
      "get-associated-diseases",
      help="Get diseases associated with a target Ensembl ID",
  )
  p_assoc_dis.add_argument(
      "ensembl_id", help="Target Ensembl ID (e.g., ENSG00000127318)"
  )

  # get-study-credible-sets
  p_study_cs = subparsers.add_parser(
      "get-study-credible-sets",
      help="Get credible sets for a GWAS or other study by study ID",
  )
  p_study_cs.add_argument(
      "study_id",
      help="Study ID (e.g., FINNGEN_R12_RX_CROHN_2NDLINE or GCST90204201)",
  )
  # search-disease
  p_search_dis = subparsers.add_parser(
      "search-disease",
      help="Search for a disease by name to find its EFO ID and other metadata",
  )
  p_search_dis.add_argument(
      "query_string",
      help="Disease name or phenotype string to search for (e.g., 'asthma')",
  )

  # get-credible-sets-near-target
  p_near = subparsers.add_parser(
      "get-credible-sets-near-target",
      help="Get credible sets near target by filtering coordinates",
  )
  p_near.add_argument(
      "ensembl_id", help="Target Ensembl ID (e.g., ENSG00000156515)"
  )
  p_near.add_argument(
      "--window",
      type=int,
      default=500_000,
      help="Window size in bp around the target (default: 500000)",
  )

  # get-disease-drugs
  p_dis_drugs = subparsers.add_parser(
      "get-disease-drugs",
      help="Get drugs and clinical candidates for a disease",
  )
  p_dis_drugs.add_argument(
      "disease_id",
      help="Disease ID (EFO or MONDO, e.g., MONDO_0006823)",
  )
  p_dis_drugs.add_argument(
      "--min-stage",
      choices=CLINICAL_STAGES,
      help="Filter to drugs at or above this clinical stage for the disease",
  )

  # custom-query
  p_custom = subparsers.add_parser(
      "custom-query", help="Execute a custom GraphQL query"
  )
  p_custom.add_argument("query", help="GraphQL query string")
  p_custom.add_argument(
      "--variables", help="JSON string of variables", default="{}"
  )

  args = parser.parse_args()

  if args.command == "get-gwas-studies":
    query = """
        query getGWASStudies($efoId: String!) {
          studies(diseaseIds: [$efoId]) {
            count
            rows {
              id
              projectId
              traitFromSource
              publicationFirstAuthor
              publicationDate
              publicationJournal
              nSamples
              cohorts
              pubmedId
              ldPopulationStructure { ldPopulation relativeSampleSize }
            }
          }
        }
        """
    variables = {"efoId": args.disease_id}

  elif args.command == "get-qtl-credible-sets":
    query = """
        query getQTLCredibleSets($variantId: String!) {
          variant(variantId: $variantId) {
            id
            qtlCredibleSets: credibleSets(
              studyTypes: [scsqtl, sceqtl, scpqtl, sctuqtl, sqtl, eqtl, pqtl, tuqtl]
            ) {
              count
              rows {
                studyLocusId pValueMantissa pValueExponent beta finemappingMethod confidence
                variant { id chromosome }
                study {
                  id studyType condition
                  target { id approvedSymbol }
                  biosample { biosampleId biosampleName }
                }
                locus(variantIds: [$variantId]) {
                  rows { posteriorProbability }
                }
              }
            }
          }
        }
        """
    variables = {"variantId": normalize_variant_id(args.variant_id)}

  elif args.command == "get-l2g":
    variant_id = normalize_variant_id(args.variant_id)
    query = """
        query getL2G($variantIds: [String!], $studyIds: [String!], $page: Pagination) {
          credibleSets(variantIds: $variantIds, studyIds: $studyIds, page: $page) {
            count
            rows {
              studyLocusId
              confidence
              study { id studyType traitFromSource }
              variant { id }
              l2GPredictions {
                rows {
                  score
                  target { id approvedSymbol }
                }
              }
            }
          }
        }
        """
    variables = {"variantIds": [variant_id]}
    if args.study_id:
      variables["studyIds"] = [args.study_id]

  elif args.command == "get-target-druggability":
    query = """
        query getTargetAnnotation($ensemblId: String!) {
          target(ensemblId: $ensemblId) {
            id
            approvedSymbol
            tractability { modality label value }
            safetyLiabilities {
              event eventId
              biosamples { cellFormat cellLabel tissueLabel }
              effects { dosing direction }
              studies { name type description }
              datasource
            }
            geneticConstraint { constraintType exp obs score oe }
          }
        }
        """
    variables = {"ensemblId": args.ensembl_id}

  elif args.command == "get-associated-targets":
    query = """
        query getAssociatedTargets($efoId: String!) {
          disease(efoId: $efoId) {
            id
            name
            associatedTargets {
              count
              rows {
                target { id approvedSymbol }
                score
              }
            }
          }
        }
        """
    variables = {"efoId": args.disease_id}

  elif args.command == "get-associated-diseases":
    query = """
        query getAssociatedDiseases($ensemblId: String!) {
          target(ensemblId: $ensemblId) {
            id
            approvedSymbol
            associatedDiseases {
              count
              rows {
                disease { id name }
                datasourceScores { id score }
              }
            }
          }
        }
        """
    variables = {"ensemblId": args.ensembl_id}

  elif args.command == "get-study-credible-sets":
    query = """
        query getStudyCredibleSets($studyIds: [String!], $page: Pagination) {
          credibleSets(studyIds: $studyIds, page: $page) {
            count
            rows {
              studyLocusId
              confidence
              finemappingMethod
              pValueMantissa
              pValueExponent
              beta
              credibleSetIndex
              region
              variant { id chromosome position }
              study { id studyType traitFromSource }
            }
          }
        }
        """
    variables = {"studyIds": [args.study_id]}

  elif args.command == "search-disease":
    query = """
        query searchDisease($queryString: String!, $page: Pagination) {
          search(queryString: $queryString, entityNames: ["disease"], page: $page) {
            hits {
              id
              name
              description
              entity
            }
          }
        }
        """
    variables = {"queryString": args.query_string}

  elif args.command == "get-credible-sets-near-target":
    query = """
        query getTargetCredibleSets($ensemblId: String!, $page: Pagination) {
          target(ensemblId: $ensemblId) {
            approvedSymbol
            genomicLocation { chromosome start end }
            credibleSets(page: $page) {
              count
              rows {
                studyLocusId
                confidence
                region
                chromosome
                position
                variant { id chromosome position }
                study { id studyType traitFromSource }
              }
            }
          }
        }
        """
    variables = {"ensemblId": args.ensembl_id}
    if "page" not in variables and args.page_size and "$page" in query:
      variables["page"] = {"index": 0, "size": args.page_size}

    data = _CLIENT.fetch_json(
        BASE_URL,
        method="POST",
        json_body={"query": query, "variables": variables},
    )

    if "errors" in data:
      print(
          f"GraphQL Errors: {json.dumps(data['errors'], indent=2)}",
          file=sys.stderr,
      )
      sys.exit(1)

    target_data = data.get("data", {}).get("target", {})
    if not target_data:
      print("Error: Target not found", file=sys.stderr)
      sys.exit(1)

    loc = target_data.get("genomicLocation", {})
    target_chrom = loc.get("chromosome")
    t_start = loc.get("start")
    t_end = loc.get("end")

    if t_start is None or t_end is None:
      print(
          "Warning: Target location not found, cannot filter by region.",
          file=sys.stderr,
      )
      min_pos = 0
      max_pos = sys.maxsize
    else:
      window = args.window
      min_pos = max(0, t_start - window)
      max_pos = t_end + window

    cs_data = target_data.get("credibleSets", {})
    rows = cs_data.get("rows", [])

    filtered_rows = []
    for row in rows:
      v_pos = row.get("position") or row.get("variant", {}).get("position")
      v_chrom = row.get("chromosome") or row.get("variant", {}).get(
          "chromosome"
      )
      if (
          v_pos is not None
          and v_chrom == target_chrom
          and min_pos <= v_pos <= max_pos
      ):
        filtered_rows.append(row)

    # Update data structure
    cs_data["total_count"] = cs_data.get("count")
    cs_data["rows"] = filtered_rows
    cs_data["filtered_count"] = len(filtered_rows)

    truncated_data = truncate_data(data.get("data", {}), args.limit)
    with open(args.output, "w", encoding="utf-8") as f:
      f.write(json.dumps(truncated_data, indent=2))

    sys.exit(0)

  elif args.command == "get-disease-drugs":
    query = """
        query getDiseaseDrugs($efoId: String!) {
          disease(efoId: $efoId) {
            id
            name
            drugAndClinicalCandidates {
              count
              rows {
                maxClinicalStage
                drug {
                  id
                  name
                  drugType
                  maximumClinicalStage
                }
              }
            }
          }
        }
        """
    variables = {"efoId": args.disease_id}

    data = _CLIENT.fetch_json(
        BASE_URL,
        method="POST",
        json_body={"query": query, "variables": variables},
    )
    if "errors" in data:
      print(
          f"GraphQL Errors: {json.dumps(data['errors'], indent=2)}",
          file=sys.stderr,
      )
      sys.exit(1)

    disease_data = data.get("data", {}).get("disease")
    if disease_data and args.min_stage:
      candidates = disease_data.get("drugAndClinicalCandidates", {})
      rows = candidates.get("rows", [])
      filtered_rows = []
      min_stage_val = STAGE_ORDER.get(args.min_stage)
      for row in rows:
        stage = row.get("maxClinicalStage")
        stage_val = STAGE_ORDER.get(stage)
        if stage_val is not None and stage_val >= min_stage_val:
          filtered_rows.append(row)
      candidates["total_count"] = candidates.get("count")
      candidates["rows"] = filtered_rows
      candidates["filtered_count"] = len(filtered_rows)
      candidates["count"] = len(filtered_rows)

    truncated_data = truncate_data(data.get("data", {}), args.limit)
    with open(args.output, "w", encoding="utf-8") as f:
      f.write(json.dumps(truncated_data, indent=2))
    sys.exit(0)

  elif args.command == "custom-query":
    query = args.query
    try:
      variables = json.loads(args.variables)
    except json.JSONDecodeError:
      print("Error: --variables must be a valid JSON string", file=sys.stderr)
      sys.exit(1)
  else:
    available_commands = ", ".join(subparsers.choices.keys())
    print(
        f"Error: Unknown command: {args.command}. Available commands:"
        f" {available_commands}",
        file=sys.stderr,
    )
    sys.exit(1)

  execute_query(query, variables, args.output, args.limit, args.page_size)


if __name__ == "__main__":
  main()
