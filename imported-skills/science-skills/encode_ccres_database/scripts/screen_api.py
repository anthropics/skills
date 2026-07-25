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

"""A command-line tool to query the ENCODE SCREEN GraphQL API.

This script provides subcommands to interact with the SCREEN API, allowing users
to search for cCREs, get details, find nearby/linked genes, query biosamples,
orthologs, ENTEx data, and GWAS information.
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

from polite_http import http_client

API_URL = "https://factorbook.api.wenglab.org/graphql"
_CLIENT = http_client.HttpClient(
    API_URL,
    qps=10,
    default_headers={
        "Origin": "https://screen-v2.wenglab.org",
        "Referer": "https://screen-v2.wenglab.org/",
    },
)


def run_query(query, variables, assembly=None, requires_assembly=True):
  """Execute a GraphQL query with automatic assembly fallback.

  Tries the specified assembly first. If none is given and
  requires_assembly is True, falls back through grch38 then
  mm10 until a non-empty result is returned.

  Args:
      query: GraphQL query string.
      variables: Dict of query variables (modified in-place with the assembly
        key).
      assembly: Explicit assembly to use, or None for automatic fallback.
      requires_assembly: Whether the query needs an assembly variable. Set to
        False for assembly-free queries.

  Returns:
      Tuple of (response_dict, assembly_used, None) on
      success, or (None, None, error_string) on failure.
  """
  assemblies_to_try = (
      [assembly]
      if assembly
      else (["grch38", "mm10"] if requires_assembly else [None])
  )

  last_err = None
  for asm in assemblies_to_try:
    if asm:
      variables["assembly"] = asm

    try:
      result = _CLIENT.fetch_json(
          API_URL,
          method="POST",
          json_body={"query": query, "variables": variables},
      )
    except (http_client.HttpError, json.JSONDecodeError) as e:
      last_err = str(e)
      continue
    if "errors" in result:
      last_err = str(result["errors"])
      continue

    data = result.get("data", {})

    # Check if data is entirely empty or null
    if any(data.values()):
      return result, asm, None
    else:
      last_err = "Empty results returned."

  return None, None, last_err


def write_output(res, asm, output_path):
  """Write the full API response to the specified JSON file.

  Args:
      res: Parsed JSON response dict from the API.
      asm: Assembly string that was used, or None.
      output_path: File path to write the JSON output to.
  """
  try:
    with open(output_path, "w", encoding="utf-8") as f:
      json.dump(res, f, indent=2)
  except (OSError, TypeError) as exc:
    print(f"Error: Failed to write {output_path}: {exc}", file=sys.stderr)
    sys.exit(1)

  print(f"Success. Data written to: {output_path}")
  if asm:
    print(f"Assembly used: {asm}")


def cmd_search(args):
  """Search cCREs by genomic coordinates, accessions, or signal scores."""
  query = """
    query Search(
        $assembly: String!,
        $coords: [GenomicRangeInput!],
        $accessions: [String!],
        $ctcf_start: Float,
        $ctcf_end: Float,
        $cellType: String
    ) {
        cCRESCREENSearch(
            assembly: $assembly,
            coordinates: $coords,
            accessions: $accessions,
            rank_ctcf_start: $ctcf_start,
            rank_ctcf_end: $ctcf_end,
            cellType: $cellType
        ) {
            chrom start len pct
            ctcf_zscore dnase_zscore atac_zscore
            enhancer_zscore promoter_zscore
            info { accession }
            ctspecific {
                ct ctcf_zscore dnase_zscore h3k4me3_zscore h3k27ac_zscore
                atac_zscore
            }
        }
    }
    """
  coords = None
  if args.chromosome and args.start and args.end:
    coords = [
        {"chromosome": args.chromosome, "start": args.start, "end": args.end}
    ]

  variables = {}
  if coords:
    variables["coords"] = coords
  if args.accessions:
    variables["accessions"] = args.accessions
  if args.ctcf_start is not None:
    variables["ctcf_start"] = args.ctcf_start
  if args.ctcf_end is not None:
    variables["ctcf_end"] = args.ctcf_end
  if args.cellType:
    variables["cellType"] = args.cellType

  res, asm, err = run_query(query, variables, args.assembly)
  if err:
    print(f"Error: {err}", file=sys.stderr)
    sys.exit(1)

  write_output(res, asm, args.output)


def cmd_nearby(args):
  """Retrieve nearest genes for one or more cCRE accessions."""
  query = """
    query Nearby($assembly: String!, $accessions: [String!]) {
        cCRESCREENSearch(assembly: $assembly, accessions: $accessions) {
            chrom start len pct
            info { accession }
            nearestgenes { gene distance }
        }
    }
    """
  variables = {"accessions": args.accessions}
  res, asm, err = run_query(query, variables, args.assembly)
  if err:
    print(f"Error: {err}", file=sys.stderr)
    sys.exit(1)

  write_output(res, asm, args.output)


def cmd_biosamples(args):
  """List available biosample metadata for an assembly."""
  query = """
    query Biosamples($assembly: String!) {
        ccREBiosampleQuery(assembly: $assembly) {
            biosamples {
                name ontology lifeStage sampleType displayname
                dnase: experimentAccession(assay: "DNase")
                h3k4me3: experimentAccession(assay: "H3K4me3")
                h3k27ac: experimentAccession(assay: "H3K27ac")
                ctcf: experimentAccession(assay: "CTCF")
            }
        }
    }
    """
  res, asm, err = run_query(query, {}, args.assembly)
  if err:
    print(f"Error: {err}", file=sys.stderr)
    sys.exit(1)

  # Enrich results with 'is_type_a' flag (all 4 core assays present)
  if res and "data" in res and "ccREBiosampleQuery" in res["data"]:
    for b in res["data"]["ccREBiosampleQuery"]["biosamples"]:
      b["is_type_a"] = all(
          [b.get("dnase"), b.get("h3k4me3"), b.get("h3k27ac"), b.get("ctcf")]
      )

  write_output(res, asm, args.output)


def cmd_details(args):
  """Get detailed info and biosample z-scores for a single cCRE."""
  query = """
    query Details($assembly: String!, $accession: [String!]!) {
        cCREQuery(assembly: $assembly, accession: $accession) {
            accession group
            dnase: maxZ(assay: "DNase")
            h3k4me3: maxZ(assay: "H3K4me3")
            h3k27ac: maxZ(assay: "H3K27ac")
            ctcf: maxZ(assay: "CTCF")
            atac: maxZ(assay: "ATAC")
            coordinates { chromosome start end }
        }
        ccREBiosampleQuery(assembly: $assembly) {
            biosamples {
                sampleType name ontology displayname
                dnase_acc: experimentAccession(assay: "DNase")
                h3k4me3_acc: experimentAccession(assay: "H3K4me3")
                h3k27ac_acc: experimentAccession(assay: "H3K27ac")
                ctcf_acc: experimentAccession(assay: "CTCF")
                cCREZScores(accession: $accession) {
                    score assay experiment_accession
                }
            }
        }
    }
    """
  res, asm, err = run_query(
      query, {"accession": [args.accession]}, args.assembly
  )
  if err:
    print(f"Error: {err}", file=sys.stderr)
    sys.exit(1)

  # Enrich results with 'is_type_a' flag (all 4 core assays present)
  if res and "data" in res and "ccREBiosampleQuery" in res["data"]:
    for b in res["data"]["ccREBiosampleQuery"]["biosamples"]:
      b["is_type_a"] = all([
          b.get("dnase_acc"),
          b.get("h3k4me3_acc"),
          b.get("h3k27ac_acc"),
          b.get("ctcf_acc"),
      ])

  write_output(res, asm, args.output)


def cmd_orthologs(args):
  """Find orthologous cCREs in another genome assembly."""
  query = """
    query Orthologs($assembly: String!, $accession: String!) {
        orthologQuery(assembly: $assembly, accession: $accession) {
            assembly accession
            ortholog { stop start chromosome accession }
        }
    }
    """
  res, asm, err = run_query(query, {"accession": args.accession}, args.assembly)
  if err:
    print(f"Error: {err}", file=sys.stderr)
    sys.exit(1)
  write_output(res, asm, args.output)


def cmd_linked(args):
  """Retrieve genes linked to one or more cCREs via eQTLs or other methods."""
  query = """
    query Linked($assembly: String!, $accessions: [String]!) {
        linkedGenesQuery(assembly: $assembly, accession: $accessions) {
            accession gene geneid genetype method effectsize assay celltype
            tissue score displayname
        }
    }
    """
  res, asm, err = run_query(
      query, {"accessions": args.accessions}, args.assembly
  )
  if err:
    print(f"Error: {err}", file=sys.stderr)
    sys.exit(1)
  write_output(res, asm, args.output)


def cmd_entex(args):
  """Query ENTEx allelic imbalance data by accession or region."""
  if args.region:
    chrom, start, end = args.region.split(":")
    start, end = int(start), int(end)
    query = """
        query EntexRegion($coords: GenomicRangeInput!) {
            entexActiveAnnotationsQuery(coordinates: $coords) {
                tissue assay_score
            }
        }
        """
    variables = {"coords": {"chromosome": chrom, "start": start, "end": end}}
    res, asm, err = run_query(query, variables, requires_assembly=False)
  else:
    query = """
        query Entex($accession: String!) {
            entexQuery(accession: $accession) {
                assay accession hap1_count hap2_count hap1_allele_ratio
                p_betabinom tissue donor imbalance_significance
            }
        }
        """
    variables = {"accession": args.accession}
    res, asm, err = run_query(query, variables, requires_assembly=False)

  if err:
    print(f"Error: {err}", file=sys.stderr)
    sys.exit(1)
  write_output(res, asm, args.output)


def cmd_gene_expression(args):
  """Retrieve gene expression (TPM and FPKM) across biosamples for a named gene.

  TPM (transcripts per million) is the preferred quantification metric;
  FPKM (fragments per kilobase per million) is also included for
  completeness.

  This is a three-step process using the factorbook GraphQL API:
    1. Resolve the gene name to an Ensembl gene ID via `gene`.
    2. Fetch per-experiment TPM and FPKM data via `gene_quantification`.
    3. Enrich with biosample/tissue metadata via `gene_dataset`.

  Args:
      args: An argparse.Namespace object with the following attributes:
          gene: The gene symbol (e.g., OR51B4).
          assembly: The genome assembly (e.g., grch38).
          output: The path to the output JSON file.
  """
  # Step 1: Resolve gene name -> Ensembl ID
  gene_query = """
    query GeneID($assembly: String!, $name: [String!]) {
        gene(assembly: $assembly, name: $name) {
            name
            id
            coordinates {
                start chromosome end
            }
        }
    }
    """
  res, asm, err = run_query(gene_query, {"name": [args.gene]}, args.assembly)
  if err:
    print(f"Error resolving gene name: {err}", file=sys.stderr)
    sys.exit(1)

  genes = res.get("data", {}).get("gene", [])
  if not genes:
    print(
        f"Error: Gene '{args.gene}' not found in assembly.",
        file=sys.stderr,
    )
    sys.exit(1)

  gene_info = genes[0]
  if len(genes) > 1:
    other_ids = ", ".join(g["id"] for g in genes[1:])
    print(
        f"Warning: Multiple genes matched '{args.gene}'. "
        f"Using {gene_info['id']}, ignoring: {other_ids}",
        file=sys.stderr,
    )
  gene_id = gene_info["id"]
  # Use the stable ID prefix without version (e.g. ENSG00000183251)
  gene_id_prefix = gene_id.split(".")[0]

  print(f"Resolved gene '{args.gene}' to ID: {gene_id}")

  # Step 2: Fetch per-experiment TPM via gene_quantification
  quant_query = """
    query GeneQuant($assembly: String!, $gene_id_prefix: [String]) {
        gene_quantification(
            assembly: $assembly,
            gene_id_prefix: $gene_id_prefix,
            sortByTpm: true
        ) {
            experiment_accession
            file_accession
            tpm
            fpkm
        }
    }
    """
  # Pin to the assembly that resolved the gene in Step 1. The Ensembl ID is
  # assembly-specific, so falling back to a different assembly would be wrong.
  res2, _, err2 = run_query(
      quant_query,
      {"gene_id_prefix": [gene_id_prefix]},
      assembly=asm,
  )
  if err2:
    print(f"Error fetching expression data: {err2}", file=sys.stderr)
    sys.exit(1)

  quants = res2.get("data", {}).get("gene_quantification", [])
  if not quants:
    print(f"No expression data found for gene '{args.gene}'.", file=sys.stderr)
    sys.exit(1)

  # Step 3: Enrich with biosample metadata via gene_dataset.
  # Chunk accessions to avoid 413 Payload Too Large on the GraphQL endpoint.
  exp_accessions = list({q["experiment_accession"] for q in quants})

  ds_query = """
    query DatasetMeta($accessions: [String]) {
        gene_dataset(accession: $accessions) {
            accession
            biosample
            tissue
            biosample_type
            cell_compartment
            assay_term_name
        }
    }
    """
  ds_lookup = {}
  chunk_size = 100
  for i in range(0, len(exp_accessions), chunk_size):
    chunk = exp_accessions[i : i + chunk_size]
    res3, _, err3 = run_query(
        ds_query,
        {"accessions": chunk},
        requires_assembly=False,
    )
    if not err3:
      for ds in res3.get("data", {}).get("gene_dataset", []):
        ds_lookup[ds["accession"]] = ds

  # Merge quantification + dataset metadata
  output = {
      "data": {
          "gene": gene_info,
          "gene_id_prefix": gene_id_prefix,
          "assembly": asm,
          "expression": [],
      }
  }
  for q in quants:
    ds = ds_lookup.get(q["experiment_accession"], {})
    output["data"]["expression"].append({
        "biosample": ds.get("biosample"),
        "tissue": ds.get("tissue"),
        "cell_compartment": ds.get("cell_compartment"),
        "biosample_type": ds.get("biosample_type"),
        "assay_term_name": ds.get("assay_term_name"),
        "experiment_accession": q["experiment_accession"],
        "file_accession": q["file_accession"],
        "tpm": q["tpm"],
        "fpkm": q["fpkm"],
    })

  print(
      f"Found expression data in {len(output['data']['expression'])} "
      "biosample entries."
  )
  write_output(output, asm, args.output)


def cmd_gwas(args):
  """Query GWAS studies, their SNPs, or cell-type enrichment."""
  if args.type == "studies":
    query = """
        query GWASStudies {
            getAllGwasStudies {
                study totalldblocks author pubmedid studyname
            }
        }
        """
    res, asm, err = run_query(query, {}, requires_assembly=False)
  elif args.type == "snps":
    query = """
        query GWASSNPs($study: [String!]!) {
            getSNPsforGWASStudies(study: $study) {
                snpid ldblock rsquare chromosome stop start
            }
        }
        """
    res, asm, err = run_query(
        query, {"study": [args.study]}, requires_assembly=False
    )
  else:
    query = """
        query GWASEnrichment($study: String!) {
            getGWASCtEnrichmentQuery(study: $study) {
                celltype accession fc fdr pvalue
            }
        }
        """
    res, asm, err = run_query(
        query, {"study": args.study}, requires_assembly=False
    )

  if err:
    print(f"Error: {err}", file=sys.stderr)
    sys.exit(1)
  write_output(res, asm, args.output)


def main():
  """Parse CLI arguments and dispatch to the appropriate subcommand."""
  parser = argparse.ArgumentParser(
      description="Query the ENCODE Registry of cCREs via SCREEN GraphQL API."
  )
  subparsers = parser.add_subparsers(dest="command", required=True)

  def add_common(p):
    """Add --assembly and --output arguments shared by most subcommands."""
    p.add_argument(
        "--assembly",
        help=(
            "Assembly (e.g., grch38, mm10). Default fallback "
            "tries grch38 then mm10."
        ),
    )
    p.add_argument(
        "--output",
        default="/tmp/encode_output.json",
        help="Output JSON file path (default: /tmp/encode_output.json).",
    )

  p_search = subparsers.add_parser(
      "search", help="Search cCREs by coordinates, accessions, or signals."
  )
  add_common(p_search)
  p_search.add_argument("--chromosome", help="e.g., chr11")
  p_search.add_argument("--start", type=int, help="Start coordinate")
  p_search.add_argument("--end", type=int, help="End coordinate")
  p_search.add_argument(
      "--accessions", nargs="+", help="One or more accessions"
  )
  p_search.add_argument(
      "--ctcf-start", type=float, help="CTCF max z-score range start"
  )
  p_search.add_argument(
      "--ctcf-end", type=float, help="CTCF max z-score range end"
  )
  p_search.add_argument(
      "--cellType",
      help="Biosample-specific epigenetic signal (e.g., GM12878_ENCDO000AAK)",
  )
  p_search.set_defaults(func=cmd_search)

  p_nearby = subparsers.add_parser(
      "nearby-genes", help="Get nearby genes for cCRE accessions."
  )
  add_common(p_nearby)
  p_nearby.add_argument("accessions", nargs="+", help="One or more accessions")
  p_nearby.set_defaults(func=cmd_nearby)

  p_biosamples = subparsers.add_parser(
      "biosamples", help="Get biosample metadata for an assembly."
  )
  add_common(p_biosamples)
  p_biosamples.set_defaults(func=cmd_biosamples)

  p_details = subparsers.add_parser(
      "details", help="Get cCRE details and biosample-specific signals."
  )
  add_common(p_details)
  p_details.add_argument(
      "accession", help="cCRE accession (e.g., EH38E2941922)"
  )
  p_details.set_defaults(func=cmd_details)

  p_orthologs = subparsers.add_parser(
      "orthologs", help="Get orthologous cCREs in another assembly."
  )
  add_common(p_orthologs)
  p_orthologs.add_argument("accession", help="cCRE accession")
  p_orthologs.set_defaults(func=cmd_orthologs)

  p_linked = subparsers.add_parser(
      "linked-genes", help="Get linked genes for a cCRE."
  )
  add_common(p_linked)
  p_linked.add_argument(
      "accessions", nargs="+", help="One or more cCRE accessions"
  )
  p_linked.set_defaults(func=cmd_linked)

  p_entex = subparsers.add_parser(
      "entex", help="Get ENTEx data for a cCRE or genomic region."
  )
  g = p_entex.add_mutually_exclusive_group(required=True)
  g.add_argument("--accession", help="cCRE accession")
  g.add_argument("--region", help="Genomic region format chr:start:end")
  p_entex.add_argument(
      "--output",
      default="/tmp/encode_output.json",
      help="Output JSON file path (default: /tmp/encode_output.json).",
  )
  p_entex.set_defaults(func=cmd_entex)

  p_gene_expr = subparsers.add_parser(
      "gene-expression",
      help="Get gene expression (TPM and FPKM) across biosamples for a gene.",
  )
  add_common(p_gene_expr)
  p_gene_expr.add_argument(
      "gene", help="Gene symbol (e.g., OR51B4, GAPDH, TP53)"
  )
  p_gene_expr.set_defaults(func=cmd_gene_expression)

  p_gwas = subparsers.add_parser(
      "gwas", help="Query GWAS studies, SNPs, or cell-type enrichment."
  )
  p_gwas.add_argument(
      "type",
      choices=["studies", "snps", "enrichment"],
      help="Type of GWAS query",
  )
  p_gwas.add_argument(
      "--study", help="Study name (required for snps and enrichment)"
  )
  p_gwas.add_argument(
      "--output",
      default="/tmp/encode_output.json",
      help="Output JSON file path (default: /tmp/encode_output.json).",
  )
  p_gwas.set_defaults(func=cmd_gwas)

  args = parser.parse_args()
  if (
      args.command == "gwas"
      and args.type in ["snps", "enrichment"]
      and not args.study
  ):
    parser.error("--study is required for GWAS snps and enrichment queries.")

  args.func(args)


if __name__ == "__main__":
  main()
