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

"""Command-line interface for querying NCBI dbSNP.

Queries via Variation Services and E-utilities.

Usage examples:
  uv run dbsnp_cli.py get-variant rs268 --output out.json
  uv run dbsnp_cli.py resolve-variant 8 19949407 T C --output out.json
  uv run dbsnp_cli.py search-region 7 117100000 117300000 --output out.json
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
#   "python-dotenv",
# ]
# ///

import argparse
import json
import os
import sys
import urllib.parse

import dotenv
from polite_http import http_client

_BASE_URL = "https://api.ncbi.nlm.nih.gov"

_GRCH38 = "GCF_000001405.40"
_GRCH37 = "GCF_000001405.25"
_ASSEMBLIES = [_GRCH38, _GRCH37]

_api_client = None


def get_api_client():
  """Returns the lazily initialized HttpClient."""
  global _api_client
  if _api_client is None:
    api_key = os.environ.get("NCBI_API_KEY")
    rate_limit = 10 if api_key else 3
    _api_client = http_client.HttpClient(
        _BASE_URL + "/",
        qps=rate_limit,
        retryable_status_codes=frozenset({429, 502, 503, 504}),
    )
  return _api_client


class RateLimitError(Exception):
  """Raised when the NCBI API returns HTTP 429."""


class ReferenceMismatchError(Exception):
  """Raised when the NCBI API reports a reference allele mismatch."""


def _fetch_json(url, allow_not_found=False, allow_ref_mismatch=False):
  """Fetches JSON from URL using HttpClient.

  Args:
    url (str): The URL to fetch.
    allow_not_found (bool): If True, returns None on HTTP 404.
    allow_ref_mismatch (bool): If True, raises ReferenceMismatchError on
      reference mismatch.

  Returns:
    dict: Decoded JSON object, or None if 404 and allow_not_found is True.

  Raises:
    RateLimitError: On HTTP 429.
  """
  api_key = os.environ.get("NCBI_API_KEY")
  if api_key:
    sep = "&" if "?" in url else "?"
    url = f"{url}{sep}api_key={urllib.parse.quote(api_key)}"

  try:
    return get_api_client().fetch_json(url)
  except http_client.HttpError as exc:
    if exc.status_code == 429:
      raise RateLimitError(
          "HTTP 429 Too Many Requests from NCBI.\n"
          "AGENT INSTRUCTION: Pause execution and inform the user that an NCBI "
          "API Key is required.  Direct them to "
          "https://ncbiinsights.ncbi.nlm.nih.gov/2017/11/02/"
          "new-api-keys-for-the-e-utilities/ and ask them to set the "
          "NCBI_API_KEY environment variable, then retry."
      ) from exc

    try:
      error_msg = exc.json().get("error", {}).get("message", "")
    except (ValueError, AttributeError, KeyError, TypeError):
      error_msg = str(exc)

    if exc.status_code == 404 and allow_not_found:
      return None

      # Check for reference mismatch (NCBI returns 500 for this)
    if (
        exc.status_code == 500
        and error_msg
        and "not equal to variant's asserted reference" in error_msg
    ):
      if allow_ref_mismatch:
        raise ReferenceMismatchError(error_msg) from exc
      _die(
          f"HTTP 500 from {url}: {error_msg}\n"
          "AGENT INSTRUCTION: This error indicates the reference allele does "
          "not match the sequence at this position. DO NOT RETRY the same "
          "query mechanically. Verify if the coordinates belong to a different "
          "assembly (e.g., GRCh38 vs GRCh37)."
      )

    _die(f"HTTP {exc.status_code} from {url}: {error_msg}")
  except Exception as exc:
    _die(f"Request failed for {url}: {exc}")
  _die(f"All retries failed for {url}")


def _die(message):
  """Print a JSON error object to stdout and exit with status 1."""
  print(json.dumps({"error": message}, indent=2))
  sys.exit(1)


def _write_output(data, output_path):
  """Write *data* as indented JSON to *output_path*."""
  try:
    with open(output_path, "w", encoding="utf-8") as fh:
      json.dump(data, fh, indent=2)
    print(f"Success. Data written to: {output_path}")
  except (OSError, TypeError) as exc:
    _die(f"Failed to write {output_path}: {exc}")


def _normalise_rsid(raw):
  """Normalises rsID by stripping leading 'rs'.

  Args:
    raw: The raw rsID string.

  Returns:
    Numeric rsID string.
  """
  text = raw.strip()
  text = text.lower().removeprefix("rs")
  if not text.isdigit():
    _die(
        f"Invalid rsID '{raw}'. Provide a numeric ID such as '268' or 'rs268'."
    )
  return text


def _abbreviate_refsnp(record, assembly):
  """Abbreviates a RefSNP record.

  Args:
    record: Raw RefSNP JSON record.
    assembly: Target assembly accession.

  Returns:
    Dict with selected fields.
  """
  snapshot = record.get("primary_snapshot_data", {})

  # --- Genomic placements for the target assembly ---
  placements = []
  for p in snapshot.get("placements_with_allele", []):
    if not p.get("is_ptlp"):
      continue
    traits = p.get("placement_annot", {}).get("seq_id_traits_by_assembly", [])
    for t in traits:
      if t.get("assembly_accession") == assembly:
        alleles = []
        for a in p.get("alleles", []):
          spdi = a.get("allele", {}).get("spdi", {})
          alleles.append({
              "deleted_sequence": spdi.get("deleted_sequence", ""),
              "inserted_sequence": spdi.get("inserted_sequence", ""),
              "position": spdi.get("position"),
              "is_variant": not a.get("hgvs", "").endswith("="),
          })
        placements.append({
            "seq_id": p.get("seq_id"),
            "alleles": alleles,
        })

  # --- Gene associations ---
  genes = set()
  for ann in snapshot.get("allele_annotations", []):
    for asm_ann in ann.get("assembly_annotation", []):
      for g in asm_ann.get("genes", []):
        name = g.get("locus")
        if name:
          genes.add(name)

  # --- Clinical significance from support ---
  clinical = []
  for ann in snapshot.get("allele_annotations", []):
    for clin in ann.get("clinical", []):
      for sig in clin.get("clinical_significances", []):
        clinical.append(sig)

  # --- Minor allele frequency ---
  maf_entries = []
  for ann in snapshot.get("allele_annotations", []):
    for freq in ann.get("frequency", []):
      study = freq.get("study_name", "")
      allele_count = freq.get("allele_count")
      total_count = freq.get("total_count")
      if allele_count is not None and total_count:
        maf_entries.append({
            "study": study,
            "allele_count": allele_count,
            "total_count": total_count,
        })

  return {
      "refsnp_id": record.get("refsnp_id"),
      "variant_type": snapshot.get("variant_type"),
      "genes": sorted(genes),
      "clinical_significances": clinical,
      "minor_allele_frequencies": maf_entries,
      "placements": placements,
  }


def cmd_get_variant(args):
  """Fetch the RefSNP record for a given rsID."""
  rsid = _normalise_rsid(args.rsid)
  url = f"{_BASE_URL}/variation/v0/refsnp/{rsid}"
  record = _fetch_json(url)

  if args.full:
    _write_output(record, args.output)
  else:
    _write_output(_abbreviate_refsnp(record, args.assembly), args.output)


def _build_spdi_string(spdi_dict):
  """Constructs SPDI string from dict.

  Args:
    spdi_dict: Dict with sequence, position, and allele info.

  Returns:
    Colon-separated SPDI string.
  """
  seq = spdi_dict.get("seq_id", "")
  pos = spdi_dict.get("position", "")
  deleted = spdi_dict.get("deleted_sequence", "")
  inserted = spdi_dict.get("inserted_sequence", "")
  return f"{seq}:{pos}:{deleted}:{inserted}"


def _spdi_list_to_rsids(spdi_list):
  """Resolves SPDI list to rsIDs.

  Args:
    spdi_list: List of SPDI dicts.

  Returns:
    Sorted list of rsID strings.
  """
  found = set()
  for item in spdi_list:
    spdi_val = _build_spdi_string(item)
    if not spdi_val or spdi_val == ":::":
      continue
    encoded = urllib.parse.quote(spdi_val)
    url = f"{_BASE_URL}/variation/v0/spdi/{encoded}/rsids"
    resp = _fetch_json(url, allow_not_found=True)
    if resp is None:
      continue
    for rid in resp.get("data", {}).get("rsids", []):
      found.add(str(rid))
  return sorted(found)


def _resolve_variant_for_assembly(chrom, pos, ref, alts, assembly):
  """Resolves coordinates using assembly.

  Args:
    chrom (str): Chromosome or sequence accession.
    pos (int): Position.
    ref (str): Reference allele.
    alts (str): Alternate alleles.
    assembly (str): Assembly accession.

  Returns:
    list[str]: List of rsID strings.
  """
  url = (
      f"{_BASE_URL}/variation/v0/"
      f"vcf/{chrom}/{pos}/{ref}/{alts}"
      f"/contextuals?assembly={assembly}"
  )
  try:
    resp = _fetch_json(url, allow_not_found=True, allow_ref_mismatch=True)
  except ReferenceMismatchError:
    return []
  if resp is None:
    return []
  spdi_list = resp.get("data", {}).get("spdis", [])
  if not spdi_list:
    return []
  return _spdi_list_to_rsids(spdi_list)


def cmd_resolve_variant(args):
  """Resolves VCF coordinates to rsIDs.

  Args:
    args (argparse.Namespace): Parse arguments.
  """
  # Build the ordered list of assemblies to try.
  assemblies = [args.assembly]
  for alt in _ASSEMBLIES:
    if alt != args.assembly:
      assemblies.append(alt)

  used_assembly = args.assembly
  rsids = []
  for asm in assemblies:
    rsids = _resolve_variant_for_assembly(
        args.chrom, args.pos, args.ref, args.alts, asm
    )
    if rsids:
      used_assembly = asm
      break

  if not rsids:
    _die(
        "No rsIDs found for the given VCF coordinates on any "
        "supported assembly (GRCh38, GRCh37). Verify that you "
        "typed the coordinates correctly and that the variant "
        "exists in dbSNP."
    )

  result = {"rsids": rsids}
  if used_assembly != args.assembly:
    result["note"] = (
        "No rsIDs found on the requested assembly "
        f"({args.assembly}); result obtained via "
        f"fallback assembly ({used_assembly})."
    )
  _write_output(result, args.output)


def cmd_resolve_rsid(args):
  """Extract genomic coordinates from an rsID."""
  rsid = _normalise_rsid(args.rsid)
  url = f"{_BASE_URL}/variation/v0/refsnp/{rsid}"
  record = _fetch_json(url)

  snapshot = record.get("primary_snapshot_data")
  if not snapshot:
    _die(f"No snapshot data found for rs{rsid}.")

  results = []
  for p in snapshot.get("placements_with_allele", []):
    if not p.get("is_ptlp"):
      continue
    traits = p.get("placement_annot", {}).get("seq_id_traits_by_assembly", [])
    for t in traits:
      if t.get("assembly_accession") == args.assembly:
        results.append({
            "seq_id": p.get("seq_id"),
            "alleles": p.get("alleles"),
        })

  _write_output(
      {"rsid": rsid, "assembly": args.assembly, "placements": results},
      args.output,
  )


def _resolve_hgvs_for_assembly(hgvs, assembly):
  """Resolves HGVS using assembly.

  Args:
    hgvs (str): HGVS string.
    assembly (str): Assembly accession.

  Returns:
    list[str]: List of rsID strings.
  """
  encoded = urllib.parse.quote(hgvs)
  url = (
      f"{_BASE_URL}/variation/v0/hgvs/{encoded}/contextuals?assembly={assembly}"
  )
  try:
    resp = _fetch_json(url, allow_not_found=True, allow_ref_mismatch=True)
  except ReferenceMismatchError:
    return []
  if resp is None:
    return []
  spdi_list = resp.get("data", {}).get("spdis", [])
  if not spdi_list:
    return []
  return _spdi_list_to_rsids(spdi_list)


def cmd_resolve_hgvs(args):
  """Resolves HGVS string to rsIDs.

  Args:
    args (argparse.Namespace): Parse arguments.
  """
  assemblies = [args.assembly]
  for alt in _ASSEMBLIES:
    if alt != args.assembly:
      assemblies.append(alt)

  used_assembly = args.assembly
  rsids = []
  for asm in assemblies:
    rsids = _resolve_hgvs_for_assembly(args.hgvs, asm)
    if rsids:
      used_assembly = asm
      break

  if not rsids:
    _die(
        "No rsIDs found for the given HGVS expression on any "
        "supported assembly (GRCh38, GRCh37). Verify that you "
        "typed the HGVS string correctly and that the variant "
        "exists in dbSNP."
    )

  result = {"rsids": rsids}
  if used_assembly != args.assembly:
    result["note"] = (
        "No rsIDs found on the requested assembly "
        f"({args.assembly}); result obtained via "
        f"fallback assembly ({used_assembly})."
    )
  _write_output(result, args.output)


_REGION_RETMAX_CEILING = 5000


def cmd_search_region(args):
  """Locate all rsIDs within a bounded chromosomal region."""
  query = f"{args.chrom}[CHR] AND {args.start}:{args.end}[CPOS]"
  encoded_query = urllib.parse.quote(query)
  page_size = min(args.retmax, 500)  # per-page batch size
  collected = []
  total_available = None
  retstart = 0

  while True:
    url = (
        f"{_BASE_URL}/entrez/eutils/esearch.fcgi?db=snp&retmode=json"
        f"&term={encoded_query}"
        f"&retmax={page_size}&retstart={retstart}"
    )
    resp = _fetch_json(url)
    result = resp.get("esearchresult", {})

    if total_available is None:
      total_available = int(result.get("count", 0))

    batch = result.get("idlist", [])
    collected.extend(batch)

    # Stop if we have enough or there are no more pages.
    if (
        len(collected) >= args.retmax
        or len(collected) >= total_available
        or not batch
    ):
      break
    retstart += page_size

  collected = collected[: args.retmax]

  output = {
      "rsids": collected,
      "returned": len(collected),
      "total_available": total_available,
  }
  if total_available > len(collected):
    output["truncated"] = True
    output["note"] = (
        f"Only {len(collected)} of {total_available} variants "
        "returned.  Increase --retmax to retrieve more."
    )

  _write_output(output, args.output)


def main():
  dotenv.load_dotenv(os.path.expanduser("~/.env"))
  parser = argparse.ArgumentParser(
      description="Query NCBI dbSNP via Variation Services and E-utilities."
  )
  subs = parser.add_subparsers(dest="command", required=True)

  # -- get-variant --------------------------------------------------------
  p_get = subs.add_parser(
      "get-variant",
      help="Retrieve the RefSNP record for a given rsID.",
  )
  p_get.add_argument(
      "rsid",
      help="RefSNP identifier (e.g. 268 or rs268).",
  )
  p_get.add_argument(
      "--assembly",
      default="GCF_000001405.40",
      help="RefSeq assembly accession (default: GCF_000001405.40 = GRCh38).",
  )
  p_get.add_argument(
      "--full",
      action="store_true",
      help=(
          "Return the complete raw RefSNP JSON payload.  WARNING: "
          "the full payload is typically 50-500 KB and can exceed 1 MB for "
          "clinically significant variants.  Only use this flag when you "
          "need fields not present in the abbreviated output, for example: "
          "submission history, full HGVS nomenclature across all "
          "transcripts, or detailed population-level allele frequency "
          "breakdowns by sub-population."
      ),
  )
  p_get.add_argument("--output", required=True, help="Output JSON file path.")
  p_get.set_defaults(func=cmd_get_variant)

  # -- resolve-variant ----------------------------------------------------
  p_vcf = subs.add_parser(
      "resolve-variant",
      help="Find rsID(s) from VCF-style coordinates.",
  )
  p_vcf.add_argument("chrom", help="Chromosome or sequence accession.")
  p_vcf.add_argument("pos", type=int, help="1-based genomic position.")
  p_vcf.add_argument("ref", help="Reference allele.")
  p_vcf.add_argument("alts", help="Alternate allele(s), comma-separated.")
  p_vcf.add_argument(
      "--assembly",
      default="GCF_000001405.40",
      help="RefSeq assembly accession (default: GCF_000001405.40).",
  )
  p_vcf.add_argument("--output", required=True, help="Output JSON file path.")
  p_vcf.set_defaults(func=cmd_resolve_variant)

  # -- resolve-rsid -------------------------------------------------------
  p_rsid = subs.add_parser(
      "resolve-rsid",
      help="Get genomic coordinates for an rsID.",
  )
  p_rsid.add_argument("rsid", help="RefSNP identifier (e.g. 268 or rs268).")
  p_rsid.add_argument(
      "--assembly",
      default="GCF_000001405.40",
      help="RefSeq assembly accession (default: GCF_000001405.40).",
  )
  p_rsid.add_argument("--output", required=True, help="Output JSON file path.")
  p_rsid.set_defaults(func=cmd_resolve_rsid)

  # -- resolve-hgvs -------------------------------------------------------
  p_hgvs = subs.add_parser(
      "resolve-hgvs",
      help="Find rsID(s) from an HGVS expression.",
  )
  p_hgvs.add_argument(
      "hgvs", help="HGVS string (e.g. NC_000008.11:g.19962213del)."
  )
  p_hgvs.add_argument(
      "--assembly",
      default="GCF_000001405.40",
      help="RefSeq assembly accession (default: GCF_000001405.40).",
  )
  p_hgvs.add_argument("--output", required=True, help="Output JSON file path.")
  p_hgvs.set_defaults(func=cmd_resolve_hgvs)

  # -- search-region ------------------------------------------------------
  p_region = subs.add_parser(
      "search-region",
      help="Find rsIDs within a chromosomal region.",
  )
  p_region.add_argument("chrom", help="Chromosome (e.g. 7).")
  p_region.add_argument("start", type=int, help="Start position.")
  p_region.add_argument("end", type=int, help="End position.")
  p_region.add_argument(
      "--retmax",
      type=int,
      default=500,
      help=(
          "Maximum number of rsIDs to return (default: 500, "
          f"ceiling: {_REGION_RETMAX_CEILING})."
      ),
  )
  p_region.add_argument(
      "--output", required=True, help="Output JSON file path."
  )
  p_region.set_defaults(func=cmd_search_region)

  args = parser.parse_args()
  # Clamp retmax for search-region.
  if hasattr(args, "retmax") and args.retmax > _REGION_RETMAX_CEILING:
    args.retmax = _REGION_RETMAX_CEILING

  args.func(args)


if __name__ == "__main__":
  main()
