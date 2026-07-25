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

"""A command-line tool to query the Ensembl REST API.

This script provides subcommands for gene/transcript/protein lookup, ID
resolution and cross-referencing, sequence retrieval, and variant effect
prediction (VEP).  All rich data is saved to a temporary JSON file; a concise
human-readable summary is printed to stdout.
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
# ]
# ///

import argparse
import json
import os
import sys
import tempfile

from polite_http import http_client

BASE_URL = "https://rest.ensembl.org"
GRCH37_URL = "https://grch37.rest.ensembl.org"

VEP_PLUGINS = (
    "?AlphaMissense=1&Conservation=1&DosageSensitivity=1&IntAct=1"
    "&MaveDB=1&OpenTargets=1&LoF=loftee&NMD=1&UTRAnnotator=1"
    "&mutfunc=1&LOEUF=1"
)

_CLIENT_REGULAR = http_client.HttpClient(BASE_URL, qps=15)
_CLIENT_GRCH37 = http_client.HttpClient(GRCH37_URL, qps=15)


def _get_client(assembly=None):
  """Return the correct client for the requested assembly."""
  if assembly and assembly.upper() == "GRCH37":
    print("[*] Using GRCh37 assembly.")
    return _CLIENT_GRCH37
  return _CLIENT_REGULAR


def _get_species(args):
  """Return the species, defaulting to 'human' if not specified."""
  species = args.species
  if not species:
    species = "human"
    print("[*] No species specified. Defaulting to 'human'.")
  return species


def _save_json(data, prefix, output_path=None):
  """Write *data* as pretty-printed JSON to a temp file and return the path."""
  if output_path:
    path = output_path
    with open(path, "w") as fh:
      json.dump(data, fh, indent=2)
  else:
    fd, path = tempfile.mkstemp(
        prefix=f"ensembl_{prefix}_", suffix=".json", text=True
    )
    with os.fdopen(fd, "w") as fh:
      json.dump(data, fh, indent=2)
  return path


def _try_fallback(url: str, query: str, client=None) -> list[dict[str, str]]:
  """Tries to resolve gene symbol via cross-references if initial lookup fails.

  Args:
    url: The URL for the cross-reference lookup.
    query: The original gene symbol query.
    client: The HttpClient to use. Defaults to _CLIENT_REGULAR.

  Returns:
    A list of dictionaries, where each dictionary contains gene information
    resolved from the cross-reference.
  """
  if client is None:
    client = _CLIENT_REGULAR
  fallback_data = client.fetch_json(url)
  if not fallback_data:
    return []
  matches = []
  for item in fallback_data:
    if item.get("type") != "gene":
      continue
    ens_id = item.get("id")
    url_lookup = f"/lookup/id/{ens_id}"
    try:
      gene_data = client.fetch_json(url_lookup)
      matches.append(gene_data)
    except http_client.HttpError:
      print(f"[!] Failed to fetch details for resolved ID {ens_id}")
      matches.append({
          "id": ens_id,
          "biotype": "N/A",
          "seq_region_name": "?",
          "start": "?",
          "end": "?",
          "strand": "?",
      })
  if matches:
    print(f"[*] Resolved via synonym '{query}' to {len(matches)} gene(s):")
  return matches


def cmd_resolve_gene(args):
  """Resolve a symbol / alias / RefSeq ID to one or more ENSG IDs."""
  query = args.query
  species = _get_species(args)
  client = _get_client(args.assembly)

  url = f"/lookup/symbol/{species}/{query}?expand=0"
  try:
    data = client.fetch_json(url)
    matches = data if isinstance(data, list) else [data]
    print(f"[*] Symbol '{query}' resolved ({len(matches)} match(es)):")
  except http_client.HttpError as e:
    if e.status_code == 404 or (
        e.status_code == 400
        and e.body
        and b"No valid lookup found for symbol" in e.body
    ):
      print(f"[*] Symbol '{query}' not found. Trying synonym resolution...")
      url_fallback = f"/xrefs/symbol/{species}/{query}"
      try:
        data = _try_fallback(url_fallback, query, client=client)
      except http_client.HttpError as exc:
        raise e from exc
      if not data:
        raise e
      matches = data
    else:
      raise e

  for m in matches:
    eid = m.get("id", "N/A")
    biotype = m.get("biotype", "N/A")
    chrom = m.get("seq_region_name", "?")
    start = m.get("start", "?")
    end = m.get("end", "?")
    strand = m.get("strand", "?")
    print(
        f"    ENSG: {eid}  |  biotype: {biotype}  "
        f"|  location: chr{chrom}:{start}-{end} (strand {strand})"
    )

  path = _save_json(data, f"resolve_{query}", output_path=args.output)
  print(f"[*] Full JSON saved to {path}")


def cmd_map_id(args):
  """Cross-reference an Ensembl ID to an external database."""
  eid = args.id
  ext_db = args.external_db
  client = _get_client(args.assembly)

  params = f"?external_db={ext_db}" if ext_db else ""
  url = f"/xrefs/id/{eid}{params}"
  data = client.fetch_json(url)

  if not data:
    print(f"[*] No cross-references found for {eid}.")
  else:
    db_label = f" in {ext_db}" if ext_db else ""
    print(f"[*] {len(data)} cross-reference(s) for {eid}{db_label}:")
    for entry in data[:10]:
      primary = entry.get("primary_id", "N/A")
      display = entry.get("display_id", "N/A")
      dbname = entry.get("db_display_name", entry.get("dbname", "N/A"))
      print(f"    {dbname}: {primary} ({display})")
    if len(data) > 10:
      print(f"    … and {len(data) - 10} more (see JSON).")

  path = _save_json(data, f"mapid_{eid}", output_path=args.output)
  print(f"[*] Full JSON saved to {path}")


def cmd_get_sequence(args):
  """Fetch raw genomic DNA for a coordinate window."""
  coords = args.coords
  species = _get_species(args)
  assembly = args.assembly

  # Normalise the region string: accept chr17:100-200, 17:100-200,
  # 17:100..200
  region = coords.replace(",", "").lower().removeprefix("chr")
  region = region.replace("-", "..")

  client = _get_client(assembly)
  url = f"/sequence/region/{species}/{region}?"
  if assembly:
    url += f"coord_system_version={assembly}&"

  headers = {"Accept": "text/plain"}
  seq = client.fetch_text(url, headers=headers)

  if args.output:
    path = args.output
    with open(path, "w") as fh:
      fh.write(str(seq))
  else:
    fd, path = tempfile.mkstemp(prefix="ensembl_seq_", suffix=".txt", text=True)
    with os.fdopen(fd, "w") as fh:
      fh.write(str(seq))

  length = len(str(seq))
  print(f"[*] Fetched genomic sequence for {coords} (length: {length} bp).")
  print(f"[*] Sequence saved to {path}")


def cmd_gene_summary(args):
  """Return high-level metadata for a gene by its ENSG ID."""
  ensg = args.ensg_id
  client = _get_client(args.assembly)
  url = f"/lookup/id/{ensg}"
  data = client.fetch_json(url)

  symbol = data.get("display_name", "N/A")
  biotype = data.get("biotype", "N/A")
  desc = data.get("description", "N/A")
  chrom = data.get("seq_region_name", "?")
  start = data.get("start", "?")
  end = data.get("end", "?")
  strand = "+" if data.get("strand", 1) == 1 else "-"
  assembly = data.get("assembly_name", "N/A")

  print(f"[*] Gene summary for {ensg}:")
  print(f"    Symbol:      {symbol}")
  print(f"    Biotype:     {biotype}")
  print(f"    Description: {desc}")
  print(f"    Location:    chr{chrom}:{start}-{end} ({strand})")
  print(f"    Assembly:    {assembly}")

  path = _save_json(data, f"gene_{ensg}", output_path=args.output)
  print(f"[*] Full JSON saved to {path}")


def cmd_transcripts(args):
  """List transcripts for a gene, with optional MANE / canonical filtering."""
  ensg = args.ensg_id
  client = _get_client(args.assembly)
  url = f"/lookup/id/{ensg}?expand=1;mane=1"
  data = client.fetch_json(url)

  transcripts = data.get("Transcript", [])
  if not transcripts:
    print(f"[*] No transcripts found for {ensg}.")
    path = _save_json(data, f"transcripts_{ensg}", output_path=args.output)
    print(f"[*] Full JSON saved to {path}")
    return

  # Apply filters
  filtered = transcripts
  if args.only_mane:
    filtered = [t for t in transcripts if t.get("MANE")]
  elif args.only_canonical:
    filtered = [t for t in transcripts if t.get("is_canonical") == 1]

  if not filtered and (args.only_mane or args.only_canonical):
    label = "MANE Select" if args.only_mane else "Canonical"
    print(
        f"[*] No {label} transcript found for {ensg}. "
        f"Total transcripts: {len(transcripts)}."
    )
    return
  filter_label = ""
  if args.only_mane:
    filter_label = " (MANE Select only)"
  elif args.only_canonical:
    filter_label = " (Canonical only)"

  print(
      f"[*] {len(filtered)} transcript(s) for {ensg}{filter_label} "
      f"(from {len(transcripts)} total):"
  )
  print()
  print("| Transcript ID | Biotype | TSL | Length (bp) | Flags |")
  print("| --- | --- | --- | --- | --- |")
  for t in filtered:
    tid = t.get("id", "N/A")
    biotype = t.get("biotype", "N/A")
    tsl = t.get("TSL", {})
    tsl_val = tsl.get("value") if isinstance(tsl, dict) else tsl
    if tsl_val is None:
      tsl_val = "N/A"
    length = t.get("length", "N/A")
    flags = []
    if t.get("is_canonical") == 1:
      flags.append("Canonical")
    mane = t.get("MANE")
    if mane:
      for m in mane:
        flags.append(m.get("type", "MANE"))
    flag_str = ", ".join(flags) if flags else "-"
    print(f"| {tid} | {biotype} | {tsl_val} | {length} | {flag_str} |")

  path = _save_json(data, f"transcripts_{ensg}", output_path=args.output)
  print(f"\n[*] Full JSON saved to {path}")


def cmd_canonical_tss(args):
  """Retrieve the TSS for the canonical transcript of a gene."""
  query = args.gene
  species = _get_species(args)
  client = _get_client(args.assembly)

  # 1. Resolve to ID if symbol
  ensg = query
  if not query.lower().startswith("ens"):
    url = f"/lookup/symbol/{species}/{query}?expand=0"
    data = client.fetch_json(url)
    if isinstance(data, list) and len(data) > 1:
      print(
          f"[!] Warning: '{query}' resolved to {len(data)} genes. "
          f"Using first match: {data[0].get('id')} "
          f"({data[0].get('display_name', 'N/A')}). "
          f"Other matches: {', '.join(d.get('id', '?') for d in data[1:])}"
      )
    ensg = data.get("id") if not isinstance(data, list) else data[0].get("id")
    if not ensg:
      print(
          f"[!] Could not resolve symbol {query} to Ensembl ID.",
          file=sys.stderr,
      )
      sys.exit(1)

  # 2. Fetch transcripts
  url = f"/lookup/id/{ensg}?expand=1;mane=1"
  data = client.fetch_json(url)

  transcripts = data.get("Transcript", [])
  if not transcripts:
    print(f"[!] No transcripts found for {ensg}.", file=sys.stderr)
    sys.exit(1)

  canonical = None
  for t in transcripts:
    if t.get("is_canonical") == 1:
      canonical = t
      break

  if not canonical:
    print(f"[!] No Canonical transcript found for {ensg}.", file=sys.stderr)
    sys.exit(1)

  strand = canonical.get("strand", 1)
  start = canonical.get("start")
  end = canonical.get("end")
  tid = canonical.get("id")

  if strand == 1:
    tss = start
  else:
    tss = end

  chrom = data.get("seq_region_name", "?")
  print(f"[*] Gene {ensg} (chr{chrom})")
  print(f"[*] Canonical Transcript: {tid}")
  print(f"[*] Strand: {'+' if strand == 1 else '-'}")
  print(f"[*] TSS Coordinate: {tss}")

  path = _save_json(canonical, f"canonical_tss_{ensg}", output_path=args.output)
  print(f"[*] Full canonical transcript JSON saved to {path}")


def cmd_transcript_structure(args):
  """Return exon, CDS, and UTR layout for a transcript."""
  enst = args.transcript_id
  client = _get_client(args.assembly)
  url = f"/lookup/id/{enst}?expand=1;mane=1"
  data = client.fetch_json(url)

  exons = data.get("Exon", [])
  strand = data.get("strand", 1)
  trans_start = data.get("start")
  trans_end = data.get("end")

  print(f"[*] Transcript structure for {enst}:")
  print(f"    Biotype: {data.get('biotype', 'N/A')}")
  print(
      f"    Genomic span: chr{data.get('seq_region_name', '?')}:"
      f"{trans_start}-{trans_end} (strand {'+'  if strand == 1 else '-'})"
  )
  print(f"    Exons: {len(exons)}")

  translation = data.get("Translation")
  utr5 = None
  utr3 = None
  if translation:
    cds_start = translation.get("start")
    cds_end = translation.get("end")
    cds_length_aa = translation.get("length", "N/A")
    ensp = translation.get("id", "N/A")
    print(f"    CDS: {cds_start}-{cds_end} ({cds_length_aa} aa, {ensp})")

    # Compute UTRs
    utr5 = (
        (cds_end + 1, trans_end)
        if cds_end and trans_end and cds_end < trans_end
        else None
    )
    utr3 = (
        (trans_start, cds_start - 1)
        if cds_start and trans_start and cds_start > trans_start
        else None
    )
    if strand == 1:
      utr3, utr5 = utr5, utr3

    if utr5:
      print(f"    5' UTR: {utr5[0]}-{utr5[1]}")
    if utr3:
      print(f"    3' UTR: {utr3[0]}-{utr3[1]}")
  else:
    print("    (non-coding – no CDS/UTR)")

  if exons:
    print()
    print("| Exon # | ID | Start | End | Length (bp) |")
    print("| --- | --- | --- | --- | --- |")
    sorted_exons = sorted(exons, key=lambda e: e.get("start", 0))
    for i, ex in enumerate(sorted_exons, 1):
      eid = ex.get("id", "N/A")
      estart = ex.get("start", "?")
      eend = ex.get("end", "?")
      elen = (
          eend - estart + 1
          if isinstance(estart, int) and isinstance(eend, int)
          else "?"
      )
      print(f"| {i} | {eid} | {estart} | {eend} | {elen} |")

  # Enrich the saved data with computed UTR info
  if translation:
    data["_computed_utrs"] = {}
    if utr5:
      data["_computed_utrs"]["5_prime"] = {"start": utr5[0], "end": utr5[1]}
    if utr3:
      data["_computed_utrs"]["3_prime"] = {"start": utr3[0], "end": utr3[1]}

  path = _save_json(data, f"structure_{enst}", output_path=args.output)
  print(f"\n[*] Full JSON saved to {path}")


def cmd_protein_info(args):
  """Fetch ENSP ID and sequence length for a transcript."""
  enst = args.transcript_id
  client = _get_client(args.assembly)
  url = f"/lookup/id/{enst}?expand=1"
  data = client.fetch_json(url)

  translation = data.get("Translation")
  if not translation:
    print(f"[*] {enst} has no translation (likely non-coding).")
    path = _save_json(data, f"protein_{enst}", output_path=args.output)
    print(f"[*] Full JSON saved to {path}")
    return

  ensp = translation.get("id", "N/A")
  length = translation.get("length", "N/A")
  print(f"[*] Protein for {enst}:")
  print(f"    ENSP:   {ensp}")
  print(f"    Length: {length} aa")

  path = _save_json(data, f"protein_{enst}", output_path=args.output)
  print(f"[*] Full JSON saved to {path}")


def cmd_protein_sequence(args):
  """Fetch the amino acid sequence (FASTA) for a transcript or protein ID."""
  target = args.id
  client = _get_client(args.assembly)
  url = f"/sequence/id/{target}?type=protein"
  headers = {"Accept": "text/x-fasta"}
  fasta = client.fetch_text(url, headers=headers)

  if args.output:
    path = args.output
    with open(path, "w") as fh:
      fh.write(str(fasta))
  else:
    fd, path = tempfile.mkstemp(
        prefix=f"ensembl_protseq_{target}_", suffix=".fasta", text=True
    )
    with os.fdopen(fd, "w") as fh:
      fh.write(str(fasta))

  # Count sequence length (exclude header lines)
  lines = str(fasta).strip().split("\n")
  seq = "".join(l for l in lines if not l.startswith(">"))
  print(f"[*] Protein sequence for {target}: {len(seq)} aa")
  print(f"[*] FASTA saved to {path}")


def cmd_vep(args):
  """Predict variant consequences using the Ensembl VEP."""
  variant = args.variant_str
  species = _get_species(args)
  client = _get_client(args.assembly)

  if variant.startswith("rs"):
    url = f"/vep/{species}/id/{variant}{VEP_PLUGINS}"
  else:
    parts = variant.split(":")
    if len(parts) == 4:
      chrom, pos, ref, alt = parts
      end = int(pos) + len(ref) - 1
      region = f"{chrom}:{pos}-{end}:1"
      url = f"/vep/{species}/region/{region}/{alt}{VEP_PLUGINS}"
    else:
      # Fallback: treat as HGVS
      url = f"/vep/{species}/hgvs/{variant}{VEP_PLUGINS}"

  data = client.fetch_json(url)

  if not isinstance(data, list) or not data:
    print("[!] No VEP results returned.")
    path = _save_json(
        data if data else {},
        f"vep_{variant.replace(':', '_')}",
        output_path=args.output,
    )
    print(f"[*] JSON saved to {path}")
    return

  top = data[0]
  mcv = top.get("most_severe_consequence", "Unknown")
  input_var = top.get("input", variant)
  t_conseq = top.get("transcript_consequences", [])

  print(f"[*] Variant: {input_var}")
  print(f"[*] Most severe consequence: {mcv}")
  print(f"[*] Found {len(t_conseq)} transcript consequences.")

  # Build the predictions table
  open_keys = {
      "am_class": "AlphaMissense Class",
      "am_pathogenicity": "AlphaMissense Pathogenicity",
      "conservation": "Conservation",
      "phaplo": "Dosage Sensitivity (Haplo)",
      "ptriplo": "Dosage Sensitivity (Triplo)",
      "lof": "Loss of Function (Loftee)",
      "nmd": "Nonsense-mediated Decay",
      "utr_annotator": "UTR Annotator",
      "mutfunc": "Mutfunc",
      "loeuf": "Loss of Function (LOEUF)",
  }

  rows = []
  for tc in t_conseq:
    tid = tc.get("transcript_id", "Unknown")
    gene = tc.get("gene_symbol", "Unknown")

    terms = tc.get("consequence_terms", [])
    if terms:
      rows.append((tid, gene, "Consequence", ", ".join(terms)))

    aa = tc.get("amino_acids")
    if aa:
      rows.append((tid, gene, "Amino Acids", aa))

    sift = tc.get("sift_prediction")
    if sift:
      score = tc.get("sift_score")
      val = f"{sift} ({score})" if score is not None else sift
      rows.append((tid, gene, "SIFT", val))

    poly = tc.get("polyphen_prediction")
    if poly:
      score = tc.get("polyphen_score")
      val = f"{poly} ({score})" if score is not None else poly
      rows.append((tid, gene, "PolyPhen", val))

    for key, label in open_keys.items():
      val = tc.get(key)
      if val is None and "alphamissense" in tc:
        val = tc["alphamissense"].get(key)
      if val is not None:
        if isinstance(val, (list, dict)):
          val = json.dumps(val)
        rows.append((tid, gene, label, str(val)))

  if rows:
    print("\n[*] VEP Predictions Table:")
    print("| Transcript ID | Gene | Method/Metric | Value |")
    print("| --- | --- | --- | --- |")
    for r in rows:
      print(f"| {r[0]} | {r[1]} | {r[2]} | {r[3]} |")
  else:
    print("\n[*] No detailed predictions in transcript consequences.")

  safe = variant.replace(":", "_").replace(">", "_")
  path = _save_json(data, f"vep_{safe}", output_path=args.output)
  print(f"\n[*] Full JSON saved to {path}")


def main():
  """Parse CLI arguments and dispatch to the appropriate subcommand."""
  parent_parser = argparse.ArgumentParser(add_help=False)
  parent_parser.add_argument(
      "--output",
      help="Output file path (optional)",
  )
  parent_parser.add_argument(
      "--assembly",
      default=None,
      help="Assembly (e.g. GRCh38, GRCh37). Default: GRCh38.",
  )

  parser = argparse.ArgumentParser(
      description="Query the Ensembl REST API.",
      formatter_class=argparse.RawDescriptionHelpFormatter,
  )
  sub = parser.add_subparsers(dest="command", required=True)

  # ---- resolve-gene ----
  p = sub.add_parser(
      "resolve-gene",
      parents=[parent_parser],
      help="Resolve a gene symbol / alias / RefSeq ID to ENSG ID(s).",
  )
  p.add_argument("query", help="Gene symbol, alias, or RefSeq ID")
  p.add_argument(
      "--species",
      default=None,
      help="Species (defaults to 'human' if not specified)",
  )
  p.set_defaults(func=cmd_resolve_gene)

  # ---- map-id ----
  p = sub.add_parser(
      "map-id",
      parents=[parent_parser],
      help="Cross-reference an Ensembl ID to external databases.",
  )
  p.add_argument("id", help="Ensembl ID (ENSG, ENST, ENSP)")
  p.add_argument(
      "--external-db",
      dest="external_db",
      default=None,
      help="Filter by external DB (e.g., UniProt, HGNC, RefSeq_mRNA)",
  )
  p.set_defaults(func=cmd_map_id)

  # ---- get-sequence ----
  p = sub.add_parser(
      "get-sequence",
      parents=[parent_parser],
      help="Fetch raw genomic DNA for a coordinate window.",
  )
  p.add_argument(
      "coords",
      help="Genomic region, e.g. 17:7661779-7687550 or chr17:7661779-7687550",
  )
  p.add_argument(
      "--species",
      default=None,
      help="Species (defaults to 'human' if not specified)",
  )

  p.set_defaults(func=cmd_get_sequence)

  # ---- gene-summary ----
  p = sub.add_parser(
      "gene-summary",
      parents=[parent_parser],
      help="Get high-level metadata for a gene (symbol, biotype, location).",
  )
  p.add_argument("ensg_id", help="Ensembl gene ID (e.g. ENSG00000141510)")
  p.set_defaults(func=cmd_gene_summary)

  # ---- transcripts ----
  p = sub.add_parser(
      "transcripts",
      parents=[parent_parser],
      help="List transcripts for a gene, with optional MANE/canonical filter.",
  )
  p.add_argument("ensg_id", help="Ensembl gene ID")
  grp = p.add_mutually_exclusive_group()
  grp.add_argument(
      "--only-mane",
      action="store_true",
      help="Return only the MANE Select transcript (human only).",
  )
  grp.add_argument(
      "--only-canonical",
      action="store_true",
      help="Return only the Ensembl Canonical transcript.",
  )
  p.set_defaults(func=cmd_transcripts)

  # ---- canonical-tss ----
  p = sub.add_parser(
      "canonical-tss",
      parents=[parent_parser],
      help="Get TSS coordinate for the canonical transcript of a gene.",
  )
  p.add_argument("gene", help="Gene symbol or Ensembl ID")
  p.add_argument(
      "--species",
      default=None,
      help="Species (defaults to 'human' if not specified)",
  )
  p.set_defaults(func=cmd_canonical_tss)

  # ---- transcript-structure ----
  p = sub.add_parser(
      "transcript-structure",
      parents=[parent_parser],
      help="Get exon, CDS, and UTR layout for a transcript.",
  )
  p.add_argument(
      "transcript_id", help="Ensembl transcript ID (e.g. ENST00000269305)"
  )
  p.set_defaults(func=cmd_transcript_structure)

  # ---- protein-info ----
  p = sub.add_parser(
      "protein-info",
      parents=[parent_parser],
      help="Get ENSP ID and sequence length for a transcript.",
  )
  p.add_argument(
      "transcript_id", help="Ensembl transcript ID (e.g. ENST00000269305)"
  )
  p.set_defaults(func=cmd_protein_info)

  # ---- protein-sequence ----
  p = sub.add_parser(
      "protein-sequence",
      parents=[parent_parser],
      help="Fetch the amino acid sequence (FASTA) for an ENST or ENSP.",
  )
  p.add_argument("id", help="Ensembl transcript or protein ID")
  p.set_defaults(func=cmd_protein_sequence)

  # ---- vep ----
  p = sub.add_parser(
      "vep",
      parents=[parent_parser],
      help="Predict variant consequences (VEP) with open-license plugins.",
  )
  p.add_argument(
      "variant_str",
      help="Variant as chr:pos:ref:alt (e.g. 9:21971147:T:C) or rsID",
  )
  p.add_argument(
      "--species",
      default=None,
      help="Species (defaults to 'human' if not specified)",
  )
  p.set_defaults(func=cmd_vep)

  args = parser.parse_args()
  args.func(args)


if __name__ == "__main__":
  main()
