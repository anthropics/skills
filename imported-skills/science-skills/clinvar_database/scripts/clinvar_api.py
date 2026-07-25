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

"""A Python client for querying the NCBI ClinVar database via E-utilities."""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
#   "python-dotenv",
# ]
# ///

from __future__ import annotations

import argparse
import json
import os
import sys
from typing import Any
import urllib.parse
import xml.etree.ElementTree as ET

import dotenv
from polite_http import http_client


class _Response:

  def __init__(self, status_code: int, content: bytes):
    self.status_code = status_code
    self.content = content


class RateLimitError(Exception):
  """Raised when the NCBI API rate limit is exceeded."""


class ClinVarClient:
  """A robust Python client for querying the NCBI ClinVar database.

  This client uses NCBI E-utilities and handles rate limiting, API key
  authentication, and complex XML/JSON response parsing.
  """

  BASE_URL = 'https://eutils.ncbi.nlm.nih.gov/entrez/eutils/'

  def __init__(self):
    # Look for the NCBI API Key in the environment
    self.api_key = os.environ.get('NCBI_API_KEY')

    # NCBI limits: 10 req/sec with key, 3 req/sec without key
    self.rate_limit = 10 if self.api_key else 3
    self.client = http_client.HttpClient(self.BASE_URL, qps=self.rate_limit)

  def _request(self, endpoint: str, params: dict[str, Any]) -> '_Response':
    """Makes an HTTP request to the given E-utilities endpoint.

    Args:
      endpoint: The API endpoint to call (e.g. 'esearch.fcgi').
      params: Query parameters for the request.

    Returns:
      A `_Response` with status code and content bytes.

    Raises:
      RateLimitError: If a 429 status is received.
      RuntimeError: On any other HTTP or network error.
    """
    if self.api_key:
      params['api_key'] = self.api_key

    url = urllib.parse.urljoin(self.BASE_URL, endpoint)
    query_string = urllib.parse.urlencode(params, doseq=True)
    full_url = f'{url}?{query_string}'

    try:
      resp = self.client.fetch(full_url)
      return _Response(resp.status_code, resp.data)
    except http_client.HttpError as exc:
      if exc.status_code == 429:
        raise RateLimitError(
            'HTTP 429 Too Many Requests hit on NCBI E-utilities.\nAGENT'
            ' INSTRUCTION: Pause execution and inform the user that an NCBI API'
            ' Key is required to increase the rate limit, providing the URL'
            ' https://www.ncbi.nlm.nih.gov/clinvar/docs/api_http/ for'
            ' instructions on how to obtain one. The user will need to set the'
            ' NCBI_API_KEY environment variable and advise the agent to retry.'
        ) from exc
      raise RuntimeError(
          f'HTTP {exc.status_code} error from NCBI E-utilities: {exc}'
      ) from exc
    except Exception as exc:
      raise RuntimeError(
          f'Failed to fetch data from NCBI E-utilities: {exc}'
      ) from exc

  def count_variants(self, query: str) -> int:
    """Returns the total number of variants matching a query.

    This is a lightweight call that does not fetch any variant IDs. Use it
    to check result set size before committing to a full search.

    Args:
        query: NCBI Entrez search query string.

    Returns:
        Total number of matching variant IDs.
    """
    params = {
        'db': 'clinvar',
        'term': query,
        'rettype': 'count',
        'retmode': 'json',
    }
    response = self._request('esearch.fcgi', params)
    data = json.loads(response.content)
    return int(data.get('esearchresult', {}).get('count', 0))

  def search_variants(
      self,
      query: str,
      retmax: int = 0,
      page_size: int = 500,
  ) -> dict[str, int | list[str]]:
    """Identifies variants based on genomic location, gene symbols, etc.

    Automatically paginates through all results using `retstart` to ensure
    complete, deterministic retrieval. Uses the NCBI Entrez Standard Search
    Syntax.

    Args:
        query: The search query string.
        retmax: Maximum total number of variant IDs to return. A value of 0 (the
          default) means "fetch all matching results".
        page_size: Number of IDs to fetch per API request (default 500, max
          10000 per NCBI limits).

    Returns:
        A dictionary with keys:
        - ``total_count``: Total number of matching variants in ClinVar.
        - ``fetched_count``: Number of IDs actually retrieved.
        - ``variant_ids``: List of ClinVar Variation ID strings.
    """
    page_size = min(page_size, 10000)

    # Step 1: Get total count.
    total_count = self.count_variants(query)
    target = total_count if retmax == 0 else min(total_count, retmax)

    print(f'Total matching variants: {total_count}. Fetching {target}...')

    # Step 2: Paginate.
    all_ids: list[str] = []
    retstart = 0
    page_num = 0
    total_pages = (target + page_size - 1) // page_size if target > 0 else 0

    while retstart < target:
      page_num += 1
      current_page_size = min(page_size, target - retstart)
      print(
          f'  Fetching page {page_num}/{total_pages}'
          f' (IDs {retstart + 1}-{retstart + current_page_size}'
          f' of {target})...'
      )

      params = {
          'db': 'clinvar',
          'term': query,
          'retmode': 'json',
          'retmax': current_page_size,
          'retstart': retstart,
      }
      response = self._request('esearch.fcgi', params)
      data = json.loads(response.content)
      ids = data.get('esearchresult', {}).get('idlist', [])

      if not ids:
        break

      all_ids.extend(ids)
      retstart += len(ids)

    print(f'Fetched {len(all_ids)} variant IDs.')

    return {
        'total_count': total_count,
        'fetched_count': len(all_ids),
        'variant_ids': all_ids,
    }

  def get_interpretation_summary(
      self, variant_ids: list[str | int]
  ) -> list[dict[str, str | list[str]]]:
    """Retrieves top-line clinical significance labels and star ratings.

    Args:
        variant_ids: A list of variant IDs to summarize.

    Returns:
        A list of summary dictionaries for rapid variant screening.
    """
    if not variant_ids:
      return []

    # Ensure all IDs are strings and join with commas
    ids_str = ','.join(map(str, variant_ids))

    params = {'db': 'clinvar', 'id': ids_str, 'retmode': 'json'}

    response = self._request('esummary.fcgi', params)
    data = json.loads(response.content)

    result_data = data.get('result', {})
    uids = result_data.get('uids', [])

    summaries = []
    for uid in uids:
      var_data = result_data.get(uid, {})
      significance = 'Unknown'
      review_status = 'Unknown'
      last_evaluated = 'Unknown'

      # Extract primary classification and date from possible classification
      # blocks
      for sig_key in [
          'clinical_significance',
          'germline_classification',
          'clinical_impact_classification',
          'oncogenicity_classification',
      ]:
        sig_data = var_data.get(sig_key)
        if sig_data and isinstance(sig_data, dict):
          desc = sig_data.get('description')
          if desc and significance == 'Unknown':
            significance = desc
            review_status = sig_data.get('review_status', 'Unknown')

          date = sig_data.get('last_evaluated')
          if date and last_evaluated == 'Unknown':
            last_evaluated = date
        elif sig_data and significance == 'Unknown':
          significance = str(sig_data)

      # Extract phenotypes from classification trait sets
      phenotypes = []
      for class_key in [
          'germline_classification',
          'clinical_impact_classification',
          'oncogenicity_classification',
      ]:
        classification = var_data.get(class_key, {})
        for trait in classification.get('trait_set', []):
          name = trait.get('trait_name')
          if name and name not in phenotypes:
            phenotypes.append(name)

      # Extract gene information
      genes = []
      for gene in var_data.get('genes', []):
        genes.append({
            'gene_id': gene.get('geneid', ''),
            'symbol': gene.get('symbol', ''),
            'strand': gene.get('strand', ''),
        })

      # Extract variation type (uses obj_type in esummary)
      variation_type = var_data.get('obj_type', '')

      # Extract molecular consequence (uses molecular_consequence_list)
      molecular_consequences = var_data.get('molecular_consequence_list', [])

      summaries.append({
          'variant_id': uid,
          'clinical_significance': significance,
          'review_status': review_status,
          'last_evaluated': last_evaluated,
          'phenotypes': phenotypes,
          'title': var_data.get('title', ''),
          'genes': genes,
          'variation_type': variation_type,
          'molecular_consequences': molecular_consequences,
      })

    return summaries

  def get_clinical_evidence(self, variant_id: str) -> dict[str, Any]:
    """Fetches full records including free-text clinician rationales.

    Note: Efetch for clinvar returns XML; parsed here into a clean dictionary.

    Args:
        variant_id: The variant ID to retrieve clinical evidence for.

    Returns:
        A dictionary containing clinical evidence submissions, allele
        information, conditions, and structural variant details.
    """
    # Ensure we're using a VCV accession for the efetch call
    if not str(variant_id).startswith('VCV'):
      try:
        vcv_id = f'VCV{int(variant_id):09d}'
      except ValueError:
        vcv_id = variant_id
    else:
      vcv_id = variant_id

    params = {'db': 'clinvar', 'id': vcv_id, 'rettype': 'vcv', 'retmode': 'xml'}

    response = self._request('efetch.fcgi', params)

    try:
      root = ET.fromstring(response.content.decode('utf-8'))
    except ET.ParseError as e:
      raise RuntimeError(f'Failed to parse NCBI XML response: {e}') from e

    # Navigate the ClinVarSet XML structure
    # Submissions are typically found under ClinVarAssertion or
    # ClinicalAssertion nodes
    assertions = root.findall('.//ClinVarAssertion') + root.findall(
        './/ClinicalAssertion'
    )

    submissions: list[dict[str, str | None]] = []
    for assertion in assertions:
      # Extract Submitter Name
      submitter_node = assertion.find('.//ClinVarAccession')
      if submitter_node is not None:
        submitter_name = (
            submitter_node.attrib.get('submitter')
            or submitter_node.attrib.get('SubmitterName')
            or 'Unknown'
        )
      else:
        submitter_name = 'Unknown'

      # Extract Classification (Clinical Significance)
      clin_sig_node = assertion.find('.//ClinicalSignificance/Description')
      if clin_sig_node is None:
        clin_sig_node = assertion.find(
            './/Classification/GermlineClassification'
        )

      classification = (
          clin_sig_node.text if clin_sig_node is not None else 'Unknown'
      )

      # Extract Curator Notes / Comments
      curator_notes = []
      for comment in assertion.findall('.//Comment'):
        if comment.text:
          curator_notes.append(comment.text.strip())

      # Extract Assertion Criteria if present
      assertion_criteria = None
      criteria_node = assertion.find(
          './/AttributeSet/Attribute[@Type="AssertionMethod"]'
      )
      if criteria_node is None:
        # In VCV XML, ReviewStatus might be what we want
        criteria_node = assertion.find('.//Classification/ReviewStatus')

      if criteria_node is not None and criteria_node.text:
        assertion_criteria = criteria_node.text.strip()

      # Extract date of last evaluation
      date_last_evaluated = None
      date_node = assertion.find('.//ClinicalSignificance')
      if date_node is not None:
        date_last_evaluated = date_node.attrib.get('DateLastEvaluated')
      if date_last_evaluated is None:
        date_node = assertion.find('.//Classification')
        if date_node is not None:
          date_last_evaluated = date_node.attrib.get('DateLastEvaluated')

      submissions.append({
          'submitter_name': submitter_name,
          'classification': classification,
          'curator_notes': '; '.join(curator_notes) if curator_notes else None,
          'assertion_criteria': assertion_criteria,
          'date_last_evaluated': date_last_evaluated,
      })

    return {
        'variant_id': variant_id,
        'allele_info': self._extract_allele_info(root),
        'conditions': self._extract_conditions(root),
        'functional_consequences': self._extract_functional_consequences(root),
        'structural_variant_details': self._extract_structural_variant(root),
        'citation_references': self._extract_global_citations(root),
        'submissions': submissions,
    }

  def _extract_global_citations(self, root: ET.Element) -> list[str]:
    """Extracts PMIDs for variant classification."""
    pmids = []

    # 1. Target VCV structure: ClassifiedRecord/Classifications/*
    # We only pick Citations that are DIRECT children of the classification
    # block to avoid picking up phenotype/gene citations in ConditionList.
    for classifications in root.findall('.//Classifications'):
      for classification in classifications:
        for citation in classification.findall(
            './Citation/ID[@Source="PubMed"]'
        ):
          if citation.text:
            pmids.append(citation.text.strip())

    # 2. Target ClinVarSet structure: InterpretedRecord
    # Similarly, only pick citations that are direct children of the
    # top-level interpretation blocks.
    for interpreted in root.findall('.//InterpretedRecord'):
      for child in interpreted:
        for citation in child.findall('./Citation/ID[@Source="PubMed"]'):
          if citation.text:
            pmids.append(citation.text.strip())

    # 3. Fallback: If still empty, check for Variation level citations
    # These are directly under the Measure element.
    if not pmids:
      for measure in root.findall('.//Measure'):
        for citation in measure.findall('./Citation/ID[@Source="PubMed"]'):
          if citation.text:
            pmids.append(citation.text.strip())

    return sorted(list(set(pmids)))

  def _extract_allele_info(self, root: ET.Element) -> dict[str, str | None]:
    """Extracts allele location and identity from the VCV XML."""
    info = {
        'chromosome': None,
        'position_start': None,
        'position_stop': None,
        'reference_allele': None,
        'alternate_allele': None,
        'cytogenetic_band': None,
        'dbsnp_rsid': None,
    }

    # Try SequenceLocation nodes (GRCh38 preferred)
    for loc in root.findall('.//SequenceLocation'):
      if loc.attrib.get('Assembly') == 'GRCh38':
        info['chromosome'] = loc.attrib.get('Chr')
        info['position_start'] = loc.attrib.get('start')
        info['position_stop'] = loc.attrib.get('stop')
        info['reference_allele'] = loc.attrib.get('referenceAllele')
        info['alternate_allele'] = loc.attrib.get('alternateAllele')
        break

    # Fallback: first SequenceLocation if GRCh38 not found
    if info['chromosome'] is None:
      first_loc = root.find('.//SequenceLocation')
      if first_loc is not None:
        info['chromosome'] = first_loc.attrib.get('Chr')
        info['position_start'] = first_loc.attrib.get('start')
        info['position_stop'] = first_loc.attrib.get('stop')
        info['reference_allele'] = first_loc.attrib.get('referenceAllele')
        info['alternate_allele'] = first_loc.attrib.get('alternateAllele')

    # Cytogenetic band
    cyto_node = root.find('.//CytogeneticLocation')
    if cyto_node is not None and cyto_node.text:
      info['cytogenetic_band'] = cyto_node.text.strip()

    # dbSNP rsID from XRef
    for xref in root.findall('.//XRef'):
      if xref.attrib.get('DB') == 'dbSNP':
        info['dbsnp_rsid'] = f"rs{xref.attrib.get('ID', '')}"
        break

    return info

  def _extract_conditions(
      self, root: ET.Element
  ) -> list[dict[str, str | None]]:
    """Extracts condition/trait details with ontology cross-references."""
    conditions = []
    seen_names = set()

    for trait in root.findall('.//TraitSet/Trait'):
      name_node = trait.find('./Name/ElementValue[@Type="Preferred"]')
      if name_node is None:
        name_node = trait.find('./Name/ElementValue')
      condition_name = (
          name_node.text.strip()
          if name_node is not None and name_node.text
          else 'Unknown'
      )

      # Deduplicate by name
      if condition_name in seen_names:
        continue
      seen_names.add(condition_name)

      # Collect ontology cross-references
      medgen_cui = None
      omim_id = None
      orphanet_id = None
      hpo_terms = []

      for xref in trait.findall('.//XRef'):
        db = xref.attrib.get('DB', '')
        ref_id = xref.attrib.get('ID', '')
        if db == 'MedGen':
          medgen_cui = ref_id
        elif db == 'OMIM':
          omim_id = ref_id
        elif db == 'Orphanet':
          orphanet_id = ref_id
        elif db == 'HP' or db == 'Human Phenotype Ontology':
          hpo_terms.append(ref_id)

      conditions.append({
          'name': condition_name,
          'medgen_cui': medgen_cui,
          'omim_id': omim_id,
          'orphanet_id': orphanet_id,
          'hpo_terms': hpo_terms,
      })

    return conditions

  def _extract_functional_consequences(
      self, root: ET.Element
  ) -> list[dict[str, str]]:
    """Extracts molecular consequence terms from Sequence Ontology."""
    consequences = []
    seen = set()

    # FunctionalConsequence nodes carry SO terms
    for fc in root.findall('.//FunctionalConsequence'):
      value = fc.attrib.get('Value', '')
      if value and value not in seen:
        seen.add(value)
        so_id = None
        xref = fc.find('./XRef[@DB="Sequence Ontology"]')
        if xref is None:
          xref = fc.find('./XRef[@DB="SO"]')
        if xref is not None:
          so_id = xref.attrib.get('ID')
        consequences.append({'value': value, 'sequence_ontology_id': so_id})

    return consequences

  def _extract_structural_variant(
      self, root: ET.Element
  ) -> dict[str, str | None] | None:
    """Extracts structural variant details for CNVs."""
    # Only present for structural variants / CNVs
    loc = None
    for seq_loc in root.findall('.//SequenceLocation'):
      if seq_loc.attrib.get('Assembly') == 'GRCh38':
        loc = seq_loc
        break
    if loc is None:
      loc = root.find('.//SequenceLocation')

    if loc is None:
      return None

    # Structural variant fields are only present for CNVs
    outer_start = loc.attrib.get('outerStart')
    inner_start = loc.attrib.get('innerStart')
    inner_stop = loc.attrib.get('innerStop')
    outer_stop = loc.attrib.get('outerStop')
    copy_number = None

    # Check for copy number in Attribute nodes
    for attr in root.findall(
        './/AttributeSet/Attribute[@Type="AbsoluteCopyNumber"]'
    ):
      if attr.text:
        copy_number = attr.text.strip()
        break

    # Only return if there is at least one structural-specific field
    if not any([outer_start, inner_start, inner_stop, outer_stop, copy_number]):
      return None

    return {
        'outer_start': outer_start,
        'inner_start': inner_start,
        'inner_stop': inner_stop,
        'outer_stop': outer_stop,
        'copy_number': copy_number,
    }


def write_output(data, output_file):
  """Writes output to a JSON file."""
  try:
    with open(output_file, 'w', encoding='utf-8') as f:
      json.dump(data, f, indent=2)
    print(f'Success! Data written to: {output_file}')
  except (OSError, TypeError) as e:
    print(f'Error writing to file {output_file}: {e}')
    sys.exit(1)


def main():
  dotenv.load_dotenv(os.path.expanduser('~/.env'))
  parser = argparse.ArgumentParser(
      description='ClinVar Database API Wrapper Script'
  )
  subparsers = parser.add_subparsers(dest='command', required=True)

  # count
  p_count = subparsers.add_parser(
      'count',
      help='Get the total number of variants matching a query (no ID fetch)',
  )
  p_count.add_argument(
      '--query',
      required=True,
      help='NCBI Entrez search query (e.g. "BRCA1[gene]")',
  )
  p_count.add_argument('--output', required=True, help='Output JSON file path')

  # search
  p_search = subparsers.add_parser(
      'search',
      help='Search for variants by gene, coordinates, or clinical attributes',
  )
  p_search.add_argument(
      '--query',
      required=True,
      help='NCBI Entrez search query (e.g. "BRCA1[gene]")',
  )
  p_search.add_argument(
      '--retmax',
      type=int,
      default=0,
      help=(
          'Maximum total number of variant IDs to return. 0 (default) means'
          ' fetch all matching results.'
      ),
  )
  p_search.add_argument(
      '--page_size',
      type=int,
      default=500,
      help='Number of IDs to fetch per API request (default: 500, max: 10000).',
  )
  p_search.add_argument('--output', required=True, help='Output JSON file path')

  # summary
  p_summary = subparsers.add_parser(
      'summary',
      help=(
          'Get clinical significance, star rating, and phenotypes for'
          ' variant IDs'
      ),
  )
  p_summary.add_argument(
      '--variant_ids',
      nargs='+',
      required=True,
      help='One or more ClinVar Variation IDs',
  )
  p_summary.add_argument(
      '--output', required=True, help='Output JSON file path'
  )

  # evidence
  p_evidence = subparsers.add_parser(
      'evidence',
      help='Fetch full clinical evidence record for a single variant',
  )
  p_evidence.add_argument(
      '--variant_id',
      required=True,
      help='A single ClinVar Variation ID',
  )
  p_evidence.add_argument(
      '--output', required=True, help='Output JSON file path'
  )

  args = parser.parse_args()
  client = ClinVarClient()

  if args.command == 'count':
    total = client.count_variants(args.query)
    data = {'total_count': total}
    print(f'Total matching variants: {total}')
  elif args.command == 'search':
    data = client.search_variants(
        args.query, retmax=args.retmax, page_size=args.page_size
    )
  elif args.command == 'summary':
    data = client.get_interpretation_summary(args.variant_ids)
  elif args.command == 'evidence':
    data = client.get_clinical_evidence(args.variant_id)
  else:
    raise AssertionError(f'Unknown command: {args.command}')
  write_output(data, args.output)


if __name__ == '__main__':
  main()
