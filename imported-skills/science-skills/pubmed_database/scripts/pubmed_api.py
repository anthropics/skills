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

r"""PubMed API CLI.

Provides command-line access to NCBI E-utilities and PMC BioC endpoints.
Outputs JSON to stdout; all diagnostics go to stderr.

Usage:
  uv run pubmed_api.py brca1_search.json \
    search_pubmed "BRCA1 cancer" 5 relevance
  uv run pubmed_api.py abstract_35113657_31234568.json \
    fetch_article_abstracts "35113657,31234568"
"""

# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "polite-http",
#   "python-dotenv",
# ]
# ///

import inspect
import json
import os
import sys
import urllib.parse
import xml.etree.ElementTree as ET

import dotenv
from polite_http import http_client

EUTILS_BASE = "https://eutils.ncbi.nlm.nih.gov"
PMC_BIOC_BASE = (
    "https://www.ncbi.nlm.nih.gov/research/bionlp/RESTful/pmcoa.cgi/BioC_json"
)

_EUTILS_CLIENT = None
_PMC_CLIENT = None


def get_eutils_client():
  """Returns the lazily initialized E-utilities HttpClient."""
  global _EUTILS_CLIENT
  if _EUTILS_CLIENT is None:
    qps = 10 if os.environ.get("NCBI_API_KEY") else 3
    _EUTILS_CLIENT = http_client.HttpClient(EUTILS_BASE, qps=qps)
  return _EUTILS_CLIENT


def get_pmc_client():
  """Returns the lazily initialized PMC HttpClient."""
  global _PMC_CLIENT
  if _PMC_CLIENT is None:
    qps = 10 if os.environ.get("NCBI_API_KEY") else 3
    _PMC_CLIENT = http_client.HttpClient(PMC_BIOC_BASE, qps=qps)
  return _PMC_CLIENT


_MAX_JSON_ERROR_SNIPPET_LENGTH = 500


def _env_params():
  """Returns a dictionary of parameters from the environment and API key."""

  params = {}
  email = os.environ.get("USER_EMAIL")
  tool = os.environ.get("NCBI_TOOL")
  api_key = os.environ.get("NCBI_API_KEY")
  if email:
    params["email"] = email
  if tool:
    params["tool"] = tool
  if api_key:
    params["api_key"] = api_key

  return params


def _get(url, params=None, *, raw=False, client=None):
  """GET request with retry logic and rate limiting."""
  if client is None:
    client = get_eutils_client()

  if params:
    url = url + "?" + urllib.parse.urlencode(params)

  try:
    if raw:
      return client.fetch_text(url)
    return client.fetch_json(url)
  except http_client.HttpError as e:
    if e.status_code == 404:
      return {
          "error": "Record not found (HTTP 404).",
          "endpoint": url.split("?")[0],
      }
    else:
      return {
          "error": f"HTTP Error {e.status_code or 'Error'}: {str(e)}",
          "endpoint": url.split("?")[0],
      }
  except json.JSONDecodeError as e:
    body_snippet = e.doc
    if len(body_snippet) > _MAX_JSON_ERROR_SNIPPET_LENGTH:
      body_snippet = f"{body_snippet[:_MAX_JSON_ERROR_SNIPPET_LENGTH]}..."
    return {
        "error": f"Failed to parse JSON response. Body: {body_snippet}",
        "endpoint": url.split("?")[0],
    }


def _post(url, params):
  """POST request with retry logic and rate limiting."""
  try:
    data_bytes = urllib.parse.urlencode(params).encode("utf-8")
    resp = get_eutils_client().fetch(url, method="POST", data=data_bytes)
    return resp.text
  except http_client.HttpError as e:
    return {"error": f"HTTP Error {e.status_code or 'Error'}", "endpoint": url}


def search_pubmed(
    query: str,
    max_results: int = 10,
    sort_by: str = "relevance",
) -> list[str]:
  """Returns a list of PubMed IDs (PMIDs) matching a free-text query.

  Supports the full NCBI query syntax including Boolean operators, MeSH terms,
  field tags (e.g. [tiab], [au]), and date ranges. The sort_by parameter accepts
  'relevance', 'pub_date', 'Author', 'JournalName', or 'Title'.

  Args:
    query: Free-text or structured NCBI query
    max_results: Maximum PMIDs to return
    sort_by: 'relevance', 'pub_date', 'Author', 'JournalName', or 'Title'

  Returns:
    List of PMIDs
  """
  params = _env_params() | {
      "db": "pubmed",
      "term": query,
      "retmax": max_results,
      "sort": sort_by,
      "retmode": "json",
  }
  data = _get(f"{EUTILS_BASE}/entrez/eutils/esearch.fcgi", params)
  if isinstance(data, dict) and "error" in data:
    return data
  try:
    return data["esearchresult"]["idlist"]
  except (KeyError, TypeError):
    return {
        "error": "Unexpected esearch response structure",
        "endpoint": "esearch.fcgi",
    }


def _id_params(ids, webenv, query_key):
  if webenv:
    return {"WebEnv": webenv, "query_key": query_key}
  return {"id": ",".join(ids) if isinstance(ids, list) else ids}


def fetch_article_abstracts(
    pmids: list[str],
    webenv: str = "",
    query_key: str = "",
) -> list[dict[str, str | list[str] | None]]:
  """Retrieves article metadata and abstracts for a batch of PMIDs.

  Uses a single efetch XML call to extract all fields from PubmedArticle
  elements: title, authors, journal, date, abstract, and DOI.
  Structured abstracts (BACKGROUND, METHODS, RESULTS, CONCLUSION) are
  concatenated with their section labels.

  Can accept either explicit pmids or a webenv/query_key pair from
  cache_results_history to reference a previously uploaded set.

  Args:
    pmids: List of PMIDs
    webenv: WebEnv from cache_results_history
    query_key: query_key from cache_results_history

  Returns:
    List of dicts with article metadata and abstracts
  """
  id_p = _id_params(pmids, webenv, query_key)
  params = (
      _env_params()
      | id_p
      | {"db": "pubmed", "rettype": "abstract", "retmode": "xml"}
  )
  xml_data = _get(f"{EUTILS_BASE}/entrez/eutils/efetch.fcgi", params, raw=True)
  if isinstance(xml_data, dict) and "error" in xml_data:
    return xml_data

  try:
    root = ET.fromstring(xml_data)
  except ET.ParseError:
    return {"error": "Failed to parse efetch XML", "endpoint": "efetch.fcgi"}

  results = []
  for article in root.iter("PubmedArticle"):
    pmid_elem = article.find(".//PMID")
    if pmid_elem is None:
      continue

    art = article.find(".//Article")
    if art is None:
      continue

    authors = []
    for author in art.findall(".//AuthorList/Author"):
      last = author.findtext("LastName") or ""
      init = author.findtext("Initials") or ""
      name = (
          f"{last} {init}".strip()
          if last
          else author.findtext("CollectiveName") or ""
      )
      if name:
        authors.append(name)

    abstract_parts = []
    for at in art.findall(".//Abstract/AbstractText"):
      label = at.get("Label")
      text = "".join(at.itertext())
      if label:
        abstract_parts.append(f"{label}: {text}")
      else:
        abstract_parts.append(text)
    abstract = "\n".join(abstract_parts) if abstract_parts else None

    doi = None
    for eid in art.findall("ELocationID"):
      if eid.get("EIdType") == "doi":
        doi = eid.text
        break

    journal_elem = art.find(".//Journal")
    journal = None
    pubdate = None
    if journal_elem is not None:
      journal = journal_elem.findtext("Title")
      pd = journal_elem.find(".//PubDate")
      if pd is not None:
        year = pd.findtext("Year") or ""
        month = pd.findtext("Month") or ""
        day = pd.findtext("Day") or ""
        medline = pd.findtext("MedlineDate") or ""
        pubdate = f"{year} {month} {day}".strip() if year else medline

    results.append({
        "pmid": pmid_elem.text,
        "title": art.findtext("ArticleTitle"),
        "authors": authors,
        "journal": journal,
        "pubdate": pubdate,
        "doi": doi,
        "abstract": abstract,
    })

  return results


def find_linked_biological_data(
    source_pmid: str,
    target_database: str,
    linkname: str,
    dbfrom: str = "pubmed",
    mindate: str = "",
    maxdate: str = "",
    webenv: str = "",
    query_key: str = "",
) -> list[str]:
  """Finds records in another NCBI database linked to a source record.

  NCBI maintains cross-references between databases (e.g. pubmed -> gene,
  pubmed -> nuccore, pubmed -> pccompound). This traverses those links and
  returns the target database record IDs. The elink response structure is
  deeply nested (linksets -> linksetdbs -> links), so this flattens it.

  Can accept either an explicit source_pmid or a webenv/query_key pair from
  cache_results_history to link all IDs in a cached set at once.

  Args:
    source_pmid: Source record ID (PMID when dbfrom is pubmed)
    target_database: Target database
    linkname: Link name
    dbfrom: Source database (default: pubmed)
    mindate: Minimum date filter (YYYY/MM/DD), pubmed->pubmed only
    maxdate: Maximum date filter (YYYY/MM/DD), pubmed->pubmed only
    webenv: WebEnv from cache_results_history
    query_key: query_key from cache_results_history

  Returns:
    List of target database record IDs
  """
  id_p = _id_params(source_pmid, webenv, query_key)
  params = (
      _env_params()
      | id_p
      | {
          "dbfrom": dbfrom,
          "db": target_database,
          "linkname": linkname,
          "retmode": "json",
      }
  )
  if mindate:
    params["mindate"] = mindate
    params["datetype"] = "pdat"
  if maxdate:
    params["maxdate"] = maxdate
    params["datetype"] = "pdat"
  data = _get(f"{EUTILS_BASE}/entrez/eutils/elink.fcgi", params)
  if isinstance(data, dict):
    if "error" in data:
      return data
    if "ERROR" in data:
      return {"error": data["ERROR"], "endpoint": "elink.fcgi"}

  linksets = data.get("linksets", [])
  if not linksets:
    print(
        f"Got empty linksets for {source_pmid}, {target_database},"
        f" {linkname}, {dbfrom}",
        file=sys.stderr,
    )
    return []
  linksetdbs = linksets[0].get("linksetdbs", [])
  if not linksetdbs:
    print(
        f"Got empty linksetdbs for {source_pmid}, {target_database},"
        f" {linkname}, {dbfrom}",
        file=sys.stderr,
    )
    return []
  return [str(link_id) for link_id in linksetdbs[0].get("links", [])]


def discover_available_links(
    source_id: str,
    dbfrom: str = "pubmed",
) -> list[dict[str, str]]:
  """Lists all available ELink linknames for a given record.

  Uses cmd=acheck to ask NCBI which cross-database links exist for the
  source record. Returns a list of dicts with linkname and target database.

  Args:
    source_id: Source record ID (e.g. a PMID)
    dbfrom: Source database (default: pubmed)

  Returns:
    List of dicts with linkname and db keys
  """
  params = _env_params() | {
      "dbfrom": dbfrom,
      "id": source_id,
      "cmd": "acheck",
      "retmode": "json",
  }
  data = _get(f"{EUTILS_BASE}/entrez/eutils/elink.fcgi", params)
  if isinstance(data, dict):
    if "error" in data:
      return data
    if "ERROR" in data:
      return {"error": data["ERROR"], "endpoint": "elink.fcgi"}

  linksets = data.get("linksets", [])
  if not linksets:
    print(f"Got empty linksets for {source_id}, {dbfrom}", file=sys.stderr)
    return []

  idchecklist = linksets[0].get("idchecklist", {})
  if not idchecklist:
    print(f"Got empty idchecklist for {source_id}, {dbfrom}", file=sys.stderr)
    return []

  idlinksets = idchecklist.get("idlinksets", [])
  if not idlinksets:
    print(f"Got empty idlinksets for {source_id}, {dbfrom}", file=sys.stderr)
    return []

  results = []
  for idcheck in idlinksets:
    for linkinfo in idcheck.get("linkinfos", []):
      results.append({
          "linkname": linkinfo.get("linkname", ""),
          "db": linkinfo.get("dbto", ""),
      })
  return results


def get_full_text_pmc(pmid: str) -> dict[str, str]:
  """Retrieves the full text of an open-access article from PubMed Central.

  Uses the PMC BioC API (not E-utilities) which returns structured JSON with
  passage-level annotations. The passages are concatenated into a single string.
  Returns an error dict if the article is paywalled, embargoed, or not in PMC.

  Args:
    pmid: PMID of the article

  Returns:
    Dict with pmid and full_text or error message
  """
  url = f"{PMC_BIOC_BASE}/{pmid}/unicode"
  data = _get(url, client=get_pmc_client())
  if isinstance(data, dict) and "error" in data:
    return data
  try:
    passages = []
    for doc in data if isinstance(data, list) else [data]:
      for document in doc.get("documents", []):
        for passage in document.get("passages", []):
          text = passage.get("text", "")
          if text:
            passages.append(text)
    return {"pmid": pmid, "full_text": "\n".join(passages)}
  except (KeyError, TypeError):
    return {"error": "Unexpected BioC response structure", "endpoint": url}


def verify_medical_spelling(term: str) -> dict[str, str]:
  """Suggests spelling corrections for biomedical terms using NCBI's dictionary.

  Useful for normalizing user-provided medical terminology before searching.
  Returns the original term unchanged if NCBI considers the spelling correct
  (i.e. the CorrectedQuery field in the XML response is empty).

  Args:
    term: Term to correct

  Returns:
    Dict with original and corrected term or error message
  """
  params = _env_params() | {"db": "pubmed", "term": term}
  data = _get(f"{EUTILS_BASE}/entrez/eutils/espell.fcgi", params, raw=True)
  if isinstance(data, dict) and "error" in data:
    return data
  try:
    root = ET.fromstring(data)
    corrected = root.findtext(".//CorrectedQuery") or ""
    return {"original": term, "corrected": corrected if corrected else term}
  except ET.ParseError:
    return {"error": "Failed to parse espell XML", "endpoint": "espell.fcgi"}


def global_database_discovery(query: str) -> dict[str, int]:
  """Reports how many records match a query across all NCBI databases at once.

  Useful for deciding which databases (pubmed, gene, protein, nuccore, etc.)
  are worth querying for a given topic. This endpoint only returns XML, so
  responses are parsed with ElementTree rather than JSON.

  Args:
    query: Query to search for

  Returns:
    Dict with database names and counts or error message
  """
  params = _env_params() | {"term": query, "retmode": "xml"}
  data = _get(f"{EUTILS_BASE}/gquery", params, raw=True)
  if isinstance(data, dict) and "error" in data:
    return data
  try:
    root = ET.fromstring(data)
    result = {}
    for item in root.iter("ResultItem"):
      db_name = item.findtext("DbName")
      count = item.findtext("Count")
      if db_name and count:
        try:
          result[db_name] = int(count)
        except ValueError:
          result[db_name] = count
    return result
  except ET.ParseError:
    return {
        "error": "Failed to parse egquery XML",
        "endpoint": "egquery.fcgi",
    }


def match_raw_citations(citation_strings: list[str]) -> list[str]:
  """Resolves messy or incomplete bibliographic citations to PMIDs.

  Each citation string should be pipe-delimited in the format
  'journal|year|volume|first_page|author_name|your_key|'. The ecitmatch
  endpoint is archaic and returns pipe-delimited plain text (not JSON/XML),
  so responses are split by line and the PMID extracted from the last field.
  Unmatched citations are silently omitted from the result.

  Args:
    citation_strings: List of citation strings

  Returns:
    List of PMIDs
  """
  params = _env_params() | {
      "db": "pubmed",
      "retmode": "xml",
      "bdata": "\r".join(citation_strings),
  }
  data = _get(f"{EUTILS_BASE}/entrez/eutils/ecitmatch.cgi", params, raw=True)
  if isinstance(data, dict) and "error" in data:
    return data
  pmids = []
  for line in data.strip().split("\n"):
    parts = line.strip().rstrip("|").split("|")
    pmid = parts[-1].strip() if parts else ""
    if pmid and pmid.lower() != "not found":
      pmids.append(pmid)
  return pmids


def cache_results_history(pmids: list[str]) -> dict[str, str]:
  """Uploads PMIDs to the NCBI History Server and returns a session handle.

  The returned WebEnv and query_key can be passed to subsequent E-utility calls
  to reference the stored set, avoiding repeated transmission of large ID lists.
  Uses POST because GET would exceed the URL length limit for large batches.
  The endpoint returns XML despite accepting retmode=json.

  Args:
    pmids: List of PMIDs

  Returns:
    Dict with webenv and query_key or error message
  """
  params = _env_params() | {"db": "pubmed", "id": ",".join(pmids)}
  data = _post(f"{EUTILS_BASE}/entrez/eutils/epost.fcgi", params)
  if isinstance(data, dict) and "error" in data:
    return data
  try:
    root = ET.fromstring(data)
    webenv = root.findtext(".//WebEnv") or ""
    query_key = root.findtext(".//QueryKey") or ""
    return {"webenv": webenv, "query_key": query_key}
  except ET.ParseError:
    return {"error": "Failed to parse epost XML", "endpoint": "epost.fcgi"}


def fetch_database_summary(
    database: str,
    id_list: list[str],
) -> list[dict[str, str | list[str] | None]]:
  """Retrieves summary metadata for records in any NCBI database.

  Wraps the esummary endpoint to resolve opaque UIDs (returned by
  find_linked_biological_data) into human-readable metadata such as
  accession numbers, gene names, organism, and descriptions.

  Args:
    database: Target NCBI database (e.g. nuccore, gene, protein, pccompound)
    id_list: List of UIDs to summarize

  Returns:
    List of dicts, one per UID, with database-specific metadata fields.
  """
  params = _env_params() | {
      "db": database,
      "id": ",".join(id_list),
      "retmode": "json",
  }
  data = _get(f"{EUTILS_BASE}/entrez/eutils/esummary.fcgi", params)
  if isinstance(data, dict) and "error" in data:
    return data
  try:
    result_block = data.get("result", {})
    uids = result_block.get("uids", [])
    summaries = []
    for uid in uids:
      doc = result_block.get(uid, {})
      if doc:
        summaries.append(doc)
    return summaries
  except (KeyError, TypeError, AttributeError):
    return {
        "error": "Unexpected esummary response",
        "endpoint": "esummary.fcgi",
    }


# ---------------------------------------------------------------------------
# CLI dispatch — inferred from type hints via inspect
# ---------------------------------------------------------------------------
FUNCTIONS = {
    fn.__name__: fn
    for fn in [
        search_pubmed,
        fetch_article_abstracts,
        find_linked_biological_data,
        discover_available_links,
        get_full_text_pmc,
        verify_medical_spelling,
        global_database_discovery,
        match_raw_citations,
        cache_results_history,
        fetch_database_summary,
    ]
}


def _is_list_type(annotation):
  origin = getattr(annotation, "__origin__", None)
  return origin is list


def _coerce_arg(value: str, annotation):
  if _is_list_type(annotation):
    return value.split(",")
  if annotation is int:
    return int(value)
  return value


def main():
  dotenv.load_dotenv(os.path.expanduser("~/.env"))
  if len(sys.argv) < 3:
    print("Usage: pubmed_api.py <output_file> <func> [--flag val]")
    print(f"Available: {', '.join(FUNCTIONS.keys())}")
    sys.exit(1)

  output_file = sys.argv[1]
  func_name = sys.argv[2]
  if func_name not in FUNCTIONS:
    print(f"Error: Unknown function: {func_name}")
    sys.exit(1)

  if os.path.exists(output_file):
    print(f"Error: Output file {output_file} already exists")
    sys.exit(1)

  fn = FUNCTIONS[func_name]
  sig = inspect.signature(fn)

  positional = []
  flags = {}
  raw_args = sys.argv[3:]
  i = 0
  while i < len(raw_args):
    if raw_args[i].startswith("--"):
      key = raw_args[i][2:]
      if i + 1 < len(raw_args):
        flags[key] = raw_args[i + 1]
        i += 2
      else:
        print(f"Error: Missing value for flag --{key}")
        sys.exit(1)
    else:
      positional.append(raw_args[i])
      i += 1

  kwargs = {}
  pos_idx = 0
  for name, param in sig.parameters.items():
    if name in flags:
      kwargs[name] = _coerce_arg(flags[name], param.annotation)
    elif pos_idx < len(positional):
      kwargs[name] = _coerce_arg(positional[pos_idx], param.annotation)
      pos_idx += 1
    elif param.default is not inspect.Parameter.empty:
      kwargs[name] = param.default
    else:
      print(f"Error: Missing required argument: {name}")
      sys.exit(1)

  try:
    result = fn(**kwargs)
  except Exception as e:
    print(f"Internal error in {func_name}: {e}")
    sys.exit(2)

  if isinstance(result, dict) and "error" in result:
    msg = result["error"]
    endpoint = result.get("endpoint", "")
    if endpoint:
      print(f"API error ({endpoint}): {msg}")
    else:
      print(f"API error: {msg}")
    sys.exit(1)

  with open(output_file, "w", encoding="utf-8") as f:
    json.dump(result, f, indent=2)
    print(file=f)

  if isinstance(result, list):
    print(f"API call OK: {len(result)} results json written to {output_file}")
  elif isinstance(result, dict):
    keys = ", ".join(sorted(result.keys()))
    print(f"API call OK: result ({keys}) json written to {output_file}")
  else:
    print(f"API call OK: result json written to {output_file}")


if __name__ == "__main__":
  main()
