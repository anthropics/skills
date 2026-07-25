"""Academic source adapters."""

from .base import AcademicSourceAdapter, AdapterDisabled, AdapterError, normalize_doi, normalize_title
from .arxiv import ArxivAdapter
from .crossref import CrossrefAdapter
from .openalex import OpenAlexAdapter
from .pubmed import PubMedAdapter
from .sciencedirect import ScienceDirectAdapter
from .scopus import ScopusAdapter
from .semantic_scholar import SemanticScholarAdapter

__all__ = [
    "ArxivAdapter",
    "AdapterDisabled",
    "AdapterError",
    "AcademicSourceAdapter",
    "CrossrefAdapter",
    "OpenAlexAdapter",
    "PubMedAdapter",
    "ScienceDirectAdapter",
    "ScopusAdapter",
    "SemanticScholarAdapter",
    "normalize_doi",
    "normalize_title",
]
