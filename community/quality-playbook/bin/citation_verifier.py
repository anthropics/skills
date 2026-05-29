"""citation_verifier.py — schemas.md §5.4 extraction + §5.5 section resolution.

Pure-function implementation of the deterministic excerpt extraction
algorithm (§5.4) and section resolution rules (§5.5) from schemas.md.
Shared between reference_docs_ingest.py (Phase 1) and quality_gate.py (Phase 5).

Design constraint: this module is stdlib-only and side-effect-free except
where the caller explicitly passes paths. `extract_excerpt` and
`resolve_section` are pure functions; `verify_citation` reads one document
file from disk but does not mutate anything. Two implementations following
the algorithms in this module MUST produce byte-identical output on the
same (document_bytes, section, line) input — that byte-determinism is the
Layer-1 anti-hallucination mechanism.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional, Tuple


# Machine-readable error codes (stable across ingest and gate).
ERROR_LOCATOR_MISSING = "locator_missing"
ERROR_LOCATOR_OUT_OF_RANGE = "locator_out_of_range"
ERROR_BLANK_ANCHOR = "blank_anchor"
ERROR_SECTION_NOT_FOUND = "section_not_found"
ERROR_SECTION_AMBIGUOUS = "section_ambiguous"
ERROR_INVALID_UTF8 = "invalid_utf8"
ERROR_UNSUPPORTED_EXTENSION = "unsupported_extension"
ERROR_HASH_MISMATCH = "hash_mismatch"
ERROR_DOCUMENT_NOT_FOUND = "document_not_found"
ERROR_DOCUMENT_OUT_OF_ROOT = "document_out_of_root"
ERROR_EXCERPT_MISMATCH = "excerpt_mismatch"


_BOM_BYTES = b"\xef\xbb\xbf"
_SUPPORTED_EXTENSIONS = frozenset({".md", ".txt"})


class CitationResolutionError(Exception):
    """Raised by extract_excerpt and resolve_section on any failure.

    The error code is the machine-readable constant above; the message is
    human-readable and suitable for surfacing in test assertions and gate
    failure reports.
    """

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _normalize_extension(extension: str) -> str:
    ext = (extension or "").lower()
    if ext and not ext.startswith("."):
        ext = "." + ext
    if ext not in _SUPPORTED_EXTENSIONS:
        raise CitationResolutionError(
            ERROR_UNSUPPORTED_EXTENSION,
            f"extension {extension!r} is not supported; expected one of .md, .txt",
        )
    return ext


def _decode_document(document_bytes: bytes) -> str:
    """Step 1 of §5.4: UTF-8 strict decode, with BOM tolerance at position 0."""
    if document_bytes[:3] == _BOM_BYTES:
        document_bytes = document_bytes[3:]
    try:
        return document_bytes.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise CitationResolutionError(
            ERROR_INVALID_UTF8,
            f"document is not valid UTF-8 at byte offset {exc.start}: {exc.reason}",
        ) from exc


def resolve_section(lines: List[str], extension: str, section: str) -> int:
    """Return the 1-based line number of the unique section anchor per §5.5.

    Raises CitationResolutionError on zero or ambiguous matches. The input
    `lines` list is the terminator-free list produced by `str.splitlines()`
    on the (BOM-stripped) decoded document text.
    """
    ext = _normalize_extension(extension)
    escaped = re.escape(section)
    if ext == ".md":
        pattern = re.compile(r"^#{1,6}[ \t]+" + escaped + r"(?:[ \t]|$)")
        def _match(line: str) -> bool:
            return pattern.match(line) is not None
    else:  # ".txt"
        pattern = re.compile(r"^" + escaped + r"(?:[ \t]|$)")
        def _match(line: str) -> bool:
            return pattern.match(line.lstrip()) is not None

    matches: List[int] = []
    for index, line in enumerate(lines, start=1):
        if _match(line):
            matches.append(index)
            if len(matches) > 1:
                break

    if not matches:
        raise CitationResolutionError(
            ERROR_SECTION_NOT_FOUND,
            f"section {section!r} not found in document with extension {ext!r}",
        )
    if len(matches) > 1:
        raise CitationResolutionError(
            ERROR_SECTION_AMBIGUOUS,
            (
                f"section {section!r} matched multiple lines "
                f"(>= {len(matches)}); add a line locator to disambiguate"
            ),
        )
    return matches[0]


def extract_excerpt(
    document_bytes: bytes,
    extension: str,
    section: Optional[str],
    line: Optional[int],
) -> str:
    """Return the deterministic excerpt per schemas.md §5.4.

    Raises CitationResolutionError with a specific code/message on failure.

    Inputs:
      document_bytes — raw bytes as read via Path.read_bytes().
      extension      — ".md" or ".txt" (used by §5.5 for section resolution).
      section        — optional section identifier; used only when `line` is None.
      line           — optional 1-based line number; authoritative when present.
    """
    text = _decode_document(document_bytes)
    lines = text.splitlines()  # step 2 — terminator-free, \r\n / \r / \n normalized.

    # Step 3 — determine anchor L (1-based).
    if line is not None:
        try:
            L = int(line)
        except (TypeError, ValueError):
            raise CitationResolutionError(
                ERROR_LOCATOR_OUT_OF_RANGE,
                f"line locator must be an integer; got {line!r}",
            )
        if L < 1:
            raise CitationResolutionError(
                ERROR_LOCATOR_OUT_OF_RANGE,
                f"line locator {line!r} must be >= 1",
            )
    elif section is not None and str(section).strip() != "":
        L = resolve_section(lines, extension, section)
    else:
        raise CitationResolutionError(
            ERROR_LOCATOR_MISSING,
            "citation has neither a non-empty `section` nor a `line`; at least one is required",
        )

    # Step 4 — compute window size N.
    if L > len(lines):
        raise CitationResolutionError(
            ERROR_LOCATOR_OUT_OF_RANGE,
            f"line locator {L} is past end of document ({len(lines)} lines)",
        )
    anchor_index = L - 1  # 0-based
    if lines[anchor_index].strip() == "":
        raise CitationResolutionError(
            ERROR_BLANK_ANCHOR,
            f"anchor at line {L} is blank; citations must point at non-blank content",
        )
    k = anchor_index
    max_k = anchor_index + 10  # 10-line cap
    while k < len(lines) and k < max_k and lines[k].strip() != "":
        k += 1
    # N = k - anchor_index; guaranteed in [1, 10] by the blank-anchor check and the cap.

    # Step 5 — join with literal "\n", no trim, no trailing newline.
    return "\n".join(lines[anchor_index:k])


# ---------------------------------------------------------------------------
# Convenience entry point: verify_citation
#
# The ingest pass (Phase 2) calls this to populate citation_excerpt on a
# fresh citation; the gate (Phase 5) calls this to re-run §5.4 and byte-equal
# check the stored excerpt. Both use the same verify_citation function.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class VerificationResult:
    """Result of verify_citation.

    Fields:
      ok             — True if every check passed.
      excerpt        — freshly-extracted excerpt (string) when extraction succeeded;
                       None if extraction itself failed before producing text.
      error_code     — machine-readable failure code (one of the ERROR_* constants);
                       None on success.
      error_message  — human-readable failure explanation; None on success.
      warnings       — tuple of non-fatal notes (e.g., line-vs-section mismatch).
    """

    ok: bool
    excerpt: Optional[str] = None
    error_code: Optional[str] = None
    error_message: Optional[str] = None
    warnings: Tuple[str, ...] = ()


def verify_citation(
    citation: dict,
    formal_doc: dict,
    root: Path,
) -> VerificationResult:
    """Verify a citation record against its FORMAL_DOC record.

    Performs, in order:
      1. Reads the document at (root / citation['document']) as raw bytes.
      2. Verifies the live SHA-256 equals formal_doc['document_sha256'] (if
         present) and citation['document_sha256'] (if present). Mismatches
         produce hash_mismatch.
      3. If both `line` and `section` are present and they resolve to
         different line numbers, emits a non-fatal warning; `line` wins
         per §5.4 step 3.
      4. Extracts the excerpt per §5.4.
      5. If citation['citation_excerpt'] is present, byte-compares it with
         the freshly-extracted excerpt; mismatch produces excerpt_mismatch.

    Arguments:
      citation   — parsed citation dict (per schemas.md §5.1).
      formal_doc — parsed FORMAL_DOC dict (per schemas.md §4.1).
      root       — filesystem root used to resolve citation['document'].

    Returns a VerificationResult. Never raises CitationResolutionError —
    any such error becomes a result with ok=False and the appropriate code.
    """
    warnings: List[str] = []

    source_path = citation.get("document") or formal_doc.get("source_path")
    if not source_path:
        return VerificationResult(
            ok=False,
            error_code=ERROR_DOCUMENT_NOT_FOUND,
            error_message="citation has no 'document' field and formal_doc has no 'source_path'",
        )

    # BUG-011 (HIGH) from the v1.5.6 codex recheck: Path(root) / source_path
    # silently discards root when source_path is absolute (Python's
    # Path.__truediv__ semantics), and `../` traversal can escape root via
    # otherwise-valid relative paths. A tampered manifest could turn this
    # into an out-of-tree file-read primitive. Resolve both sides and
    # confirm containment before reading bytes. .resolve() also follows
    # symlinks, so symlink-escape is rejected here too.
    root_resolved = Path(root).resolve()
    doc_path_unresolved = Path(root) / source_path
    doc_path = doc_path_unresolved.resolve()
    try:
        doc_path.relative_to(root_resolved)
    except ValueError:
        return VerificationResult(
            ok=False,
            error_code=ERROR_DOCUMENT_OUT_OF_ROOT,
            error_message=(
                f"document {source_path!r} resolves to {doc_path}, which is "
                f"outside repository root {root_resolved}"
            ),
        )

    try:
        document_bytes = doc_path.read_bytes()
    except FileNotFoundError:
        return VerificationResult(
            ok=False,
            error_code=ERROR_DOCUMENT_NOT_FOUND,
            error_message=f"document {source_path!r} not found at {doc_path}",
        )
    except OSError as exc:
        return VerificationResult(
            ok=False,
            error_code=ERROR_DOCUMENT_NOT_FOUND,
            error_message=f"could not read document {source_path!r}: {exc}",
        )

    actual_sha = hashlib.sha256(document_bytes).hexdigest()
    formal_sha = formal_doc.get("document_sha256")
    if formal_sha and formal_sha != actual_sha:
        return VerificationResult(
            ok=False,
            error_code=ERROR_HASH_MISMATCH,
            error_message=(
                f"document {source_path!r} SHA-256 mismatch: "
                f"formal_doc says {formal_sha}, file is {actual_sha}"
            ),
        )
    cited_sha = citation.get("document_sha256")
    if cited_sha and cited_sha != actual_sha:
        return VerificationResult(
            ok=False,
            error_code=ERROR_HASH_MISMATCH,
            error_message=(
                f"citation document_sha256 {cited_sha} does not match live "
                f"document SHA {actual_sha}"
            ),
        )

    extension = doc_path.suffix.lower()
    section = citation.get("section")
    line = citation.get("line")

    # §5.4 step 3 — cross-check `section` against `line` when both are present.
    if line is not None and section is not None and str(section).strip() != "":
        try:
            text = _decode_document(document_bytes)
            section_line = resolve_section(text.splitlines(), extension, section)
        except CitationResolutionError:
            section_line = None
        if section_line is not None and section_line != int(line):
            warnings.append(
                f"line {line} and section {section!r} disagree: section resolves to line "
                f"{section_line}; line wins per schemas.md §5.4"
            )

    try:
        fresh = extract_excerpt(document_bytes, extension, section, line)
    except CitationResolutionError as exc:
        return VerificationResult(
            ok=False,
            error_code=exc.code,
            error_message=exc.message,
            warnings=tuple(warnings),
        )

    stored = citation.get("citation_excerpt")
    if stored is not None and stored != fresh:
        return VerificationResult(
            ok=False,
            excerpt=fresh,
            error_code=ERROR_EXCERPT_MISMATCH,
            error_message=(
                "stored citation_excerpt is not byte-equal to the deterministic "
                "extraction per schemas.md §5.4"
            ),
            warnings=tuple(warnings),
        )

    return VerificationResult(ok=True, excerpt=fresh, warnings=tuple(warnings))
