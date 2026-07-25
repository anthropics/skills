"""Shared block parser for the diff/patch revision mode toolchain (#89 Item 7 Slice A).

Normative source: `docs/design/2026-06-10-390-diff-patch-revision-mode-spec.md`
§3.1 (block segmentation, marker grammar, malformed-state rules,
unsupported-construct rejection). Both `ars_anchorize_draft.py` and
`ars_apply_revision_patch.py` import this module so segmentation can never
drift between the stamping side and the splicing side.

Design constraints the implementation must not violate:

  - **Fail-closed, never guess.** Anything the line-based scan cannot
    classify into the §3.1 supported block classes raises
    ``BlockParseError`` naming the construct. Mis-anchoring would silently
    misroute patches; a loud stop is the contract.
  - **Byte-span fidelity.** Blocks carry character offsets into the
    original text (UTF-8 decoded, no newline translation) so the apply
    script can splice the original byte stream. The parser never
    re-serializes content.
  - **Hash normalization is read-side only** (§3.2): CRLF→LF, marker line
    excluded, block-level leading/trailing blank lines stripped, intra-line
    whitespace untouched. Normalized text exists for hash computation and
    is never written back.

Supported block classes (§3.1, closed list): fenced code, ATX heading,
table run, list run, blockquote run, plain text run, plus skipped YAML
frontmatter. Setext-underline shapes, line-initial raw-HTML openers
(detector subset: ``^</?[A-Za-z]``, NOT full CommonMark HTML-block
coverage — spec §10 R3 P2 advisory), and footnote definitions are
rejected by name.
"""
from __future__ import annotations

import hashlib
import os
import re
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

MARKER_RE = re.compile(r"^<!--block:(B\d{4,})-->$")
MARKER_PREFIX = "<!--block:"

_FENCE_OPEN_RE = re.compile(r"^ {0,3}(`{3,}|~{3,})(.*)$")
_ATX_HEADING_RE = re.compile(r"^ {0,3}#{1,6}(\s|$)")
_TABLE_LINE_RE = re.compile(r"^ {0,3}\|")
_LIST_START_RE = re.compile(r"^ {0,3}(?:[-*+]\s|\d{1,9}[.)]\s)")
_BLOCKQUOTE_RE = re.compile(r"^ {0,3}>")
_SETEXT_UNDERLINE_RE = re.compile(r"^ {0,3}(=+|-+)\s*$")
_RAW_HTML_OPENER_RE = re.compile(r"^ {0,3}</?[A-Za-z]")
_FOOTNOTE_DEF_RE = re.compile(r"^ {0,3}\[\^[^\]]*\]:")

BLOCK_ID_FORMAT = "B{:04d}"


class BlockParseError(ValueError):
    """Raised on any document the parser refuses to classify (§3.1).

    ``kind`` is a stable machine-readable failure class; ``line_no`` is
    1-based; ``hint`` is the human repair hint the spec requires for
    orphan markers and friends.
    """

    def __init__(self, kind: str, line_no: int, message: str, hint: str = ""):
        self.kind = kind
        self.line_no = line_no
        self.hint = hint
        super().__init__(f"line {line_no}: {message}" + (f" (hint: {hint})" if hint else ""))


@dataclass
class Block:
    """One §3.1 block: marker (optional) + content lines, with char spans."""

    kind: str  # fence | heading | table | list | blockquote | text
    block_id: str | None
    marker_span: tuple[int, int] | None  # char span of the marker line incl. EOL
    span: tuple[int, int]  # char span of the content lines incl. trailing EOL (if present)
    first_line: str  # first content line, EOL stripped (manifest excerpt source)
    normalized_text: str = field(repr=False, default="")
    norm_hash: str = ""

    @property
    def full_start(self) -> int:
        return self.marker_span[0] if self.marker_span is not None else self.span[0]


@dataclass
class ParsedDocument:
    text: str
    frontmatter_span: tuple[int, int] | None
    blocks: list[Block]

    def block_by_id(self) -> dict[str, Block]:
        return {b.block_id: b for b in self.blocks if b.block_id is not None}

    def next_fresh_id_num(self) -> int:
        nums = [int(b.block_id[1:]) for b in self.blocks if b.block_id is not None]
        return (max(nums) + 1) if nums else 1


def split_lines_keepends(text: str) -> list[str]:
    """Split on ``\\n`` only, keeping line endings.

    ``str.splitlines`` also splits on \\x0b/\\x0c/\\u2028/..., which would
    desynchronize char offsets from markdown line semantics. A trailing
    segment without a newline is kept as the final line.
    """
    lines = text.split("\n")
    out = [line + "\n" for line in lines[:-1]]
    if lines[-1] != "":
        out.append(lines[-1])
    return out


def _strip_eol(line: str) -> str:
    return line.rstrip("\n").rstrip("\r")


def _is_blank(line: str) -> bool:
    return _strip_eol(line).strip() == ""


def normalize_block_text(lines: list[str]) -> str:
    """§3.2 hash normalization: LF endings, strip block-level blank edges."""
    norm = [_strip_eol(line) for line in lines]
    while norm and norm[0].strip() == "":
        norm.pop(0)
    while norm and norm[-1].strip() == "":
        norm.pop()
    return "\n".join(norm)


def block_hash(normalized_text: str) -> str:
    """First 12 hex chars of SHA-256 over the normalized text (§3.2)."""
    return hashlib.sha256(normalized_text.encode("utf-8")).hexdigest()[:12]


def base_draft_hash(raw: bytes) -> str:
    """First 12 hex chars of SHA-256 over the entire file's raw bytes (§3.2)."""
    return hashlib.sha256(raw).hexdigest()[:12]


def atomic_write_bytes(path: Path, data: bytes) -> None:
    """Temp-file + atomic rename write, shared by the Slice A toolchain.

    An interrupted write leaves no partial artifact (§3.3); the temp file
    is removed on any failure before the rename.
    """
    fd, tmp_name = tempfile.mkstemp(dir=str(path.parent), prefix=f".{path.name}.")
    try:
        with os.fdopen(fd, "wb") as fh:
            fh.write(data)
        os.replace(tmp_name, path)
    except BaseException:
        if os.path.exists(tmp_name):
            os.unlink(tmp_name)
        raise


def _classify_start(stripped: str) -> str:
    """Class of the block starting at a non-blank, non-marker line."""
    if _FENCE_OPEN_RE.match(stripped):
        return "fence"
    if _ATX_HEADING_RE.match(stripped):
        return "heading"
    if _TABLE_LINE_RE.match(stripped):
        return "table"
    if _LIST_START_RE.match(stripped):
        return "list"
    if _BLOCKQUOTE_RE.match(stripped):
        return "blockquote"
    return "text"


def _reject_unsupported_text_line(stripped: str, line_no: int, first_of_run: bool) -> None:
    """§3.1 unsupported-construct rejection, by name, inside a text run."""
    if not first_of_run and _SETEXT_UNDERLINE_RE.match(stripped):
        raise BlockParseError(
            "unsupported_construct:setext_underline",
            line_no,
            "setext-underline shape (===/--- directly under a non-blank line) is unsupported",
            "use an ATX heading (#/##) instead",
        )
    if _RAW_HTML_OPENER_RE.match(stripped):
        raise BlockParseError(
            "unsupported_construct:raw_html_block",
            line_no,
            "line-initial raw-HTML opener is unsupported (detector subset: ^</?[A-Za-z])",
            "raw HTML blocks cannot use patch mode yet",
        )
    if _FOOTNOTE_DEF_RE.match(stripped):
        raise BlockParseError(
            "unsupported_construct:footnote_definition",
            line_no,
            "footnote-definition opener ([^...]:) is unsupported",
            "footnote definitions cannot use patch mode yet",
        )


def parse_document(text: str, *, fragment: bool = False) -> ParsedDocument:
    """Parse a draft (or, with ``fragment=True``, a patch ``new_text``).

    Fragment mode differences: no YAML-frontmatter detection (frontmatter
    is never patchable, §3.1, so a fragment starting with ``---`` is just
    an unsupported shape), and any ``<!--block:`` marker line is rejected
    (ID assignment is the apply script's exclusive authority, §3.2).
    """
    lines = split_lines_keepends(text)
    n = len(lines)
    offsets = [0] * (n + 1)
    for i, line in enumerate(lines):
        offsets[i + 1] = offsets[i] + len(line)

    blocks: list[Block] = []
    frontmatter_span: tuple[int, int] | None = None
    i = 0

    if not fragment and n > 0 and _strip_eol(lines[0]) == "---":
        j = 1
        while j < n and _strip_eol(lines[j]) != "---":
            j += 1
        if j >= n:
            raise BlockParseError(
                "unterminated_frontmatter", 1, "YAML frontmatter fence is never closed"
            )
        frontmatter_span = (offsets[0], offsets[j + 1])
        i = j + 1

    pending_marker: tuple[int, str] | None = None  # (line index, block id)

    def _finish_block(kind: str, start_line: int, end_line: int) -> None:
        nonlocal pending_marker
        marker_span = None
        block_id = None
        if pending_marker is not None:
            m_idx, block_id = pending_marker
            marker_span = (offsets[m_idx], offsets[m_idx + 1])
            pending_marker = None
        content_lines = lines[start_line:end_line]
        normalized = normalize_block_text(content_lines)
        blocks.append(
            Block(
                kind=kind,
                block_id=block_id,
                marker_span=marker_span,
                span=(offsets[start_line], offsets[end_line]),
                first_line=_strip_eol(lines[start_line]),
                normalized_text=normalized,
                norm_hash=block_hash(normalized),
            )
        )

    while i < n:
        stripped = _strip_eol(lines[i])

        if _is_blank(lines[i]):
            if pending_marker is not None:
                raise BlockParseError(
                    "orphan_marker",
                    pending_marker[0] + 1,
                    f"marker {pending_marker[1]} is attached to nothing (blank line follows)",
                    "remove the marker line or re-run anchorize",
                )
            i += 1
            continue

        marker_match = MARKER_RE.match(stripped)
        if marker_match:
            if fragment:
                raise BlockParseError(
                    "marker_in_fragment",
                    i + 1,
                    "new_text must not contain <!--block:--> markers (§3.2)",
                )
            if pending_marker is not None:
                raise BlockParseError(
                    "marker_stack",
                    pending_marker[0] + 1,
                    f"marker {pending_marker[1]} is followed by another marker line",
                    "each marker labels exactly one block",
                )
            pending_marker = (i, marker_match.group(1))
            i += 1
            if i >= n:
                raise BlockParseError(
                    "orphan_marker",
                    pending_marker[0] + 1,
                    f"marker {pending_marker[1]} is attached to nothing (end of file)",
                    "remove the marker line or re-run anchorize",
                )
            continue

        kind = _classify_start(stripped)
        start = i

        if kind == "fence":
            fence_match = _FENCE_OPEN_RE.match(stripped)
            fence_str = fence_match.group(1)
            fence_char = fence_str[0]
            fence_len = len(fence_str)
            close_re = re.compile(r"^ {0,3}(" + re.escape(fence_char) + r"{" + str(fence_len) + r",})\s*$")
            i += 1
            while i < n and not close_re.match(_strip_eol(lines[i])):
                i += 1
            if i >= n:
                raise BlockParseError(
                    "unterminated_fence",
                    start + 1,
                    "fenced code block has no matching closing fence",
                    "close the fence; the parser does not guess at EOF-terminated fences",
                )
            i += 1  # include the closing fence line

        elif kind == "heading":
            i += 1

        elif kind == "table":
            while i < n and _TABLE_LINE_RE.match(_strip_eol(lines[i])):
                i += 1

        elif kind == "list":
            i += 1
            while i < n:
                cur = _strip_eol(lines[i])
                if _is_blank(lines[i]):
                    # A blank stays inside the run only when the next
                    # non-blank line continues the list (loose lists).
                    k = i
                    while k < n and _is_blank(lines[k]):
                        k += 1
                    if k < n:
                        nxt = _strip_eol(lines[k])
                        if not MARKER_RE.match(nxt) and (
                            _LIST_START_RE.match(nxt)
                            or (nxt[:1] in (" ", "\t") and nxt.strip() != "")
                        ):
                            i = k
                            continue
                    break
                if _LIST_START_RE.match(cur) or (cur[:1] in (" ", "\t")):
                    i += 1
                    continue
                break

        elif kind == "blockquote":
            while i < n and _BLOCKQUOTE_RE.match(_strip_eol(lines[i])):
                i += 1

        else:  # text run
            _reject_unsupported_text_line(stripped, i + 1, first_of_run=True)
            i += 1
            while i < n:
                cur_raw = lines[i]
                cur = _strip_eol(cur_raw)
                if _is_blank(cur_raw) or MARKER_RE.match(cur):
                    break
                if _classify_start(cur) != "text":
                    break
                _reject_unsupported_text_line(cur, i + 1, first_of_run=False)
                i += 1

        _finish_block(kind, start, i)

    # Unreachable invariant, not a third orphan-marker code path: a marker
    # before a blank line is rejected in the blank branch, and a marker at
    # EOF is rejected right after it is consumed.
    assert pending_marker is None

    seen: dict[str, int] = {}
    for b in blocks:
        if b.block_id is None:
            continue
        if b.block_id in seen:
            raise BlockParseError(
                "duplicate_block_id",
                0,
                f"block ID {b.block_id} appears more than once",
                "duplicates can only arise from hand-editing; re-anchorize from a clean draft",
            )
        seen[b.block_id] = 1

    return ParsedDocument(text=text, frontmatter_span=frontmatter_span, blocks=blocks)


def segment_fragment(new_text: str) -> list[Block]:
    """Segment a patch op's ``new_text`` into blocks (§3.2).

    Returns the parsed ``Block`` objects (spans are into ``new_text``),
    using the same normative segmentation as the document parser. Raises
    ``BlockParseError`` on anything the parser refuses (unsupported
    constructs, embedded markers) and on an empty/blank fragment.
    """
    parsed = parse_document(new_text, fragment=True)
    if not parsed.blocks:
        raise BlockParseError("empty_fragment", 1, "new_text contains no block content")
    return parsed.blocks
