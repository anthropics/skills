"""Bounded confidentiality gate for a public tree (standard library only).

Supply a private JSON policy outside the public tree for corpus-derived denylist
tokens and source_workbook_names. Never publish that policy or the source corpus.
The bundled policy contains only public documentation hosts and one exact,
synthetic positive-control fixture exclusion. No test directory is skipped.

This mechanical sweep supports confidentiality layers 2, 3 and 5; a separate
review must still check whether example geography, counts and timing combine
to identify a customer. Arbitrary binary formats are counted, not interpreted.
Archive text is scanned without extraction, including metadata and nested ZIPs.
"""

from __future__ import annotations

import argparse
from collections.abc import Callable
from dataclasses import dataclass, field
from hashlib import sha256
import html
import io
import ipaddress
import json
import os
from pathlib import Path, PurePosixPath
import re
import tokenize
import zipfile
import zlib

try:
    from .publication import structural_guid_spans
except ImportError:  # Direct authoring-tool CLI invocation.
    from publication import structural_guid_spans


TEXT_SUFFIXES = {".md", ".markdown", ".json", ".py", ".csv", ".xml", ".svg", ".txt", ".rels", ".ini"}
ARCHIVE_SUFFIXES = {".zip", ".xlsx"}
FILE_SUFFIXES = TEXT_SUFFIXES | ARCHIVE_SUFFIXES | {".png", ".jpg", ".jpeg", ".gif", ".pdf", ".pyc", ".drawio", ".exe", ".dll", ".pth"}
# Offline IANA root-zone snapshot, obtained from its public TLD data endpoint.
# Explicit URL hosts are inspected even when their suffix is not delegated.
PUBLIC_TLDS = {line.strip() for line in Path(__file__).with_name("public-tlds.txt").read_text(encoding="utf-8").splitlines()
               if line and not line.startswith("#")} | {"internal", "local", "corp", "lan"}
DEFAULT_LIMITS = {
    "max_entry_bytes": 8 * 1024 * 1024,
    "max_total_bytes": 64 * 1024 * 1024,
    "max_archive_entries": 4096,
    "max_archive_depth": 3,
    "max_compression_ratio": 200,
    "max_files": 10000,
    "max_matches": 10000,
}
# The exact distributed OFL text carries public author contacts. This is not a
# general email/domain allowlist; private identifiers/literal rules still run.
PUBLIC_OFL_SHA256 = "19e7e97ffc31e58fa0e54919b8189b2ddcc6fd75539f387e2822b107b6a51423"
PUBLIC_OFL_PATHS = {"tooling/fonts/lato/OFL.txt"}
for _skill in json.loads(Path(__file__).with_name("domain-registry.json").read_bytes())["skills"]:
    _name = _skill["name"]
    PUBLIC_OFL_PATHS.update({f"{_name}/scripts/fonts/lato/OFL.txt",
                            f"bundles/{_name}.skill!{_name}/scripts/fonts/lato/OFL.txt"})
DOMAIN = re.compile(r"(?i)(?<![\w@.-])(?:[^\W_](?:[^\W_]|-){0,62}\.)+(?:[^\W\d_]{2,63}|xn--[a-z0-9-]{2,59})\b")
EMAIL = re.compile(r"(?i)\b[a-z0-9._%+-]+@((?:[a-z0-9-]+\.)+[a-z]{2,63})\b")
IPV4 = re.compile(r"(?<![\w.])(?:\d{1,3}\.){3}\d{1,3}(?!\w|\.\w)")
IPV6 = re.compile(r"(?<![\w:])(?:[0-9a-fA-F]{0,4}:){2,}[0-9a-fA-F:.]*(?![\w:]|\.\w)")
IDENTIFIERS = {
    "local-user-path": re.compile(r"(?i)(?:[a-z]:[\\/]Users[\\/]|/Users/|/home/)[a-z0-9_.-]+(?:[\\/][^\s<>\"']*)?"),
    "cloud-account-id": re.compile(r"(?<![\w])\d{12}(?![\w])"),
    "cloud-project-id": re.compile(r"(?i)\b(?:project[_-]?id\s*[\"']?\s*[:=]\s*[\"']?|projects/)([a-z][a-z0-9-]{4,62}[a-z0-9])\b"),
    "cloud-subscription-id": re.compile(r"(?i)\b(?:subscription[_-]?id\s*[\"']?\s*[:=]\s*[\"']?|subscriptions/)([a-f0-9]{8}(?:-[a-f0-9]{4}){3}-[a-f0-9]{12})\b"),
    "cloud-tenant-id": re.compile(r"(?i)\btenant[_-]?id\s*[\"']?\s*[:=]\s*[\"']?([a-f0-9]{8}(?:-[a-f0-9]{4}){3}-[a-f0-9]{12})\b"),
    "cloud-ocid": re.compile(r"(?i)\bocid1\.[a-z0-9._-]{10,}\b"),
}


@dataclass(frozen=True)
class AnonymisationMatch:
    path: str = field(repr=False)
    rule: str
    line: int
    excerpt: str = "[REDACTED]"


@dataclass(frozen=True)
class ScanIssue:
    path: str = field(repr=False)
    rule: str


@dataclass
class AnonymisationReport:
    matches: list[AnonymisationMatch] = field(default_factory=list, repr=False)
    issues: list[ScanIssue] = field(default_factory=list, repr=False)
    excluded_paths: list[str] = field(default_factory=list, repr=False)
    scanned_files: int = 0
    scanned_texts: int = 0
    binary_entries: int = 0
    _path_is_sensitive: Callable[[str], bool] = field(default=lambda path: True, repr=False)

    @property
    def match_count(self) -> int:
        return len(self.matches)

    @property
    def complete(self) -> bool:
        return not self.issues

    @property
    def clean(self) -> bool:
        return self.complete and not self.matches

    def summary(self) -> str:
        """Safe console report: never print source excerpts or sensitive paths."""
        def safe(path: str) -> str:
            return "[REDACTED PATH]" if self._path_is_sensitive(path) else path

        lines = [f"matches={self.match_count} issues={len(self.issues)} complete={str(self.complete).lower()} "
                 f"files={self.scanned_files} texts={self.scanned_texts} binary={self.binary_entries} "
                 f"excluded={len(self.excluded_paths)}"]
        lines.extend(f"{safe(item.path)}:{item.line} rule={item.rule} {item.excerpt}" for item in self.matches)
        lines.extend(f"{safe(item.path)} rule={item.rule}" for item in self.issues)
        lines.extend(f"excluded-fixture={safe(path)}" for path in self.excluded_paths)
        return "\n".join(lines)


def _load_policy(path: Path | None) -> dict:
    data = json.loads((path or Path(__file__).with_name("anonymisation-policy.json")).read_text(encoding="utf-8"))
    keys = {"denylist", "source_workbook_names", "allowed_domains", "technical_identifiers", "excluded_fixture_paths", "limits"}
    if not isinstance(data, dict) or set(data) - keys:
        raise ValueError("invalid anonymisation policy keys")
    for key in keys - {"limits"}:
        items = data.setdefault(key, [])
        if not isinstance(items, list) or any(not isinstance(item, str) or not item.strip() for item in items):
            raise ValueError("invalid anonymisation policy list")
    for path_name in data["excluded_fixture_paths"]:
        path_obj = PurePosixPath(path_name)
        if (path_name != path_obj.as_posix() or path_obj.is_absolute() or ".." in path_obj.parts
                or len(path_obj.parts) != 3 or path_obj.parts[:2] != ("tests", "fixtures")
                or not path_obj.name.startswith("forbidden-sample") or path_obj.suffix != ".txt"
                or any(character in path_name for character in "*?[]\\")):
            raise ValueError("only exact synthetic positive-control fixture paths may be excluded")
    limits = data.setdefault("limits", {})
    if (not isinstance(limits, dict) or set(limits) - set(DEFAULT_LIMITS)
            or any(type(value) is not int or value <= 0 for value in limits.values())):
        raise ValueError("invalid anonymisation scan limits")
    data["limits"] = DEFAULT_LIMITS | limits
    for domain in data["allowed_domains"]:
        if not DOMAIN.fullmatch(domain) or "*" in domain:
            raise ValueError("allowed_domains must contain exact DNS hosts")
    return data


def _example_domain(host: str) -> bool:
    host = host.lower().rstrip(".")
    return (host in {"example.com", "example.org", "example.net", "localhost"}
            or any(host.endswith("." + suffix) for suffix in
                   ("example.com", "example.org", "example.net", "example", "test", "invalid", "localhost")))


class _Scanner:
    def __init__(self, policy: dict):
        self.policy = policy
        self.limits = policy["limits"]
        self.report = AnonymisationReport()
        self.bytes_read = 0
        self.archive_entries = 0
        self.literal_rules = [(rule, re.compile(re.escape(token), re.IGNORECASE))
                              for key, rule in (("denylist", "denylist-token"),
                                                ("source_workbook_names", "private-source-workbook"))
                              for token in policy[key]]
        # Diagnostic masking reruns the pure detector against each complete
        # path, independent of retained matches, issue type or traversal order.
        self.report._path_is_sensitive = lambda path: any(self.rules_for_line(path))

    def issue(self, path: str, rule: str) -> None:
        self.report.issues.append(ScanIssue(path, rule))

    def record(self, path: str, rule: str, line: int) -> None:
        if len(self.report.matches) < self.limits["max_matches"]:
            item = AnonymisationMatch(path, rule, line)
            if item not in self.report.matches:
                self.report.matches.append(item)
        elif not any(item.rule == "match-limit" for item in self.report.issues):
            self.issue(path, "match-limit")

    def check_line(self, text: str, path: str, line: int, domains: bool = True) -> None:
        for rule in self.rules_for_line(text, domains):
            self.record(path, rule, line)

    def rules_for_line(self, text: str, domains: bool = True):
        """Yield detection rules without changing report state or consuming limits."""
        text = html.unescape(text)
        for rule, pattern in list(IDENTIFIERS.items()) + self.literal_rules:
            if pattern.search(text):
                yield rule
        for found in EMAIL.finditer(text):
            if not _example_domain(found.group(1)):
                yield "email"
        for pattern in (IPV4, IPV6):
            for found in pattern.finditer(text):
                candidate = found.group().rstrip(".")
                # A single final colon may be prose punctuation; compressed
                # IPv6 endings (::) remain part of the address and are validated.
                if candidate.endswith(":") and not candidate.endswith("::"):
                    candidate = candidate[:-1]
                try:
                    address = ipaddress.ip_address(candidate)
                    if address.is_global and not address.is_reserved:
                        yield "public-ip"
                except ValueError:
                    pass
        if domains:
            for found in DOMAIN.finditer(text):
                try:
                    host = found.group().lower().encode("idna").decode("ascii")
                except UnicodeError:
                    yield "non-example-domain"
                    continue
                url_host = text[:found.start()].endswith(("://", "//"))
                if not url_host and (host.rsplit(".", 1)[-1] not in PUBLIC_TLDS
                                     or host in self.policy["technical_identifiers"]):
                    continue
                if (not _example_domain(host) and host not in self.policy["allowed_domains"]
                        and (url_host or Path(host).suffix not in FILE_SUFFIXES)):
                    yield "non-example-domain"

    def text(self, raw: bytes, path: str, required: bool) -> None:
        try:
            if raw.startswith((b"\xff\xfe\x00\x00", b"\x00\x00\xfe\xff")):
                encoding = "utf-32"
            else:
                encoding = "utf-16" if raw.startswith((b"\xff\xfe", b"\xfe\xff")) else "utf-8-sig"
            try:
                content = raw.decode(encoding)
            except UnicodeError:
                controls = sum(value < 32 and value not in (9, 10, 13) for value in raw)
                if encoding != "utf-8-sig" or b"\x00" in raw or controls > len(raw) * 0.05:
                    raise
                content = raw.decode("cp1252")
            if "\x00" in content:
                raise UnicodeError("binary data")
        except UnicodeError:
            if required:
                self.issue(path, "text-unreadable")
            else:
                self.report.binary_entries += 1
            return
        self.report.scanned_texts += 1
        if path in PUBLIC_OFL_PATHS and sha256(raw).hexdigest() == PUBLIC_OFL_SHA256:
            # A separate pass keeps every private-policy and identifier rule.
            for line, text in enumerate(content.splitlines(), 1):
                for rule, pattern in list(IDENTIFIERS.items()) + self.literal_rules:
                    if pattern.search(html.unescape(text)):
                        self.record(path, rule, line)
            return
        if "!" in path:
            part = path.rsplit("!", 1)[-1]
            spans = structural_guid_spans(content, part)
            # Explicit private policy tokens remain forbidden even in a uid.
            for line, text in enumerate(content.splitlines(), 1):
                for rule, pattern in self.literal_rules:
                    if pattern.search(text):
                        self.record(path, rule, line)
            for start, end in sorted(spans, reverse=True):
                content = content[:start] + "X" * (end - start) + content[end:]
        is_python = path.endswith(".py")
        for line, text in enumerate(content.splitlines(), 1):
            self.check_line(text, path, line, domains=not is_python)
        # A dotted Python expression is not a DNS host; strings and comments can
        # contain one. Other identifier/literal rules still inspect all bytes.
        if is_python:
            try:
                for token in tokenize.generate_tokens(io.StringIO(content).readline):
                    if token.type in {tokenize.STRING, tokenize.COMMENT, getattr(tokenize, "FSTRING_MIDDLE", -1)}:
                        for offset, text in enumerate(token.string.splitlines()):
                            self.check_line(text, path, token.start[0] + offset)
            except (tokenize.TokenError, IndentationError, SyntaxError):
                self.issue(path, "python-tokenization-failed")

    def reserve(self, size: int, path: str) -> bool:
        if size > self.limits["max_entry_bytes"]:
            self.issue(path, "entry-size-limit")
            return False
        if self.bytes_read + size > self.limits["max_total_bytes"]:
            self.issue(path, "total-size-limit")
            return False
        self.bytes_read += size
        return True

    def archive(self, raw: bytes, path: str, depth: int) -> None:
        if depth > self.limits["max_archive_depth"]:
            self.issue(path, "archive-depth-limit")
            return
        try:
            with zipfile.ZipFile(io.BytesIO(raw)) as archive:
                for entry in archive.infolist():
                    self.archive_entries += 1
                    entry_path = path + "!" + entry.filename
                    self.check_line(entry.filename, entry_path, 0)
                    if self.archive_entries > self.limits["max_archive_entries"]:
                        self.issue(path, "archive-entry-limit")
                        break
                    if entry.is_dir():
                        continue
                    if entry.file_size / max(entry.compress_size, 1) > self.limits["max_compression_ratio"]:
                        self.issue(entry_path, "archive-compression-limit")
                        continue
                    if not self.reserve(entry.file_size, entry_path):
                        continue
                    try:
                        with archive.open(entry) as stream:
                            data = stream.read(self.limits["max_entry_bytes"] + 1)
                        if len(data) != entry.file_size:
                            self.issue(entry_path, "archive-size-mismatch")
                            continue
                        suffix = PurePosixPath(entry.filename).suffix.lower()
                        if suffix in ARCHIVE_SUFFIXES or data.startswith(b"PK\x03\x04"):
                            self.archive(data, entry_path, depth + 1)
                        else:
                            self.text(data, entry_path, suffix in TEXT_SUFFIXES)
                    except (OSError, RuntimeError, ValueError, zipfile.BadZipFile, NotImplementedError, EOFError, zlib.error):
                        self.issue(entry_path, "archive-entry-unreadable")
        except (OSError, ValueError, zipfile.BadZipFile, NotImplementedError):
            self.issue(path, "archive-unreadable")


def scan_tree(root: Path, policy: Path | None = None) -> AnonymisationReport:
    """Scan the complete tree; line 0 means a filename/path match.

    Policy and traversal errors cannot yield a clean result. Exclusions apply
    only to exact, explicitly named positive-control fixtures at the root.
    """
    root = Path(root).resolve(strict=True)
    if not root.is_dir():
        raise ValueError("scan root must be a directory")
    scanner = _Scanner(_load_policy(policy))
    scanner.check_line(root.name, ".", 0)

    def walk_error(error: OSError) -> None:
        scanner.issue("[UNREADABLE PATH]", "tree-unreadable")

    for folder, directories, filenames in os.walk(root, followlinks=False, onerror=walk_error):
        directories.sort()
        for name in directories[:]:
            directory = Path(folder) / name
            path = directory.relative_to(root).as_posix()
            scanner.check_line(path, path, 0)
            if directory.is_symlink():
                scanner.issue(path, "symlink-not-scanned")
                directories.remove(name)
        for name in sorted(filenames):
            file = Path(folder) / name
            path = file.relative_to(root).as_posix()
            if path in scanner.policy["excluded_fixture_paths"]:
                scanner.report.excluded_paths.append(path)
                continue
            scanner.report.scanned_files += 1
            scanner.check_line(path, path, 0)
            if scanner.report.scanned_files > scanner.limits["max_files"]:
                scanner.issue(path, "file-count-limit")
                return scanner.report
            if file.is_symlink():
                scanner.issue(path, "symlink-not-scanned")
                continue
            try:
                size = file.stat().st_size
                if not scanner.reserve(size, path):
                    continue
                with file.open("rb") as stream:
                    raw = stream.read(scanner.limits["max_entry_bytes"] + 1)
                if len(raw) != size:
                    scanner.issue(path, "file-size-changed")
                    continue
                suffix = file.suffix.lower()
                if suffix in ARCHIVE_SUFFIXES or raw.startswith(b"PK\x03\x04"):
                    scanner.archive(raw, path, 1)
                else:
                    scanner.text(raw, path, suffix in TEXT_SUFFIXES)
            except OSError:
                scanner.issue(path, "file-unreadable")
    return scanner.report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("--policy", type=Path, help="external private or bundled public JSON policy")
    args = parser.parse_args()
    try:
        report = scan_tree(args.root, args.policy)
    except (OSError, ValueError):
        print("matches=0 issues=1 complete=false rule=scan-configuration-error")
        return 2
    print(report.summary())
    return 2 if not report.complete else 1 if report.matches else 0


if __name__ == "__main__":
    raise SystemExit(main())
