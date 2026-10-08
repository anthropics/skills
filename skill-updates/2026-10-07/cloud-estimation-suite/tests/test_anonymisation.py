import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import zipfile

import pytest

from tooling.anonymisation import scan_tree

ROOT = Path(__file__).parents[1]
CONTROL = ROOT / "tests/fixtures/forbidden-sample.txt"


@pytest.fixture
def policy(tmp_path):
    path = tmp_path.parent / (tmp_path.name + "-policy.json")
    path.write_text(json.dumps({"denylist": [], "source_workbook_names": []}), encoding="utf-8")
    return path


def test_positive_control_detects_each_identifier_and_redacts_entire_line(tmp_path, policy):
    shutil.copyfile(CONTROL, tmp_path / "control.txt")
    report = scan_tree(tmp_path, policy)
    assert {item.rule for item in report.matches} >= {
        "cloud-account-id", "cloud-project-id", "cloud-subscription-id",
        "cloud-tenant-id", "cloud-ocid", "public-ip", "non-example-domain", "email",
    }
    assert report.complete and not report.clean
    assert all(item.path == "control.txt" and item.line >= 1 for item in report.matches)
    assert all(item.excerpt == "[REDACTED]" for item in report.matches)
    assert report.match_count == len(report.matches) > 0


@pytest.mark.parametrize("extension", ["md", "json", "py", "csv", "xml", "svg", "txt"])
def test_all_public_text_formats_are_scanned(tmp_path, policy, extension):
    account = "123456" + "789012"
    (tmp_path / ("source." + extension)).write_text('value="' + account + '"', encoding="utf-8")
    assert "cloud-account-id" in {item.rule for item in scan_tree(tmp_path, policy).matches}


@pytest.mark.parametrize("extension", ["zip", "xlsx"])
def test_every_archive_text_entry_is_scanned_including_metadata_and_unknown_suffix(tmp_path, policy, extension):
    email = "operator" + "@" + "synthetic-control" + ".internal"
    with zipfile.ZipFile(tmp_path / ("export." + extension), "w") as archive:
        archive.writestr("docProps/custom.xml", "<value>" + email + "</value>")
        archive.writestr("notes.unknown", "first\n" + email)
        archive.writestr("media/icon.png", b"\x89PNG\x00\xff")
    report = scan_tree(tmp_path, policy)
    found = {item.path: item.line for item in report.matches if item.rule == "email"}
    assert found == {"export." + extension + "!docProps/custom.xml": 1,
                     "export." + extension + "!notes.unknown": 2}
    assert report.scanned_texts == 2


def test_archive_recursion_is_bounded_and_nested_content_is_scanned(tmp_path, policy):
    nested = io.BytesIO()
    with zipfile.ZipFile(nested, "w") as archive:
        archive.writestr("hidden.txt", "account=" + "123456" + "789012")
    with zipfile.ZipFile(tmp_path / "outer.zip", "w") as archive:
        archive.writestr("inner.zip", nested.getvalue())
    report = scan_tree(tmp_path, policy)
    assert any(item.path == "outer.zip!inner.zip!hidden.txt" for item in report.matches)
    policy.write_text(json.dumps({"limits": {"max_archive_depth": 1}}), encoding="utf-8")
    report = scan_tree(tmp_path, policy)
    assert not report.complete and not report.clean
    assert any(item.rule == "archive-depth-limit" for item in report.issues)


@pytest.mark.parametrize("limits", [
    {"max_entry_bytes": 16}, {"max_total_bytes": 16},
    {"max_archive_entries": 1}, {"max_compression_ratio": 2},
])
def test_archive_limits_prevent_false_clean_results(tmp_path, policy, limits):
    with zipfile.ZipFile(tmp_path / "large.zip", "w", compression=zipfile.ZIP_DEFLATED) as archive:
        archive.writestr("one.txt", "a" * 4096)
        archive.writestr("two.txt", "b" * 32)
    policy.write_text(json.dumps({"limits": limits}), encoding="utf-8")
    report = scan_tree(tmp_path, policy)
    assert report.issues and not report.complete and not report.clean


def test_broken_archive_and_undecodable_required_text_are_incomplete(tmp_path, policy):
    (tmp_path / "broken.xlsx").write_bytes(b"not an archive")
    (tmp_path / "broken.md").write_bytes(b"\xff\xfe\xff")
    report = scan_tree(tmp_path, policy)
    assert {item.rule for item in report.issues} >= {"archive-unreadable", "text-unreadable"}
    assert not report.clean


def test_private_policy_detects_literals_and_source_names_in_content_and_paths(tmp_path, policy):
    token = "synthetic" + "-private-marker"
    workbook = "synthetic" + "-source.xlsx"
    policy.write_text(json.dumps({"denylist": [token], "source_workbook_names": [workbook]}), encoding="utf-8")
    (tmp_path / "notes.md").write_text(token.upper() + "\n" + workbook, encoding="utf-8")
    with zipfile.ZipFile(tmp_path / "export.zip", "w") as archive:
        archive.writestr(workbook + ".txt", "neutral")
    report = scan_tree(tmp_path, policy)
    assert {item.rule for item in report.matches} >= {"denylist-token", "private-source-workbook"}
    assert any(item.line == 0 for item in report.matches)
    assert token not in report.summary() and workbook not in report.summary()


def test_reserved_examples_private_ips_and_exact_documentation_domains_are_safe(tmp_path, policy):
    (tmp_path / "safe.md").write_text(
        "operator@example.com docs.example.org sub.example.net demo.test name.invalid\n"
        "192.0.2.1 198.51.100.20 203.0.113.5 10.0.0.1 127.0.0.1 2001:db8::1\n"
        "https://aws.amazon.com/architecture/icons/\n",
        encoding="utf-8",
    )
    policy.write_text(json.dumps({"allowed_domains": ["aws.amazon.com"]}), encoding="utf-8")
    report = scan_tree(tmp_path, policy)
    assert report.clean and report.match_count == 0
    assert "matches=0" in report.summary() and "issues=0" in report.summary()


def test_allowlist_does_not_allow_customer_subdomains_or_email_on_documentation_domain(tmp_path, policy):
    host = "aws" + ".amazon.com"
    policy.write_text(json.dumps({"allowed_domains": [host]}), encoding="utf-8")
    (tmp_path / "notes.md").write_text("customer." + host + "\noperator@" + host, encoding="utf-8")
    assert {item.rule for item in scan_tree(tmp_path, policy).matches} >= {"email", "non-example-domain"}


def test_public_ipv6_and_bare_uncommon_domain_are_detected(tmp_path, policy):
    (tmp_path / "notes.md").write_text("2606:" + "4700:4700::1111\n" + "synthetic" + ".museum", encoding="utf-8")
    assert {item.rule for item in scan_tree(tmp_path, policy).matches} >= {"public-ip", "non-example-domain"}


def test_dotted_program_expressions_and_slices_are_not_domains_or_ips(tmp_path, policy):
    (tmp_path / "program.py").write_text(
        'points = coordinates[::2]\nmessage = "Excel.Application scripts.model tasks.dependencies"\n',
        encoding="utf-8",
    )
    assert scan_tree(tmp_path, policy).clean


def test_explicit_technical_field_exception_cannot_allow_url_domain(tmp_path, policy):
    field = "node" + ".id"
    policy.write_text(json.dumps({"technical_identifiers": [field]}), encoding="utf-8")
    (tmp_path / "fields.md").write_text(field, encoding="utf-8")
    assert scan_tree(tmp_path, policy).clean
    (tmp_path / "url.md").write_text("https://" + field, encoding="utf-8")
    assert any(item.rule == "non-example-domain" for item in scan_tree(tmp_path, policy).matches)


def test_url_hosts_are_checked_even_when_suffix_looks_like_a_filename(tmp_path, policy):
    (tmp_path / "urls.md").write_text("https://" + "synthetic" + ".zip", encoding="utf-8")
    assert any(item.rule == "non-example-domain" for item in scan_tree(tmp_path, policy).matches)


def test_fstring_and_unicode_domains_are_scanned(tmp_path, policy):
    (tmp_path / "program.py").write_text('url = f"https://' + 'synthetic' + '.com/{name}"', encoding="utf-8")
    (tmp_path / "urls.md").write_text("https://" + "synth\u00e9tique" + ".com", encoding="utf-8")
    report = scan_tree(tmp_path, policy)
    assert {item.path for item in report.matches if item.rule == "non-example-domain"} == {"program.py", "urls.md"}


def test_domain_in_filename_and_archive_entry_is_detected_and_redacted(tmp_path, policy):
    domain = "synthetic" + ".com"
    (tmp_path / domain).write_text("neutral", encoding="utf-8")
    with zipfile.ZipFile(tmp_path / "export.zip", "w") as archive:
        archive.writestr(domain, "neutral")
    report = scan_tree(tmp_path, policy)
    assert {item.path for item in report.matches if item.rule == "non-example-domain" and item.line == 0} == {domain, "export.zip!" + domain}
    assert domain not in report.summary()


def test_legacy_archive_text_and_xml_entities_are_scanned(tmp_path, policy):
    email = "operator" + "@" + "synthetic-control" + ".internal"
    with zipfile.ZipFile(tmp_path / "export.zip", "w") as archive:
        archive.writestr("legacy.unknown", ("caf\u00e9 " + email).encode("cp1252"))
        archive.writestr("meta.xml", "<name>" + email.replace("@", "&#64;") + "</name>")
        archive.writestr("unicode.xml", ("<name>" + email + "</name>").encode("utf-16"))
    report = scan_tree(tmp_path, policy)
    assert {item.path for item in report.matches if item.rule == "email"} == {"export.zip!legacy.unknown", "export.zip!meta.xml", "export.zip!unicode.xml"}


def test_fixture_is_scanned_unless_exact_explicit_rule_excludes_it(tmp_path, policy):
    control = tmp_path / "tests/fixtures/forbidden-sample.txt"
    control.parent.mkdir(parents=True)
    shutil.copyfile(CONTROL, control)
    assert scan_tree(tmp_path, policy).match_count > 0
    policy.write_text(json.dumps({"excluded_fixture_paths": ["tests/fixtures/forbidden-sample.txt"]}), encoding="utf-8")
    report = scan_tree(tmp_path, policy)
    assert report.clean and report.excluded_paths == ["tests/fixtures/forbidden-sample.txt"]
    shutil.copyfile(CONTROL, tmp_path / "forbidden-sample.txt")
    assert scan_tree(tmp_path, policy).match_count > 0


@pytest.mark.parametrize("bad_policy", [
    {"excluded_fixture_paths": ["tests/*"]}, {"excluded_fixture_paths": ["tooling/anonymisation.py"]},
    {"limits": {"max_entry_bytes": 0}}, {"denylist": [""]}, {"typo": []},
])
def test_invalid_policy_is_rejected(tmp_path, policy, bad_policy):
    policy.write_text(json.dumps(bad_policy), encoding="utf-8")
    with pytest.raises(ValueError):
        scan_tree(tmp_path, policy)


def test_cli_reports_zero_and_returns_nonzero_for_leaks_and_incomplete_scan(tmp_path, policy):
    command = [sys.executable, str(ROOT / "tooling/anonymisation.py"), str(tmp_path), "--policy", str(policy)]
    good = subprocess.run(command, capture_output=True, text=True)
    assert good.returncode == 0 and "matches=0" in good.stdout
    shutil.copyfile(CONTROL, tmp_path / "control.txt")
    bad = subprocess.run(command, capture_output=True, text=True)
    assert bad.returncode == 1 and "[REDACTED]" in bad.stdout
    assert "123456" + "789012" not in bad.stdout
    (tmp_path / "control.txt").unlink()
    (tmp_path / "broken.xlsx").write_bytes(b"broken")
    incomplete = subprocess.run(command, capture_output=True, text=True)
    assert incomplete.returncode == 2 and "complete=false" in incomplete.stdout


def test_default_policy_scans_the_final_public_tree_with_explicit_positive_control_exclusion():
    report = scan_tree(ROOT, ROOT / "tooling/anonymisation-policy.json")
    assert report.clean, report.summary()
    assert report.scanned_texts > 100
    assert report.excluded_paths == ["tests/fixtures/forbidden-sample.txt"]


@pytest.mark.parametrize("suffix", [".", ",", ";", ":", ")", "]", "!", "?", "..."])
@pytest.mark.parametrize("address", ["8." + "8.8.8", "2606:" + "4700:4700::1111"])
def test_public_ips_followed_by_sentence_punctuation_are_detected(tmp_path, policy, address, suffix):
    (tmp_path / "notes.md").write_text("Address: " + address + suffix, encoding="utf-8")
    assert any(item.rule == "public-ip" for item in scan_tree(tmp_path, policy).matches)


@pytest.mark.parametrize("value", [
    "192.0.2.1.", "10.0.0.1,", "2001:db8::1.", "coordinates[::2]",
    "999.999.999.999.", "8.8." + "8.8.9", "8." + "8.8.8.example.com",
    "2606:" + "4700:4700::1111.example.com", "2606:" + "4700:4700::1111:::",
])
def test_punctuation_handling_does_not_create_false_public_ip_matches(tmp_path, policy, value):
    (tmp_path / "notes.md").write_text(value, encoding="utf-8")
    assert not any(item.rule == "public-ip" for item in scan_tree(tmp_path, policy).matches)


def test_sensitive_issue_paths_remain_redacted_after_match_storage_is_full(tmp_path, policy):
    token = "synthetic" + "-sensitive-path"
    policy.write_text(json.dumps({"denylist": [token], "limits": {"max_matches": 1}}), encoding="utf-8")
    (tmp_path / "a.md").write_text("account=" + "123456" + "789012", encoding="utf-8")
    (tmp_path / (token + ".xlsx")).write_bytes(b"not an archive")
    report = scan_tree(tmp_path, policy)
    assert report.match_count == 1 and not report.complete
    assert {item.rule for item in report.issues} >= {"match-limit", "archive-unreadable"}
    assert token not in report.summary()
    assert token not in repr(report)
    assert "[REDACTED PATH]" in report.summary()


def test_sensitive_symlink_directory_issue_is_redacted(tmp_path, policy, monkeypatch):
    token = "synthetic" + "-sensitive-link"
    policy.write_text(json.dumps({"denylist": [token]}), encoding="utf-8")
    link = tmp_path / token
    link.mkdir()
    (link / "must-not-be-read.md").write_text("neutral", encoding="utf-8")
    # This machine disallows unprivileged symlink creation. Exercise the real
    # scanner against the filesystem adapter's symlink classification instead.
    original_is_symlink = Path.is_symlink
    monkeypatch.setattr(Path, "is_symlink", lambda path: path == link or original_is_symlink(path))
    report = scan_tree(tmp_path, policy)
    assert any(item.rule == "symlink-not-scanned" for item in report.issues)
    assert token not in report.summary()
    assert token not in repr(report)
    assert report.scanned_texts == 0


def test_sensitive_empty_filesystem_directory_name_is_scanned(tmp_path, policy):
    token = "synthetic" + "-sensitive-directory"
    policy.write_text(json.dumps({"denylist": [token]}), encoding="utf-8")
    (tmp_path / token).mkdir()
    report = scan_tree(tmp_path, policy)
    assert any(item.path == token and item.line == 0 and item.rule == "denylist-token" for item in report.matches)
    assert token not in report.summary()


def test_scan_root_directory_name_is_also_checked_without_printing_absolute_path(tmp_path, policy):
    token = "synthetic" + "-sensitive-root"
    policy.write_text(json.dumps({"denylist": [token]}), encoding="utf-8")
    root = tmp_path / token
    root.mkdir()
    report = scan_tree(root, policy)
    assert any(item.path == "." and item.line == 0 and item.rule == "denylist-token" for item in report.matches)
    assert token not in report.summary() and str(tmp_path) not in report.summary()


def test_sensitive_zip_directory_name_is_scanned_before_skipping_its_content(tmp_path, policy):
    token = "synthetic" + "-sensitive-directory"
    policy.write_text(json.dumps({"denylist": [token]}), encoding="utf-8")
    with zipfile.ZipFile(tmp_path / "export.zip", "w") as archive:
        archive.writestr(token + "/", b"")
    report = scan_tree(tmp_path, policy)
    assert any(item.path == "export.zip!" + token + "/" and item.line == 0 for item in report.matches)
    assert token not in report.summary()


def test_zip_directory_entries_count_toward_archive_entry_limit(tmp_path, policy):
    policy.write_text(json.dumps({"limits": {"max_archive_entries": 1}}), encoding="utf-8")
    with zipfile.ZipFile(tmp_path / "export.zip", "w") as archive:
        archive.writestr("one/", b"")
        archive.writestr("two/", b"")
    report = scan_tree(tmp_path, policy)
    assert not report.complete and any(item.rule == "archive-entry-limit" for item in report.issues)
