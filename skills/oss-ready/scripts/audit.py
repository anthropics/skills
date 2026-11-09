#!/usr/bin/env python3
"""Audit a repository for open-source readiness.

Read-only: never modifies the repository. Standard library only (Python 3.8+).

Usage:
    python audit.py [REPO_PATH] [--format markdown|json]

Reports a 0-100 readiness score, the status of each check (pass / partial /
missing), warnings about files that look like secrets, the detected stack and
the real install/build/test/lint/format commands found in manifest files.
"""

import argparse
import fnmatch
import json
import os
import re
import sys

SKIP_DIRS = {
    ".git", "node_modules", "target", "dist", "build", "out", ".next", ".nuxt",
    ".venv", "venv", "env", "__pycache__", ".tox", ".mypy_cache", ".pytest_cache",
    "vendor", ".gradle", ".idea", ".vscode", "coverage", ".turbo", ".cache",
}
MAX_FILES = 50000
LARGE_FILE_BYTES = 10 * 1024 * 1024

SECRET_NAME_PATTERNS = [
    ".env", ".env.*", "*.pem", "*.key", "*.p12", "*.pfx", "id_rsa", "id_dsa",
    "id_ecdsa", "id_ed25519", "credentials.json", "service-account*.json",
    "*.keystore", "*.jks", ".npmrc", ".pypirc", "secrets.*",
]
SECRET_NAME_ALLOW = {".env.example", ".env.sample", ".env.template", ".env.dist"}

# Check id -> (group, weight, title)
CHECKS = [
    ("readme", "Essential", 20, "README"),
    ("license", "Essential", 20, "LICENSE"),
    ("contributing", "Essential", 15, "CONTRIBUTING.md"),
    ("code_of_conduct", "Community", 7, "CODE_OF_CONDUCT.md"),
    ("security", "Community", 7, "SECURITY.md"),
    ("issue_templates", "Community", 6, "Issue templates"),
    ("pr_template", "Community", 5, "Pull request template"),
    ("ci", "Tooling", 8, "Continuous integration"),
    ("gitignore", "Tooling", 4, ".gitignore"),
    ("tests", "Tooling", 5, "Tests"),
    ("changelog", "Tooling", 3, "CHANGELOG"),
]

DOC_DIRS = ["", ".github", "docs"]


# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #

def read_text(path, limit=200000):
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            return fh.read(limit)
    except OSError:
        return ""


def find_doc(root, names):
    """Find the first file matching any of `names` (case-insensitive) in the
    standard community-file locations. Returns a repo-relative path or None."""
    lowered = [n.lower() for n in names]
    for sub in DOC_DIRS:
        d = os.path.join(root, sub)
        if not os.path.isdir(d):
            continue
        try:
            entries = os.listdir(d)
        except OSError:
            continue
        for entry in sorted(entries):
            full = os.path.join(d, entry)
            if os.path.isfile(full) and entry.lower() in lowered:
                return os.path.join(sub, entry).replace("\\", "/")
    return None


def walk_files(root):
    """Yield repo-relative file paths, skipping vendored/build dirs."""
    count = 0
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for name in filenames:
            count += 1
            if count > MAX_FILES:
                return
            rel = os.path.relpath(os.path.join(dirpath, name), root)
            yield rel.replace("\\", "/")


def load_gitignore(root):
    patterns = []
    text = read_text(os.path.join(root, ".gitignore"))
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        negate = line.startswith("!")
        if negate:
            line = line[1:]
        patterns.append((negate, line))
    return patterns


def is_ignored(rel_path, patterns):
    """Approximate .gitignore matching (good enough for warnings)."""
    ignored = False
    parts = rel_path.split("/")
    base = parts[-1]
    for negate, pat in patterns:
        anchored = pat.startswith("/")
        p = pat.strip("/")
        if not p:
            continue
        if "/" in p or anchored:
            if any(c in p for c in "*?["):
                hit = fnmatch.fnmatch(rel_path, p) or fnmatch.fnmatch(rel_path, p + "/*")
            else:
                hit = rel_path == p or rel_path.startswith(p + "/")
        else:
            hit = fnmatch.fnmatch(base, p) or any(fnmatch.fnmatch(seg, p) for seg in parts[:-1])
        if hit:
            ignored = not negate
    return ignored


def parse_git(root):
    info = {"remote_url": None, "default_branch": None, "is_git_repo": False}
    git_dir = os.path.join(root, ".git")
    if not os.path.isdir(git_dir):
        return info
    info["is_git_repo"] = True
    config = read_text(os.path.join(git_dir, "config"))
    m = re.search(r'\[remote "origin"\][^\[]*?url\s*=\s*(\S+)', config, re.S)
    if m:
        url = m.group(1)
        ssh = re.match(r"git@([^:]+):(.+?)(\.git)?$", url)
        if ssh:
            url = "https://%s/%s" % (ssh.group(1), ssh.group(2))
        url = re.sub(r"\.git$", "", url)
        url = re.sub(r"https://[^@/]+@", "https://", url)  # strip credentials
        info["remote_url"] = url
    origin_head = read_text(os.path.join(git_dir, "refs", "remotes", "origin", "HEAD"))
    m = re.search(r"refs/remotes/origin/(\S+)", origin_head)
    if m:
        info["default_branch"] = m.group(1)
    else:
        head = read_text(os.path.join(git_dir, "HEAD"))
        m = re.search(r"refs/heads/(\S+)", head)
        if m:
            info["default_branch"] = m.group(1)
    return info


# --------------------------------------------------------------------------- #
# Stack and command detection
# --------------------------------------------------------------------------- #

def find_manifests(root, max_depth=2):
    names = {
        "package.json", "Cargo.toml", "pyproject.toml", "setup.py", "setup.cfg",
        "requirements.txt", "go.mod", "pom.xml", "build.gradle", "build.gradle.kts",
        "Gemfile", "composer.json", "Makefile", "deno.json", "mix.exs", "pubspec.yaml",
    }
    found = []
    root_depth = root.rstrip(os.sep).count(os.sep)
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        if dirpath.count(os.sep) - root_depth >= max_depth:
            dirnames[:] = []
        for f in filenames:
            if f in names or f.endswith((".csproj", ".sln", ".fsproj")):
                rel = os.path.relpath(os.path.join(dirpath, f), root).replace("\\", "/")
                found.append(rel)
    return sorted(found, key=lambda p: (p.count("/"), p))


def cmd(command, source):
    return {"command": command, "source": source}


def detect_node(root, rel_dir, commands, stack):
    pkg_path = os.path.join(root, rel_dir, "package.json")
    try:
        pkg = json.loads(read_text(pkg_path) or "{}")
    except ValueError:
        pkg = {}
    d = os.path.join(root, rel_dir)
    if os.path.exists(os.path.join(d, "pnpm-lock.yaml")):
        pm, install = "pnpm", "pnpm install --frozen-lockfile"
    elif os.path.exists(os.path.join(d, "yarn.lock")):
        pm, install = "yarn", "yarn install --frozen-lockfile"
    elif os.path.exists(os.path.join(d, "bun.lockb")) or os.path.exists(os.path.join(d, "bun.lock")):
        pm, install = "bun", "bun install"
    elif os.path.exists(os.path.join(d, "package-lock.json")):
        pm, install = "npm", "npm ci"
    else:
        pm, install = "npm", "npm install"
    src = (rel_dir + "/package.json").lstrip("/")
    stack["package_manager"] = stack.get("package_manager") or pm
    commands.setdefault("install", cmd(install, src + " + lockfile"))
    scripts = pkg.get("scripts") or {}
    placeholder_test = "no test specified"
    mapping = {
        "build": ["build"],
        "test": ["test"],
        "lint": ["lint"],
        "format": ["format", "fmt", "prettier"],
        "typecheck": ["typecheck", "type-check", "tsc"],
    }
    for kind, keys in mapping.items():
        for k in keys:
            if k in scripts and placeholder_test not in str(scripts[k]):
                run = "%s test" % pm if k == "test" and pm in ("npm", "yarn", "bun") else "%s run %s" % (pm, k)
                commands.setdefault(kind, cmd(run, src + " scripts." + k))
                break
    node_version = None
    nvmrc = read_text(os.path.join(d, ".nvmrc")).strip() or read_text(os.path.join(d, ".node-version")).strip()
    if nvmrc:
        node_version = nvmrc
    elif isinstance(pkg.get("engines"), dict) and pkg["engines"].get("node"):
        node_version = pkg["engines"]["node"]
    if node_version:
        stack["node_version"] = node_version
    if "typescript" in json.dumps(pkg.get("devDependencies", {})) or os.path.exists(os.path.join(d, "tsconfig.json")):
        stack["languages"].add("TypeScript")
    else:
        stack["languages"].add("JavaScript")
    if pkg.get("license"):
        stack["manifest_license"] = pkg["license"]


def detect_rust(root, rel_dir, commands, stack):
    src = (rel_dir + "/Cargo.toml").lstrip("/")
    stack["languages"].add("Rust")
    stack["package_manager"] = stack.get("package_manager") or "cargo"
    commands.setdefault("install", cmd("cargo build", src))
    commands.setdefault("build", cmd("cargo build --release", src))
    commands.setdefault("test", cmd("cargo test", src))
    commands.setdefault("lint", cmd("cargo clippy --all-targets -- -D warnings", src))
    commands.setdefault("format", cmd("cargo fmt --all", src))
    m = re.search(r'^\s*license\s*=\s*"([^"]+)"', read_text(os.path.join(root, rel_dir, "Cargo.toml")), re.M)
    if m:
        stack["manifest_license"] = m.group(1)


def detect_python(root, rel_dir, commands, stack, manifest):
    d = os.path.join(root, rel_dir)
    stack["languages"].add("Python")
    blob = ""
    for f in ("pyproject.toml", "setup.cfg", "setup.py", "requirements.txt",
              "requirements-dev.txt", "requirements_dev.txt", "dev-requirements.txt", "tox.ini"):
        blob += read_text(os.path.join(d, f))
    src = (rel_dir + "/" + manifest).lstrip("/")
    if os.path.exists(os.path.join(d, "uv.lock")):
        stack["package_manager"] = stack.get("package_manager") or "uv"
        commands.setdefault("install", cmd("uv sync", "uv.lock"))
        runner = "uv run "
    elif os.path.exists(os.path.join(d, "poetry.lock")):
        stack["package_manager"] = stack.get("package_manager") or "poetry"
        commands.setdefault("install", cmd("poetry install", "poetry.lock"))
        runner = "poetry run "
    elif os.path.exists(os.path.join(d, "pyproject.toml")) or os.path.exists(os.path.join(d, "setup.py")):
        stack["package_manager"] = stack.get("package_manager") or "pip"
        extra = '".[dev]"' if re.search(r"^\s*dev\s*=\s*\[", blob, re.M) else "."
        commands.setdefault("install", cmd("pip install -e %s" % extra, src))
        runner = ""
    else:
        stack["package_manager"] = stack.get("package_manager") or "pip"
        commands.setdefault("install", cmd("pip install -r requirements.txt", src))
        runner = ""
    if re.search(r"\bpytest\b", blob):
        commands.setdefault("test", cmd(runner + "pytest", src + " (pytest dependency)"))
    if re.search(r"\bruff\b", blob):
        commands.setdefault("lint", cmd(runner + "ruff check .", src + " (ruff dependency)"))
        commands.setdefault("format", cmd(runner + "ruff format .", src + " (ruff dependency)"))
    elif re.search(r"\bflake8\b", blob):
        commands.setdefault("lint", cmd(runner + "flake8", src + " (flake8 dependency)"))
    if "format" not in commands and re.search(r"\bblack\b", blob):
        commands.setdefault("format", cmd(runner + "black .", src + " (black dependency)"))
    if re.search(r"\bmypy\b", blob):
        commands.setdefault("typecheck", cmd(runner + "mypy .", src + " (mypy dependency)"))
    m = re.search(r'requires-python\s*=\s*"([^"]+)"', blob)
    if m:
        stack["python_requires"] = m.group(1)
    m = re.search(r'^\s*license\s*=\s*(?:\{\s*text\s*=\s*)?"([^"]+)"', blob, re.M)
    if m:
        stack["manifest_license"] = m.group(1)


def detect_go(root, rel_dir, commands, stack):
    src = (rel_dir + "/go.mod").lstrip("/")
    stack["languages"].add("Go")
    stack["package_manager"] = stack.get("package_manager") or "go modules"
    commands.setdefault("install", cmd("go mod download", src))
    commands.setdefault("build", cmd("go build ./...", src))
    commands.setdefault("test", cmd("go test ./...", src))
    commands.setdefault("lint", cmd("go vet ./...", src))
    commands.setdefault("format", cmd("gofmt -w .", src))


def detect_jvm(root, rel_dir, manifest, commands, stack):
    d = os.path.join(root, rel_dir)
    src = (rel_dir + "/" + manifest).lstrip("/")
    if manifest == "pom.xml":
        stack["languages"].add("Java/Kotlin")
        stack["package_manager"] = stack.get("package_manager") or "maven"
        mvn = "./mvnw" if os.path.exists(os.path.join(d, "mvnw")) else "mvn"
        commands.setdefault("build", cmd("%s -B package" % mvn, src))
        commands.setdefault("test", cmd("%s -B test" % mvn, src))
    else:
        stack["languages"].add("Java/Kotlin")
        stack["package_manager"] = stack.get("package_manager") or "gradle"
        gradle = "./gradlew" if os.path.exists(os.path.join(d, "gradlew")) else "gradle"
        commands.setdefault("build", cmd("%s build" % gradle, src))
        commands.setdefault("test", cmd("%s test" % gradle, src))


def detect_makefile(root, rel_dir, commands):
    text = read_text(os.path.join(root, rel_dir, "Makefile"))
    src = (rel_dir + "/Makefile").lstrip("/")
    targets = set(re.findall(r"^([A-Za-z0-9_-]+)\s*:(?!=)", text, re.M))
    for kind, names in (("build", ["build"]), ("test", ["test", "check"]),
                        ("lint", ["lint"]), ("format", ["fmt", "format"]),
                        ("install", ["install", "setup", "deps"])):
        for n in names:
            if n in targets:
                commands.setdefault(kind, cmd("make %s" % n, src))
                break


def detect_stack(root):
    stack = {"languages": set(), "package_manager": None, "manifests": []}
    commands = {}
    manifests = find_manifests(root)
    stack["manifests"] = manifests
    seen_python_dirs = set()
    for rel in manifests:
        rel_dir = os.path.dirname(rel)
        name = os.path.basename(rel)
        if name == "package.json":
            detect_node(root, rel_dir, commands, stack)
        elif name == "Cargo.toml":
            detect_rust(root, rel_dir, commands, stack)
        elif name in ("pyproject.toml", "setup.py", "setup.cfg", "requirements.txt"):
            if rel_dir not in seen_python_dirs:
                seen_python_dirs.add(rel_dir)
                detect_python(root, rel_dir, commands, stack, name)
        elif name == "go.mod":
            detect_go(root, rel_dir, commands, stack)
        elif name in ("pom.xml", "build.gradle", "build.gradle.kts"):
            detect_jvm(root, rel_dir, name, commands, stack)
        elif name.endswith((".csproj", ".sln", ".fsproj")):
            stack["languages"].add(".NET")
            commands.setdefault("build", cmd("dotnet build", rel))
            commands.setdefault("test", cmd("dotnet test", rel))
        elif name == "Gemfile":
            stack["languages"].add("Ruby")
            commands.setdefault("install", cmd("bundle install", rel))
        elif name == "composer.json":
            stack["languages"].add("PHP")
            commands.setdefault("install", cmd("composer install", rel))
        elif name == "Makefile":
            detect_makefile(root, rel_dir, commands)
    stack["languages"] = sorted(stack["languages"])
    if len({os.path.dirname(m) for m in manifests if not m.endswith("Makefile")}) > 1:
        stack["monorepo_hint"] = True
    return stack, commands


# --------------------------------------------------------------------------- #
# Checks
# --------------------------------------------------------------------------- #

LICENSE_SIGNATURES = [
    ("AGPL-3.0", ["GNU AFFERO GENERAL PUBLIC LICENSE"]),
    ("LGPL-3.0", ["GNU LESSER GENERAL PUBLIC LICENSE", "Version 3"]),
    ("LGPL-2.1", ["GNU LESSER GENERAL PUBLIC LICENSE", "Version 2.1"]),
    ("GPL-3.0", ["GNU GENERAL PUBLIC LICENSE", "Version 3"]),
    ("GPL-2.0", ["GNU GENERAL PUBLIC LICENSE", "Version 2"]),
    ("Apache-2.0", ["Apache License", "Version 2.0"]),
    ("MPL-2.0", ["Mozilla Public License", "2.0"]),
    ("Unlicense", ["This is free and unencumbered software"]),
    ("CC0-1.0", ["CC0 1.0"]),
    ("ISC", ["Permission to use, copy, modify, and/or distribute this software"]),
    ("MIT", ["Permission is hereby granted, free of charge"]),
    ("BSD-3-Clause", ["Redistribution and use in source and binary forms", "Neither the name"]),
    ("BSD-2-Clause", ["Redistribution and use in source and binary forms"]),
]


def identify_license(text):
    for spdx, needles in LICENSE_SIGNATURES:
        if all(n.lower() in text.lower() for n in needles):
            return spdx
    return None


def result(status, detail, path=None, **extra):
    r = {"status": status, "detail": detail, "path": path}
    r.update(extra)
    return r


def check_readme(root):
    path = find_doc(root, ["README.md", "README", "README.rst", "README.txt", "README.markdown", "readme.md"])
    if not path:
        return result("missing", "No README found.")
    text = read_text(os.path.join(root, path))
    prose = re.sub(r"^\s*(```|~~~).*?^\s*\1", "", text, flags=re.M | re.S)  # drop fenced code
    found = re.findall(r"^\s{0,3}#{1,6}\s*(.+)$", prose, re.M)          # ATX headings
    found += re.findall(r"^(\S.*)\n[=-]{3,}\s*$", prose, re.M)           # Setext / RST headings
    headings = " ".join(found).lower()
    has = {
        "install": bool(re.search(r"install|setup|getting started|quick ?start|build", headings)),
        "usage": bool(re.search(r"usage|example|how to use|quick ?start|getting started|demo", headings)),
        "contributing": bool(re.search(r"contribut", text, re.I)),
        "license": bool(re.search(r"licen[cs]e", headings)),
    }
    missing = [k for k, v in has.items() if not v]
    if len(text) >= 300 and has["install"] and has["usage"]:
        detail = "Good." if not missing else "Has install and usage; missing sections: " + ", ".join(missing) + "."
        return result("pass", detail, path, sections=has, length=len(text))
    reasons = []
    if len(text) < 300:
        reasons.append("short (%d chars)" % len(text))
    if missing:
        reasons.append("missing sections: " + ", ".join(missing))
    return result("partial", "README is " + "; ".join(reasons) + ".", path, sections=has, length=len(text))


def check_license(root, stack):
    path = find_doc(root, ["LICENSE", "LICENSE.md", "LICENSE.txt", "LICENCE", "LICENCE.md",
                           "LICENCE.txt", "COPYING", "COPYING.md", "LICENSE-MIT", "LICENSE-APACHE"])
    if not path:
        if stack.get("manifest_license"):
            return result("missing", "No LICENSE file, although the manifest declares '%s'. Add the full license text."
                          % stack["manifest_license"])
        return result("missing", "No LICENSE file. Without one, others have no legal right to use or contribute.")
    spdx = identify_license(read_text(os.path.join(root, path)))
    if spdx:
        return result("pass", "Detected %s." % spdx, path, spdx=spdx)
    return result("partial", "License file found but the license could not be identified.", path)


def check_contributing(root):
    path = find_doc(root, ["CONTRIBUTING.md", "CONTRIBUTING", "CONTRIBUTING.rst", "CONTRIBUTING.txt"])
    if not path:
        return result("missing", "No contributing guide.")
    text = read_text(os.path.join(root, path))
    if re.search(r"```|^\s{4}\S", text, re.M) and re.search(r"\b(test|build|install|lint)\b", text, re.I):
        return result("pass", "Has setup/test instructions.", path)
    return result("partial", "Exists but has no concrete setup or test commands.", path)


def check_simple(root, names, what):
    path = find_doc(root, names)
    if path:
        return result("pass", "Found.", path)
    return result("missing", "No %s." % what)


def check_issue_templates(root):
    for base in (".github/ISSUE_TEMPLATE", ".gitlab/issue_templates"):
        d = os.path.join(root, base)
        if os.path.isdir(d):
            files = [f for f in os.listdir(d) if f.lower().endswith((".md", ".yml", ".yaml"))]
            templates = [f for f in files if f.lower() not in ("config.yml", "config.yaml")]
            if templates:
                return result("pass", "%d template(s)." % len(templates), base, files=sorted(templates))
            if files:
                return result("partial", "Only config.yml, no actual templates.", base)
    single = find_doc(root, ["ISSUE_TEMPLATE.md"])
    if single:
        return result("partial", "Single legacy ISSUE_TEMPLATE.md; issue forms are recommended.", single)
    return result("missing", "No issue templates.")


def check_pr_template(root):
    path = find_doc(root, ["PULL_REQUEST_TEMPLATE.md", "pull_request_template.md"])
    if path:
        return result("pass", "Found.", path)
    for base in (".github/PULL_REQUEST_TEMPLATE", ".gitlab/merge_request_templates"):
        d = os.path.join(root, base)
        if os.path.isdir(d) and os.listdir(d):
            return result("pass", "Found.", base)
    return result("missing", "No pull request template.")


def check_ci(root):
    wf = os.path.join(root, ".github", "workflows")
    if os.path.isdir(wf):
        files = sorted(f for f in os.listdir(wf) if f.endswith((".yml", ".yaml")))
        if files:
            return result("pass", "GitHub Actions: " + ", ".join(files), ".github/workflows")
    for p in (".gitlab-ci.yml", ".circleci/config.yml", "azure-pipelines.yml", ".travis.yml",
              "Jenkinsfile", "bitbucket-pipelines.yml", ".woodpecker.yml", ".drone.yml"):
        if os.path.exists(os.path.join(root, p)):
            return result("pass", "Found %s." % p, p)
    return result("missing", "No CI configuration.")


TEST_FILE_PATTERNS = ["test_*.py", "*_test.py", "*_test.go", "*.test.js", "*.test.ts",
                      "*.test.jsx", "*.test.tsx", "*.spec.js", "*.spec.ts", "*Test.java",
                      "*Tests.cs", "*_spec.rb", "*Test.kt"]
TEST_DIRS = {"tests", "test", "__tests__", "spec", "specs"}
CODE_EXTENSIONS = (".py", ".js", ".jsx", ".ts", ".tsx", ".mjs", ".cjs", ".go", ".rs", ".java",
                   ".kt", ".cs", ".fs", ".rb", ".php", ".ex", ".exs", ".dart", ".swift", ".c",
                   ".cc", ".cpp", ".h", ".sh", ".lua", ".scala", ".clj", ".zig")


def check_tests(root, files):
    test_files = []
    rust_inline = False
    for rel in files:
        parts = rel.split("/")
        base = parts[-1]
        in_test_dir = any(p in TEST_DIRS for p in parts[:-1]) and base.endswith(CODE_EXTENSIONS)
        if in_test_dir or any(fnmatch.fnmatch(base, pat) for pat in TEST_FILE_PATTERNS):
            test_files.append(rel)
        elif base.endswith(".rs") and not rust_inline and "#[test]" in read_text(os.path.join(root, rel), 400000):
            rust_inline = True
            test_files.append(rel + " (#[test])")
        if len(test_files) >= 50:
            break
    if test_files:
        return result("pass", "Found test files (e.g. %s)." % test_files[0], examples=test_files[:5])
    return result("missing", "No tests found. Not generated by this skill; mention in CONTRIBUTING.md that tests are welcome.")


def check_changelog(root):
    return check_simple(root, ["CHANGELOG.md", "CHANGELOG", "HISTORY.md", "CHANGES.md", "NEWS.md", "RELEASES.md"],
                        "changelog (GitHub releases also count; check manually)")


def find_warnings(root, files, ignore_patterns):
    warnings = []
    for rel in files:
        base = rel.split("/")[-1]
        if base.lower() in SECRET_NAME_ALLOW:
            continue
        if any(fnmatch.fnmatch(base, pat) for pat in SECRET_NAME_PATTERNS):
            if not is_ignored(rel, ignore_patterns):
                warnings.append({"type": "possible_secret", "path": rel,
                                 "detail": "Looks like a secret or credential file and is not in .gitignore."})
        try:
            size = os.path.getsize(os.path.join(root, rel))
        except OSError:
            continue
        if size > LARGE_FILE_BYTES and not is_ignored(rel, ignore_patterns):
            warnings.append({"type": "large_file", "path": rel,
                             "detail": "%.1f MB; consider Git LFS or removing it." % (size / 1048576.0)})
    return warnings


# --------------------------------------------------------------------------- #
# Main
# --------------------------------------------------------------------------- #

def grade(score):
    if score >= 90:
        return "A", "Ready for contributors"
    if score >= 75:
        return "B", "Nearly there"
    if score >= 50:
        return "C", "Usable, but newcomers will struggle"
    return "D", "Not ready to accept contributions"


def audit(root):
    root = os.path.abspath(root)
    git = parse_git(root)
    stack, commands = detect_stack(root)
    files = list(walk_files(root))
    ignore_patterns = load_gitignore(root)

    checks = {
        "readme": check_readme(root),
        "license": check_license(root, stack),
        "contributing": check_contributing(root),
        "code_of_conduct": check_simple(root, ["CODE_OF_CONDUCT.md", "CODE_OF_CONDUCT", "CODE-OF-CONDUCT.md"],
                                        "code of conduct"),
        "security": check_simple(root, ["SECURITY.md", "SECURITY"], "security policy"),
        "issue_templates": check_issue_templates(root),
        "pr_template": check_pr_template(root),
        "ci": check_ci(root),
        "gitignore": check_simple(root, [".gitignore"], ".gitignore"),
        "tests": check_tests(root, files),
        "changelog": check_changelog(root),
    }
    # .gitignore must be at the root to matter
    if checks["gitignore"]["status"] == "pass" and checks["gitignore"]["path"] != ".gitignore":
        checks["gitignore"] = result("partial", ".gitignore is not at the repository root.", checks["gitignore"]["path"])

    score = 0.0
    out_checks = []
    for cid, group, weight, title in CHECKS:
        r = checks[cid]
        factor = {"pass": 1.0, "partial": 0.5, "missing": 0.0}[r["status"]]
        score += weight * factor
        entry = {"id": cid, "group": group, "title": title, "weight": weight}
        entry.update(r)
        out_checks.append(entry)
    score = int(round(score))
    letter, meaning = grade(score)

    repo_name = os.path.basename(root)
    if git["remote_url"]:
        repo_name = git["remote_url"].rstrip("/").split("/")[-1]

    return {
        "repo_path": root,
        "repo_name": repo_name,
        "git": git,
        "score": score,
        "grade": letter,
        "grade_meaning": meaning,
        "checks": out_checks,
        "warnings": find_warnings(root, files, ignore_patterns),
        "stack": stack,
        "commands": commands,
        "files_scanned": len(files),
    }


def to_markdown(rep):
    icon = {"pass": "[x]", "partial": "[~]", "missing": "[ ]"}
    lines = []
    lines.append("# OSS readiness: %s" % rep["repo_name"])
    lines.append("")
    lines.append("**Score: %d/100 (grade %s - %s)**" % (rep["score"], rep["grade"], rep["grade_meaning"]))
    lines.append("")
    if rep["warnings"]:
        lines.append("## Warnings (review before publishing)")
        lines.append("")
        for w in rep["warnings"]:
            lines.append("- `%s`: %s" % (w["path"], w["detail"]))
        lines.append("")
    for group in ("Essential", "Community", "Tooling"):
        lines.append("## %s" % group)
        lines.append("")
        lines.append("| | Check | Points | Status | Detail |")
        lines.append("|---|---|---|---|---|")
        for c in rep["checks"]:
            if c["group"] != group:
                continue
            where = (" (`%s`)" % c["path"]) if c.get("path") else ""
            lines.append("| %s | %s%s | %d | %s | %s |" % (icon[c["status"]], c["title"], where,
                                                          c["weight"], c["status"], c["detail"]))
        lines.append("")
    lines.append("## Detected project facts")
    lines.append("")
    st = rep["stack"]
    lines.append("- Languages: %s" % (", ".join(st["languages"]) or "unknown"))
    lines.append("- Package manager: %s" % (st.get("package_manager") or "unknown"))
    for key, label in (("node_version", "Node version"), ("python_requires", "Python requires"),
                       ("manifest_license", "License in manifest")):
        if st.get(key):
            lines.append("- %s: %s" % (label, st[key]))
    lines.append("- Remote URL: %s" % (rep["git"]["remote_url"] or "unknown"))
    lines.append("- Default branch: %s" % (rep["git"]["default_branch"] or "unknown"))
    if st.get("monorepo_hint"):
        lines.append("- Monorepo: manifests found in several directories: %s" % ", ".join(st["manifests"]))
    lines.append("")
    lines.append("## Commands (use these in CONTRIBUTING.md and CI)")
    lines.append("")
    if rep["commands"]:
        lines.append("| Purpose | Command | Found in |")
        lines.append("|---|---|---|")
        for kind in ("install", "build", "test", "lint", "format", "typecheck"):
            if kind in rep["commands"]:
                c = rep["commands"][kind]
                lines.append("| %s | `%s` | %s |" % (kind, c["command"], c["source"]))
        missing = [k for k in ("install", "build", "test", "lint", "format") if k not in rep["commands"]]
        if missing:
            lines.append("")
            lines.append("Not detected: %s. Do not invent these; ask the user or leave them out." % ", ".join(missing))
    else:
        lines.append("No manifest files found; ask the user how to build and test the project.")
    lines.append("")
    return "\n".join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Audit a repository for open-source readiness (read-only).")
    parser.add_argument("repo", nargs="?", default=".", help="Path to the repository root (default: .)")
    parser.add_argument("--format", choices=["markdown", "json"], default="markdown",
                        help="Output format (default: markdown)")
    args = parser.parse_args(argv)

    if not os.path.isdir(args.repo):
        print("error: '%s' is not a directory" % args.repo, file=sys.stderr)
        return 2
    rep = audit(args.repo)
    if args.format == "json":
        print(json.dumps(rep, indent=2, default=list))
    else:
        print(to_markdown(rep))
    return 0


if __name__ == "__main__":
    sys.exit(main())
