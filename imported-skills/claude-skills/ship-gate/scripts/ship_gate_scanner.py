#!/usr/bin/env python3
"""
ship_gate_scanner.py — Pre-production audit CLI
Part of the ship-gate skill: https://github.com/rx4u/ship-gate

Usage:
  python scripts/ship_gate_scanner.py [PATH] [options]

Options:
  --json            Output results as JSON
  --no-color        Disable ANSI color output
  --no-interactive  Skip manual confirmation prompts
  --category CAT    Only run a specific category (SEC, DB, CODE, etc.)
  --verbose         Show PASS results in addition to FAIL
  --version         Show version and exit

Exit codes:
  0 = CLEAR TO SHIP (no critical issues)
  1 = DO NOT SHIP (critical issues found)
  2 = SHIP WITH CAUTION (high issues only)
"""

import argparse
import json
import os
import re
import sys
import time
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import List, Optional

VERSION = "1.0.0"

EXCLUDE_DIRS = {
    "node_modules", ".next", "dist", "build", ".git", "__pycache__",
    "venv", ".venv", "vendor", "coverage", ".turbo", "out", ".cache",
    ".pytest_cache", ".mypy_cache", "target", "bin", "obj",
}

FRONTEND_DIRS = {"src", "app", "pages", "components", "public", "lib", "utils"}

JS_EXTS = {".js", ".ts", ".jsx", ".tsx", ".mjs", ".cjs"}
PY_EXTS = {".py"}
ALL_CODE_EXTS = JS_EXTS | PY_EXTS | {".go", ".rb", ".php"}
TEMPLATE_EXTS = {".html", ".jsx", ".tsx", ".vue", ".svelte"}
SQL_EXTS = {".sql", ".prisma"}


# ---------------------------------------------------------------------------
# ANSI helpers
# ---------------------------------------------------------------------------

USE_COLOR = True


def _c(code: str, text: str) -> str:
    if not USE_COLOR:
        return text
    return f"\033[{code}m{text}\033[0m"


def red(t):    return _c("31", t)
def green(t):  return _c("32", t)
def yellow(t): return _c("33", t)
def cyan(t):   return _c("36", t)
def bold(t):   return _c("1", t)
def dim(t):    return _c("2", t)


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------

class Status(str, Enum):
    PASS   = "PASS"
    FAIL   = "FAIL"
    SKIP   = "SKIP"
    MANUAL = "MANUAL"


class Severity(str, Enum):
    CRITICAL = "CRITICAL"
    HIGH     = "HIGH"
    ADVISORY = "ADVISORY"


@dataclass
class Finding:
    file: str
    line: int
    snippet: str = ""


@dataclass
class CheckDef:
    id: str
    description: str
    severity: Severity
    category: str
    stack: str = "all"     # "all", "js", "ts", "react", "supabase", "ai", "web", "vps"


@dataclass
class Result:
    check: CheckDef
    status: Status
    message: str = ""
    findings: List[Finding] = field(default_factory=list)


@dataclass
class Stack:
    has_node: bool = False
    framework: str = ""         # next, react, vue, svelte, astro, express, fastify, hono
    has_python: bool = False
    py_framework: str = ""      # django, flask, fastapi
    has_go: bool = False
    has_rust: bool = False
    has_supabase: bool = False
    has_typescript: bool = False
    has_react: bool = False
    deploy_target: str = ""     # vercel, netlify, docker, fly, railway
    has_ai: bool = False
    ai_providers: List[str] = field(default_factory=list)
    is_web: bool = False


# ---------------------------------------------------------------------------
# File walking / grep helpers
# ---------------------------------------------------------------------------

def walk_files(root: str, exts: Optional[set] = None, dirs: Optional[set] = None):
    """Yield (filepath, relpath) for all files under root, skipping EXCLUDE_DIRS."""
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in EXCLUDE_DIRS]
        if dirs is not None:
            rel = os.path.relpath(dirpath, root)
            top = rel.split(os.sep)[0]
            if rel != "." and top not in dirs:
                dirnames[:] = []
                continue
        for fname in filenames:
            if exts is None or os.path.splitext(fname)[1].lower() in exts:
                fpath = os.path.join(dirpath, fname)
                yield fpath, os.path.relpath(fpath, root)


def grep_files(
    root: str,
    pattern: str,
    exts: Optional[set] = None,
    dirs: Optional[set] = None,
    flags: int = 0,
    max_findings: int = 20,
    exclude_patterns: Optional[List[str]] = None,
) -> List[Finding]:
    """Return up to max_findings matches across the codebase."""
    try:
        rx = re.compile(pattern, flags)
    except re.error:
        return []

    exclude_rxs = []
    if exclude_patterns:
        for ep in exclude_patterns:
            try:
                exclude_rxs.append(re.compile(ep))
            except re.error:
                pass

    results: List[Finding] = []
    for fpath, relpath in walk_files(root, exts, dirs):
        if any(seg in fpath for seg in (".test.", ".spec.", ".config.")):
            if exts and exts <= JS_EXTS:
                skip = True
                # still yield for config-specific checks
                if "tsconfig" in fpath or "package.json" in fpath:
                    skip = False
                if skip:
                    continue
        try:
            with open(fpath, "r", encoding="utf-8", errors="ignore") as fh:
                for lineno, line in enumerate(fh, 1):
                    if rx.search(line):
                        if any(ex.search(line) for ex in exclude_rxs):
                            continue
                        results.append(Finding(
                            file=relpath,
                            line=lineno,
                            snippet=line.rstrip()[:120],
                        ))
                        if len(results) >= max_findings:
                            return results
        except (OSError, PermissionError):
            continue
    return results


def file_exists_in(root: str, *names: str) -> Optional[str]:
    """Return the first found path among names (searched recursively up to depth 5)."""
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in EXCLUDE_DIRS]
        depth = dirpath.replace(root, "").count(os.sep)
        if depth >= 5:
            dirnames[:] = []
            continue
        for fname in filenames:
            if fname in names:
                return os.path.join(dirpath, fname)
    return None


def read_json_file(path: str) -> dict:
    try:
        with open(path) as f:
            return json.load(f)
    except Exception:
        return {}


# ---------------------------------------------------------------------------
# Stack detection
# ---------------------------------------------------------------------------

def detect_stack(root: str) -> Stack:
    s = Stack()
    pkg_path = os.path.join(root, "package.json")
    if os.path.isfile(pkg_path):
        s.has_node = True
        pkg = read_json_file(pkg_path)
        all_deps = {}
        for key in ("dependencies", "devDependencies", "peerDependencies"):
            all_deps.update(pkg.get(key, {}))

        if "next" in all_deps:            s.framework = "next"
        elif "react" in all_deps:         s.framework = "react"
        elif "vue" in all_deps:           s.framework = "vue"
        elif "svelte" in all_deps:        s.framework = "svelte"
        elif "astro" in all_deps:         s.framework = "astro"
        elif "express" in all_deps:       s.framework = "express"
        elif "fastify" in all_deps:       s.framework = "fastify"
        elif "hono" in all_deps:          s.framework = "hono"

        s.has_react = s.framework in ("next", "react")
        s.is_web = s.framework in ("next", "react", "vue", "svelte", "astro")

        if "@supabase/supabase-js" in all_deps:
            s.has_supabase = True
        if "typescript" in all_deps or os.path.isfile(os.path.join(root, "tsconfig.json")):
            s.has_typescript = True

        for ai_pkg in ("openai", "@anthropic-ai/sdk", "@google/generative-ai",
                       "ai", "@huggingface/inference"):
            if ai_pkg in all_deps:
                s.has_ai = True
                s.ai_providers.append(ai_pkg)

    if os.path.isdir(os.path.join(root, "supabase")):
        s.has_supabase = True

    for pyfile in ("requirements.txt", "pyproject.toml", "Pipfile", "setup.py"):
        if os.path.isfile(os.path.join(root, pyfile)):
            s.has_python = True
            try:
                content = open(os.path.join(root, pyfile)).read().lower()
                if "django" in content:    s.py_framework = "django"
                elif "flask" in content:   s.py_framework = "flask"
                elif "fastapi" in content: s.py_framework = "fastapi"
            except Exception:
                pass
            break

    if os.path.isfile(os.path.join(root, "go.mod")):
        s.has_go = True
    if os.path.isfile(os.path.join(root, "Cargo.toml")):
        s.has_rust = True

    if os.path.isfile(os.path.join(root, "vercel.json")) or \
       os.path.isdir(os.path.join(root, ".vercel")):
        s.deploy_target = "vercel"
    elif os.path.isfile(os.path.join(root, "netlify.toml")):
        s.deploy_target = "netlify"
    elif os.path.isfile(os.path.join(root, "fly.toml")):
        s.deploy_target = "fly"
    elif os.path.isfile(os.path.join(root, "railway.json")):
        s.deploy_target = "railway"
    elif os.path.isfile(os.path.join(root, "Dockerfile")):
        s.deploy_target = "docker"

    return s


# ---------------------------------------------------------------------------
# Check definitions
# ---------------------------------------------------------------------------

CHECKS = {
    # SEC
    "SEC-01": CheckDef("SEC-01", "No API keys or secrets in frontend code", Severity.CRITICAL, "SEC"),
    "SEC-04": CheckDef("SEC-04", "CORS not wildcard", Severity.CRITICAL, "SEC"),
    "SEC-05": CheckDef("SEC-05", "CSRF protection on state-changing endpoints", Severity.CRITICAL, "SEC"),
    "SEC-06": CheckDef("SEC-06", "Input validated and sanitized server-side", Severity.HIGH, "SEC"),
    "SEC-07": CheckDef("SEC-07", "Rate limiting on auth and sensitive endpoints", Severity.HIGH, "SEC"),
    "SEC-08": CheckDef("SEC-08", "Passwords hashed with bcrypt or argon2", Severity.CRITICAL, "SEC"),
    "SEC-11": CheckDef("SEC-11", "CSP headers configured", Severity.HIGH, "SEC"),
    "SEC-13": CheckDef("SEC-13", "No eval() or dangerouslySetInnerHTML without sanitization", Severity.HIGH, "SEC", stack="js"),  # noqa: SEC-AUDITOR
    "SEC-14": CheckDef("SEC-14", "No sensitive data in URLs or logs", Severity.HIGH, "SEC"),
    "SEC-17": CheckDef("SEC-17", "No hardcoded secrets in .env committed to repo", Severity.CRITICAL, "SEC"),
    "SEC-18": CheckDef("SEC-18", ".env files listed in .gitignore", Severity.CRITICAL, "SEC"),
    # DB
    "DB-03": CheckDef("DB-03", "Parameterized queries everywhere (no SQL injection)", Severity.CRITICAL, "DB"),
    "DB-05": CheckDef("DB-05", "Connection pooling configured", Severity.HIGH, "DB"),
    "DB-06": CheckDef("DB-06", "Migrations in version control", Severity.HIGH, "DB"),
    "DB-07": CheckDef("DB-07", "RLS enabled on all Supabase tables", Severity.CRITICAL, "DB", stack="supabase"),
    "DB-08": CheckDef("DB-08", "No service_role key in client-side code", Severity.CRITICAL, "DB", stack="supabase"),
    "DB-12": CheckDef("DB-12", "No PII stored unencrypted", Severity.HIGH, "DB"),
    # DEPLOY
    "DEPLOY-09": CheckDef("DEPLOY-09", "Health check endpoint exists", Severity.HIGH, "DEPLOY"),
    "DEPLOY-10": CheckDef("DEPLOY-10", "Structured logging (not raw console)", Severity.HIGH, "DEPLOY"),
    # CODE
    "CODE-01": CheckDef("CODE-01", "No console.log in production build", Severity.HIGH, "CODE", stack="js"),
    "CODE-03": CheckDef("CODE-03", "No empty catch blocks", Severity.HIGH, "CODE"),
    "CODE-07": CheckDef("CODE-07", "No TODO-auth or TODO-security patterns", Severity.CRITICAL, "CODE"),
    "CODE-09": CheckDef("CODE-09", "React error boundaries in place", Severity.HIGH, "CODE", stack="react"),
    "CODE-10": CheckDef("CODE-10", "No leaked stack traces in error responses", Severity.HIGH, "CODE"),
    "CODE-11": CheckDef("CODE-11", "No eslint-disable on security rules", Severity.HIGH, "CODE", stack="js"),
    "CODE-12": CheckDef("CODE-12", "Lockfile committed", Severity.HIGH, "CODE"),
    "CODE-13": CheckDef("CODE-13", "No wildcard versions in package.json", Severity.HIGH, "CODE", stack="js"),
    "CODE-14": CheckDef("CODE-14", "TypeScript strict mode enabled", Severity.ADVISORY, "CODE", stack="ts"),
    # AI
    "AI-01": CheckDef("AI-01", "System prompts not leakable via user input", Severity.CRITICAL, "AI", stack="ai"),
    "AI-02": CheckDef("AI-02", "No prompt injection vectors in user inputs", Severity.CRITICAL, "AI", stack="ai"),
    "AI-03": CheckDef("AI-03", "LLM API keys not in frontend code", Severity.CRITICAL, "AI", stack="ai"),
    "AI-05": CheckDef("AI-05", "AI response output sanitized before rendering", Severity.HIGH, "AI", stack="ai"),
    # DEP
    "DEP-01": CheckDef("DEP-01", "No git:// or URL-based dependencies", Severity.HIGH, "DEP"),
    "DEP-05": CheckDef("DEP-05", "No suspicious postinstall scripts", Severity.HIGH, "DEP", stack="js"),
    "DEP-06": CheckDef("DEP-06", "Dependencies pinned (no wildcard *)", Severity.HIGH, "DEP"),
    # FE
    "FE-01": CheckDef("FE-01", "Meta tags present (title, description, OG)", Severity.ADVISORY, "FE", stack="web"),
    "FE-02": CheckDef("FE-02", "Favicon configured", Severity.ADVISORY, "FE", stack="web"),
    "FE-03": CheckDef("FE-03", "Custom 404 page exists", Severity.ADVISORY, "FE", stack="web"),
    "FE-09": CheckDef("FE-09", "robots.txt present", Severity.ADVISORY, "FE", stack="web"),
    # OBS
    "OBS-01": CheckDef("OBS-01", "Error monitoring configured (Sentry, etc.)", Severity.ADVISORY, "OBS"),
    "OBS-03": CheckDef("OBS-03", "Structured logging with request IDs", Severity.ADVISORY, "OBS"),
}

MANUAL_CHECKS = [
    CheckDef("SEC-02",     "Every route checks authentication",              Severity.CRITICAL, "SEC"),
    CheckDef("SEC-03",     "HTTPS enforced, HTTP redirected",                 Severity.CRITICAL, "SEC"),
    CheckDef("SEC-10",     "Sessions invalidated on logout (server-side)",    Severity.HIGH,     "SEC"),
    CheckDef("DB-01",      "Backups configured and tested",                   Severity.CRITICAL, "DB"),
    CheckDef("DB-02",      "Backup restore tested (not just backup)",         Severity.CRITICAL, "DB"),
    CheckDef("DB-04",      "Separate dev and production databases",           Severity.HIGH,     "DB"),
    CheckDef("DB-11",      "App uses a non-root DB user",                     Severity.HIGH,     "DB"),
    CheckDef("DEPLOY-01",  "All env vars set on production server",           Severity.CRITICAL, "DEPLOY"),
    CheckDef("DEPLOY-02",  "SSL certificate installed and valid",             Severity.CRITICAL, "DEPLOY"),
    CheckDef("DEPLOY-05",  "Rollback plan exists",                            Severity.HIGH,     "DEPLOY"),
    CheckDef("DEPLOY-06",  "Staging test passed before production",           Severity.HIGH,     "DEPLOY"),
    CheckDef("AI-07",      "Agent permissions scoped (no unrestricted access)", Severity.HIGH,   "AI", stack="ai"),
    CheckDef("AI-08",      "No sensitive data sent to third-party LLMs without consent", Severity.HIGH, "AI", stack="ai"),
    CheckDef("FE-04",      "Responsive design tested on mobile",              Severity.HIGH,     "FE", stack="web"),
    CheckDef("OBS-05",     "Uptime monitoring configured",                    Severity.HIGH,     "OBS"),
]


# ---------------------------------------------------------------------------
# Individual check implementations
# ---------------------------------------------------------------------------

def check_sec01(root, stack):
    c = CHECKS["SEC-01"]
    dirs = FRONTEND_DIRS & set(os.listdir(root))
    patterns = [
        r"sk-[a-zA-Z0-9]{20,}",
        r"sk-ant-[a-zA-Z0-9-]+",
        r"sk-proj-[a-zA-Z0-9-]+",
        r"AIza[a-zA-Z0-9_-]{35}",
        r"ghp_[a-zA-Z0-9]{36}",
        r"glpat-[a-zA-Z0-9_-]{20,}",
        r"AKIA[0-9A-Z]{16}",
        r"sk_live_[a-zA-Z0-9]{24,}",
        r"(api_key|apikey|api_secret|secret_key|auth_token)\s*[:=]\s*['\"][a-zA-Z0-9_\-]{16,}",
    ]
    findings = []
    for pat in patterns:
        findings += grep_files(root, pat, exts=JS_EXTS | {".env", ".json"},
                               dirs=dirs if dirs else None, max_findings=5)
    if findings:
        return Result(c, Status.FAIL,
                      f"{len(findings)} potential secret(s) found in frontend/client code",
                      findings[:10])
    return Result(c, Status.PASS)


def check_sec04(root, stack):
    c = CHECKS["SEC-04"]
    findings = grep_files(root, r"(origin\s*:\s*['\"]?\*['\"]?|Access-Control-Allow-Origin.*\*|cors\(\s*\))",
                          exts=ALL_CODE_EXTS)
    if findings:
        return Result(c, Status.FAIL, "CORS wildcard (*) detected", findings)
    return Result(c, Status.PASS)


def check_sec05(root, stack):
    c = CHECKS["SEC-05"]
    # Check for state-changing routes
    route_findings = grep_files(root, r"(app|router)\.(post|put|patch|delete)\s*\(",
                                exts=JS_EXTS)
    if not route_findings:
        return Result(c, Status.SKIP, "No Express-style routes found")
    # Check for CSRF protection
    csrf_findings = grep_files(root, r"(csrf|csrfToken|_csrf|CSRF_COOKIE|csurf)",
                               exts=ALL_CODE_EXTS)
    if not csrf_findings:
        return Result(c, Status.FAIL,
                      f"{len(route_findings)} state-changing route(s) found but no CSRF protection detected",
                      route_findings[:5])
    return Result(c, Status.PASS)


def check_sec06(root, stack):
    c = CHECKS["SEC-06"]
    # Check for validation library
    val_findings = grep_files(root,
        r"(from ['\"]zod['\"]|from ['\"]yup['\"]|from ['\"]joi['\"]|from ['\"]class-validator['\"]|from pydantic|import pydantic)",
        exts=ALL_CODE_EXTS)
    if val_findings:
        return Result(c, Status.PASS)
    # Check if there are API routes that use req.body without validation
    body_findings = grep_files(root, r"(req\.body|request\.json\(\)|request\.form)",
                               exts=ALL_CODE_EXTS)
    if body_findings:
        return Result(c, Status.FAIL,
                      "request body used without a validation library (zod/yup/joi/pydantic)",
                      body_findings[:5])
    return Result(c, Status.SKIP, "No API route body handling detected")


def check_sec07(root, stack):
    c = CHECKS["SEC-07"]
    findings = grep_files(root,
        r"(express-rate-limit|@upstash/ratelimit|rate-limiter-flexible|slowapi|throttle|rateLimit)",
        exts=ALL_CODE_EXTS | {".json"})
    if findings:
        return Result(c, Status.PASS)
    # Only fail if there are auth-related routes
    auth_routes = grep_files(root, r"(login|signin|register|signup|forgot.password|reset.password)",
                             exts=ALL_CODE_EXTS)
    if auth_routes:
        return Result(c, Status.FAIL,
                      "Auth routes found but no rate-limiting library detected", auth_routes[:3])
    return Result(c, Status.SKIP, "No auth routes detected")


def check_sec08(root, stack):
    c = CHECKS["SEC-08"]
    # Weak hash for passwords
    weak = grep_files(root, r"\b(md5|sha1|sha256)\s*\(",
                      exts=ALL_CODE_EXTS,
                      exclude_patterns=[r"//.*\b(md5|sha1|sha256)\b"])
    if weak:
        return Result(c, Status.FAIL, "Weak hashing algorithm (md5/sha1/sha256) detected", weak)
    strong = grep_files(root, r"(bcrypt|argon2|scrypt|pbkdf2)", exts=ALL_CODE_EXTS)
    pw_fields = grep_files(root, r"(password|passwd)", exts=ALL_CODE_EXTS)
    if pw_fields and not strong:
        return Result(c, Status.FAIL, "Password fields found but no bcrypt/argon2/scrypt usage")
    return Result(c, Status.PASS if strong or not pw_fields else Status.SKIP)


def check_sec11(root, stack):
    c = CHECKS["SEC-11"]
    findings = grep_files(root, r"(Content-Security-Policy|contentSecurityPolicy|[^a-z]csp[^a-z])",
                          exts=ALL_CODE_EXTS | {".json", ".toml", ".yaml", ".yml"})
    if findings:
        return Result(c, Status.PASS)
    return Result(c, Status.FAIL, "No Content-Security-Policy configuration found")


def check_sec13(root, stack):
    c = CHECKS["SEC-13"]
    if not stack.has_node:
        return Result(c, Status.SKIP, "Not a JS/TS project")
    eval_findings = grep_files(root, r"(\beval\s*\(|new\s+Function\s*\()", exts=JS_EXTS)
    dsi_findings = grep_files(root, r"dangerouslySetInnerHTML", exts=JS_EXTS)
    # If dangerouslySetInnerHTML is used, check for DOMPurify
    unsafe_dsi = []
    for f in dsi_findings:
        try:
            content = open(os.path.join(root, f.file), errors="ignore").read()
            if "DOMPurify" not in content and "sanitize" not in content.lower():
                unsafe_dsi.append(f)
        except Exception:
            unsafe_dsi.append(f)
    all_findings = eval_findings + unsafe_dsi  # noqa: SEC-AUDITOR
    if all_findings:
        return Result(c, Status.FAIL, "Unsafe eval() or unsanitized dangerouslySetInnerHTML", all_findings)  # noqa: SEC-AUDITOR
    return Result(c, Status.PASS)


def check_sec14(root, stack):
    c = CHECKS["SEC-14"]
    url_findings = grep_files(root,
        r"(password|token|secret|key|ssn|credit.card)=",
        exts=ALL_CODE_EXTS)
    log_findings = grep_files(root,
        r"console\.(log|info|debug)\s*\(\s*(req|request)\s*\)",
        exts=JS_EXTS)
    findings = url_findings + log_findings
    if findings:
        return Result(c, Status.FAIL, "Sensitive data may appear in URLs or logs", findings[:5])
    return Result(c, Status.PASS)


def check_sec17(root, stack):
    c = CHECKS["SEC-17"]
    # Check for .env files that are not .example/.sample
    env_files = []
    for entry in os.scandir(root):
        name = entry.name
        if name.startswith(".env") and name not in (".env.example", ".env.sample",
                                                      ".env.template", ".env.local.example"):
            if entry.is_file():
                env_files.append(name)
    if not env_files:
        return Result(c, Status.PASS)
    # Check if git-tracked
    gitignore_path = os.path.join(root, ".gitignore")
    if os.path.isfile(gitignore_path):
        content = open(gitignore_path, errors="ignore").read()
        if ".env" in content:
            return Result(c, Status.PASS)
    return Result(c, Status.FAIL,
                  f".env file(s) exist ({', '.join(env_files)}) and may not be gitignored",
                  [Finding(f, 0) for f in env_files])


def check_sec18(root, stack):
    c = CHECKS["SEC-18"]
    gitignore_path = os.path.join(root, ".gitignore")
    if not os.path.isfile(gitignore_path):
        return Result(c, Status.FAIL, ".gitignore file not found")
    content = open(gitignore_path, errors="ignore").read()
    if re.search(r"\.env", content):
        return Result(c, Status.PASS)
    return Result(c, Status.FAIL, ".env not listed in .gitignore")


def check_db03(root, stack):
    c = CHECKS["DB-03"]
    # Template literal SQL
    tl_findings = grep_files(root,
        r"(SELECT|INSERT|UPDATE|DELETE|FROM|WHERE).*\$\{",
        exts=JS_EXTS)
    # Python f-string SQL
    py_findings = grep_files(root,
        r'f["\'].*\b(SELECT|INSERT|UPDATE|DELETE|FROM|WHERE)\b.*\{',
        exts=PY_EXTS)
    # String concat SQL
    concat_findings = grep_files(root,
        r"(SELECT|INSERT|UPDATE|DELETE|FROM|WHERE).*\+\s*(req\.|params\.|body\.|query\.)",
        exts=ALL_CODE_EXTS)
    all_findings = tl_findings + py_findings + concat_findings
    if all_findings:
        return Result(c, Status.FAIL,
                      f"{len(all_findings)} potential SQL injection vector(s)", all_findings[:10])
    return Result(c, Status.PASS)


def check_db05(root, stack):
    c = CHECKS["DB-05"]
    findings = grep_files(root,
        r"(pool|connectionLimit|max_connections|poolSize|pooler|6543)",
        exts=ALL_CODE_EXTS | {".env", ".env.local", ".env.production"})
    if findings:
        return Result(c, Status.PASS)
    db_found = grep_files(root, r"(pg\.|postgres\.|mysql\.|mongoose\.)", exts=ALL_CODE_EXTS)
    if db_found:
        return Result(c, Status.FAIL, "Database usage detected but no connection pooling configured")
    return Result(c, Status.SKIP, "No direct DB connection detected")


def check_db06(root, stack):
    c = CHECKS["DB-06"]
    migration_dirs = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in EXCLUDE_DIRS]
        depth = dirpath.replace(root, "").count(os.sep)
        if depth >= 4:
            dirnames[:] = []
            continue
        for d in dirnames:
            if d in ("migrations", "migrate", "versions", "alembic"):
                migration_dirs.append(os.path.join(dirpath, d))
    if migration_dirs:
        return Result(c, Status.PASS)
    # Check for database usage
    db_found = grep_files(root, r"(prisma|supabase|mongoose|pg\.|sqlite)", exts=ALL_CODE_EXTS)
    if db_found:
        return Result(c, Status.FAIL, "Database usage found but no migrations directory detected")
    return Result(c, Status.SKIP, "No database usage detected")


def check_db07(root, stack):
    c = CHECKS["DB-07"]
    if not stack.has_supabase:
        return Result(c, Status.SKIP, "Not a Supabase project")
    sql_findings = grep_files(root, r"CREATE TABLE", exts=SQL_EXTS)
    if not sql_findings:
        return Result(c, Status.SKIP, "No CREATE TABLE statements found in migrations")
    rls_findings = grep_files(root, r"ENABLE ROW LEVEL SECURITY", exts=SQL_EXTS)
    if not rls_findings:
        return Result(c, Status.FAIL,
                      f"{len(sql_findings)} table(s) found but no RLS policies detected",
                      sql_findings[:5])
    if len(rls_findings) < len(sql_findings):
        return Result(c, Status.FAIL,
                      f"{len(sql_findings)} table(s) but only {len(rls_findings)} RLS statement(s) — some tables may lack RLS",
                      sql_findings[:5])
    return Result(c, Status.PASS)


def check_db08(root, stack):
    c = CHECKS["DB-08"]
    if not stack.has_supabase:
        return Result(c, Status.SKIP, "Not a Supabase project")
    dirs = FRONTEND_DIRS & set(os.listdir(root))
    findings = grep_files(root,
        r"(service_role|serviceRole|SUPABASE_SERVICE_ROLE)",
        exts=JS_EXTS, dirs=dirs if dirs else None)
    if findings:
        return Result(c, Status.FAIL, "service_role key referenced in client-side code", findings)
    return Result(c, Status.PASS)


def check_db12(root, stack):
    c = CHECKS["DB-12"]
    findings = grep_files(root,
        r"(ssn|social_security|credit_card|card_number|passport_number)",
        exts=SQL_EXTS | {".prisma"}, flags=re.IGNORECASE)
    if findings:
        return Result(c, Status.FAIL,
                      "PII column names found in schema — verify encryption at rest", findings)
    return Result(c, Status.PASS)


def check_deploy09(root, stack):
    c = CHECKS["DEPLOY-09"]
    findings = grep_files(root,
        r"(/health|/healthz|/api/health|/status|/readyz)",
        exts=ALL_CODE_EXTS)
    if findings:
        return Result(c, Status.PASS)
    return Result(c, Status.FAIL, "No health check endpoint found")


def check_deploy10(root, stack):
    c = CHECKS["DEPLOY-10"]
    # Check for logging libraries
    lib_findings = grep_files(root,
        r"(winston|pino|bunyan|morgan|log4js|structlog|loguru)",
        exts=ALL_CODE_EXTS | {".json"})
    if lib_findings:
        return Result(c, Status.PASS)
    # Count console.log in server/api code
    server_dirs = {"api", "server", "backend"}
    for d in ("pages/api", "app/api"):
        if os.path.isdir(os.path.join(root, d)):
            server_dirs.add(d.split("/")[0])
    console_findings = grep_files(root, r"console\.(log|debug|info)\(", exts=JS_EXTS)
    if console_findings:
        return Result(c, Status.FAIL,
                      f"No structured logger found; {len(console_findings)} console.log(s) in code",
                      console_findings[:5])
    return Result(c, Status.SKIP, "No server-side code detected")


def check_code01(root, stack):
    c = CHECKS["CODE-01"]
    if not stack.has_node:
        return Result(c, Status.SKIP, "Not a JS/TS project")
    findings = grep_files(root, r"console\.(log|debug|info)\(",
                          exts=JS_EXTS,
                          dirs=FRONTEND_DIRS & set(os.listdir(root)) or None,
                          exclude_patterns=[r"//.*console\.(log|debug|info)\("])
    if findings:
        return Result(c, Status.FAIL, f"{len(findings)} console.log statement(s) in production code", findings[:10])
    return Result(c, Status.PASS)


def check_code03(root, stack):
    c = CHECKS["CODE-03"]
    findings = grep_files(root,
        r"catch\s*\([^)]*\)\s*\{\s*\}",
        exts=ALL_CODE_EXTS)
    if findings:
        return Result(c, Status.FAIL, f"{len(findings)} empty catch block(s)", findings)
    return Result(c, Status.PASS)


def check_code07(root, stack):
    c = CHECKS["CODE-07"]
    findings = grep_files(root,
        r"(TODO|FIXME|HACK|XXX).{0,20}(auth|security|permission|validation|sanitiz)",
        exts=ALL_CODE_EXTS, flags=re.IGNORECASE)
    if findings:
        return Result(c, Status.FAIL, f"{len(findings)} deferred security TODO(s)", findings)
    return Result(c, Status.PASS)


def check_code09(root, stack):
    c = CHECKS["CODE-09"]
    if not stack.has_react:
        return Result(c, Status.SKIP, "Not a React project")
    # Next.js App Router: error.tsx
    error_page = file_exists_in(root, "error.tsx", "error.jsx", "global-error.tsx")
    if error_page:
        return Result(c, Status.PASS)
    # Class-based error boundary
    eb_findings = grep_files(root,
        r"(ErrorBoundary|componentDidCatch|getDerivedStateFromError)",
        exts=JS_EXTS)
    if eb_findings:
        return Result(c, Status.PASS)
    return Result(c, Status.FAIL, "No React error boundary or error.tsx found")


def check_code10(root, stack):
    c = CHECKS["CODE-10"]
    findings = grep_files(root,
        r"(error\.stack|\.stack\s*\)|err\.message.*res\.(json|send)|traceback\.format_exc)",
        exts=ALL_CODE_EXTS)
    if findings:
        return Result(c, Status.FAIL, "Potential stack trace leak in error responses", findings)
    return Result(c, Status.PASS)


def check_code11(root, stack):
    c = CHECKS["CODE-11"]
    if not stack.has_node:
        return Result(c, Status.SKIP, "Not a JS/TS project")
    findings = grep_files(root,
        r"eslint-disable.*(no-eval|no-implied-eval|no-script-url|security)",
        exts=JS_EXTS)
    if findings:
        return Result(c, Status.FAIL, "Security lint rule(s) disabled", findings)
    return Result(c, Status.PASS)


def check_code12(root, stack):
    c = CHECKS["CODE-12"]
    lockfiles = ["package-lock.json", "pnpm-lock.yaml", "yarn.lock", "bun.lockb",
                 "Pipfile.lock", "poetry.lock", "Gemfile.lock", "go.sum", "Cargo.lock"]
    for lf in lockfiles:
        if os.path.isfile(os.path.join(root, lf)):
            return Result(c, Status.PASS)
    return Result(c, Status.FAIL, "No lockfile found — dependencies are not pinned")


def check_code13(root, stack):
    c = CHECKS["CODE-13"]
    if not stack.has_node:
        return Result(c, Status.SKIP, "Not a JS/TS project")
    pkg_path = os.path.join(root, "package.json")
    if not os.path.isfile(pkg_path):
        return Result(c, Status.SKIP)
    findings = grep_files(root, r'"[^"]+"\s*:\s*"\*"', exts={".json"})
    findings += grep_files(root, r'"[^"]+"\s*:\s*"latest"', exts={".json"})
    findings = [f for f in findings if "package.json" in f.file and "node_modules" not in f.file]
    if findings:
        return Result(c, Status.FAIL, "Wildcard (*) or 'latest' version found in package.json", findings)
    return Result(c, Status.PASS)


def check_code14(root, stack):
    c = CHECKS["CODE-14"]
    if not stack.has_typescript:
        return Result(c, Status.SKIP, "Not a TypeScript project")
    tsconfig_path = os.path.join(root, "tsconfig.json")
    if not os.path.isfile(tsconfig_path):
        return Result(c, Status.SKIP, "tsconfig.json not found")
    content = open(tsconfig_path, errors="ignore").read()
    if re.search(r'"strict"\s*:\s*true', content):
        return Result(c, Status.PASS)
    return Result(c, Status.FAIL, "TypeScript strict mode not enabled in tsconfig.json",
                  [Finding("tsconfig.json", 0)])


def check_ai01(root, stack):
    c = CHECKS["AI-01"]
    if not stack.has_ai:
        return Result(c, Status.SKIP, "No AI/LLM usage detected")
    dirs = FRONTEND_DIRS & set(os.listdir(root))
    findings = grep_files(root,
        r"(system.?prompt|system.?message|system_instruction)",
        exts=ALL_CODE_EXTS, dirs=dirs if dirs else None, flags=re.IGNORECASE)
    if findings:
        return Result(c, Status.FAIL,
                      "System prompt referenced in client-accessible code — may be leakable",
                      findings)
    return Result(c, Status.PASS)


def check_ai02(root, stack):
    c = CHECKS["AI-02"]
    if not stack.has_ai:
        return Result(c, Status.SKIP, "No AI/LLM usage detected")
    findings = grep_files(root,
        r"(messages\.push|content\s*:.*\$\{|content\s*:.*\+\s*user|prompt.*\+)",
        exts=ALL_CODE_EXTS)
    if findings:
        return Result(c, Status.FAIL,
                      "User input may be concatenated directly into AI prompt", findings[:5])
    return Result(c, Status.PASS)


def check_ai03(root, stack):
    c = CHECKS["AI-03"]
    if not stack.has_ai:
        return Result(c, Status.SKIP, "No AI/LLM usage detected")
    dirs = FRONTEND_DIRS & set(os.listdir(root))
    findings = grep_files(root,
        r"(OPENAI_API_KEY|ANTHROPIC_API_KEY|GOOGLE_AI_API_KEY|sk-ant-|sk-proj-)",
        exts=JS_EXTS, dirs=dirs if dirs else None)
    if findings:
        return Result(c, Status.FAIL, "LLM API key referenced in frontend code", findings)
    return Result(c, Status.PASS)


def check_ai05(root, stack):
    c = CHECKS["AI-05"]
    if not stack.has_ai:
        return Result(c, Status.SKIP, "No AI/LLM usage detected")
    findings = grep_files(root,
        r"dangerouslySetInnerHTML.*\b(response|result|completion|message|content)\b",
        exts=JS_EXTS)
    if findings:
        return Result(c, Status.FAIL, "AI output rendered via dangerouslySetInnerHTML", findings)
    return Result(c, Status.PASS)


def check_dep01(root, stack):
    c = CHECKS["DEP-01"]
    if not stack.has_node:
        return Result(c, Status.SKIP, "Not a Node.js project")
    findings = grep_files(root,
        r'"[^"]+"\s*:\s*"(git://|git\+|github:|https://github\.com|file:)',
        exts={".json"})
    findings = [f for f in findings if "package.json" in f.file and "node_modules" not in f.file]
    if findings:
        return Result(c, Status.FAIL, "Git/URL-based dependency found in package.json", findings)
    return Result(c, Status.PASS)


def check_dep05(root, stack):
    c = CHECKS["DEP-05"]
    if not stack.has_node:
        return Result(c, Status.SKIP, "Not a Node.js project")
    pkg_path = os.path.join(root, "package.json")
    if not os.path.isfile(pkg_path):
        return Result(c, Status.SKIP)
    pkg = read_json_file(pkg_path)
    scripts = pkg.get("scripts", {})
    suspicious = []
    for key in ("preinstall", "postinstall", "install"):
        val = scripts.get(key, "")
        if val and any(kw in val for kw in ("curl", "wget", "fetch", "exec", "eval", "sh ", "bash ")):
            suspicious.append(Finding("package.json", 0, f'"{key}": "{val}"'))
    if suspicious:
        return Result(c, Status.FAIL, "Suspicious install script detected in package.json", suspicious)
    return Result(c, Status.PASS)


def check_dep06(root, stack):
    c = CHECKS["DEP-06"]
    if not stack.has_node:
        return Result(c, Status.SKIP, "Not a Node.js project")
    pkg_path = os.path.join(root, "package.json")
    if not os.path.isfile(pkg_path):
        return Result(c, Status.SKIP)
    findings = grep_files(root, r'"\*"', exts={".json"})
    findings = [f for f in findings if "package.json" in f.file and "node_modules" not in f.file]
    if findings:
        return Result(c, Status.FAIL, "Wildcard (*) version found", findings)
    return Result(c, Status.PASS)


def check_fe01(root, stack):
    c = CHECKS["FE-01"]
    if not stack.is_web and not stack.has_node:
        return Result(c, Status.SKIP, "Not a web project")
    # Next.js metadata export
    meta_findings = grep_files(root,
        r"(export\s+(const|async\s+function)\s+metadata|generateMetadata|<title>|og:title|og:description)",
        exts=JS_EXTS | {".html"})
    if meta_findings:
        return Result(c, Status.PASS)
    return Result(c, Status.FAIL, "No meta tags or Next.js metadata export found")


def check_fe02(root, stack):
    c = CHECKS["FE-02"]
    if not stack.is_web and not stack.has_node:
        return Result(c, Status.SKIP, "Not a web project")
    favicon = file_exists_in(root, "favicon.ico", "favicon.png", "favicon.svg",
                              "favicon.webp", "icon.png", "icon.ico")
    if favicon:
        return Result(c, Status.PASS)
    return Result(c, Status.FAIL, "No favicon file found")


def check_fe03(root, stack):
    c = CHECKS["FE-03"]
    if not stack.is_web and not stack.has_node:
        return Result(c, Status.SKIP, "Not a web project")
    page_404 = file_exists_in(root, "404.tsx", "404.jsx", "404.html",
                               "not-found.tsx", "not-found.jsx")
    if page_404:
        return Result(c, Status.PASS)
    return Result(c, Status.FAIL, "No custom 404 or not-found page found")


def check_fe09(root, stack):
    c = CHECKS["FE-09"]
    if not stack.is_web and not stack.has_node:
        return Result(c, Status.SKIP, "Not a web project")
    public_robots = os.path.join(root, "public", "robots.txt")
    root_robots = os.path.join(root, "robots.txt")
    if os.path.isfile(public_robots) or os.path.isfile(root_robots):
        return Result(c, Status.PASS)
    return Result(c, Status.FAIL, "No robots.txt found")


def check_obs01(root, stack):
    c = CHECKS["OBS-01"]
    findings = grep_files(root,
        r"(@sentry/|sentry-|LogRocket|Bugsnag|datadogRum|Rollbar|Honeybadger|newrelic)",
        exts=ALL_CODE_EXTS | {".json"})
    if findings:
        return Result(c, Status.PASS)
    return Result(c, Status.FAIL, "No error monitoring library detected")


def check_obs03(root, stack):
    c = CHECKS["OBS-03"]
    findings = grep_files(root,
        r"(winston|pino|bunyan|structlog|loguru|import logging)",
        exts=ALL_CODE_EXTS | {".json"})
    if findings:
        return Result(c, Status.PASS)
    return Result(c, Status.FAIL, "No structured logging library detected")


CATEGORY_CHECKS = {
    "SEC":    [check_sec01, check_sec04, check_sec05, check_sec06, check_sec07,
               check_sec08, check_sec11, check_sec13, check_sec14, check_sec17, check_sec18],
    "DB":     [check_db03, check_db05, check_db06, check_db07, check_db08, check_db12],
    "DEPLOY": [check_deploy09, check_deploy10],
    "CODE":   [check_code01, check_code03, check_code07, check_code09, check_code10,
               check_code11, check_code12, check_code13, check_code14],
    "AI":     [check_ai01, check_ai02, check_ai03, check_ai05],
    "DEP":    [check_dep01, check_dep05, check_dep06],
    "FE":     [check_fe01, check_fe02, check_fe03, check_fe09],
    "OBS":    [check_obs01, check_obs03],
}

CATEGORY_ORDER = ["SEC", "DB", "CODE", "DEP", "AI", "DEPLOY", "FE", "OBS"]


# ---------------------------------------------------------------------------
# Manual check runner
# ---------------------------------------------------------------------------

def run_manual_checks(stack: Stack, interactive: bool, category_filter: Optional[str]) -> List[Result]:
    results = []
    applicable = []
    for chk in MANUAL_CHECKS:
        if category_filter and chk.category != category_filter.upper():
            continue
        if chk.stack == "ai" and not stack.has_ai:
            results.append(Result(chk, Status.SKIP, "No AI/LLM usage detected"))
            continue
        if chk.stack == "web" and not stack.is_web:
            results.append(Result(chk, Status.SKIP, "Not a web project"))
            continue
        if chk.stack == "vps" and stack.deploy_target not in ("docker", "vps", ""):
            results.append(Result(chk, Status.SKIP, "Not a VPS/Docker deployment"))
            continue
        applicable.append(chk)

    if not interactive or not applicable:
        for chk in applicable:
            results.append(Result(chk, Status.MANUAL, "Not confirmed (run without --no-interactive to answer)"))
        return results

    print()
    print(bold("Manual Checks") + " — answer Y/N for each:")
    print()
    for chk in applicable:
        sev_label = {
            Severity.CRITICAL: red("CRITICAL"),
            Severity.HIGH:     yellow("HIGH"),
            Severity.ADVISORY: dim("ADVISORY"),
        }[chk.severity]
        while True:
            try:
                answer = input(f"  [{sev_label}] [{chk.id}] {chk.description} [y/N]: ").strip().lower()
            except (EOFError, KeyboardInterrupt):
                answer = "n"
            if answer in ("y", "yes"):
                results.append(Result(chk, Status.PASS))
                break
            elif answer in ("n", "no", ""):
                results.append(Result(chk, Status.FAIL, "Not confirmed"))
                break
            print("  Please enter Y or N.")
    return results


# ---------------------------------------------------------------------------
# Verdict / output
# ---------------------------------------------------------------------------

def severity_for_result(r: Result) -> Severity:
    return r.check.severity


def print_report(all_results: List[Result], stack: Stack, scan_time: float,
                 verbose: bool) -> int:
    critical = [r for r in all_results if r.status in (Status.FAIL, Status.MANUAL)
                and r.check.severity == Severity.CRITICAL]
    high     = [r for r in all_results if r.status in (Status.FAIL, Status.MANUAL)
                and r.check.severity == Severity.HIGH]
    advisory = [r for r in all_results if r.status in (Status.FAIL, Status.MANUAL)
                and r.check.severity == Severity.ADVISORY]

    stack_desc = []
    if stack.framework:   stack_desc.append(stack.framework.capitalize())
    if stack.has_supabase: stack_desc.append("Supabase")
    if stack.deploy_target: stack_desc.append(stack.deploy_target.capitalize())
    if stack.has_python and stack.py_framework: stack_desc.append(stack.py_framework.capitalize())
    if not stack_desc:    stack_desc.append("Unknown")
    stack_str = " + ".join(stack_desc)

    print()
    print(bold("SHIP GATE REPORT"))
    print("=" * 48)
    print(f"Stack:     {stack_str}")
    print(f"Scan time: {scan_time:.1f}s")
    print(f"Checks:    {len(all_results)} total")
    print()

    def _section(label, items, color_fn):
        if not items and not verbose:
            return
        print(bold(f"{label} ({len(items)} item{'s' if len(items) != 1 else ''})"))
        for r in items:
            status_str = {
                Status.FAIL:   red("FAIL  "),
                Status.MANUAL: yellow("MANUAL"),
                Status.PASS:   green("PASS  "),
                Status.SKIP:   dim("SKIP  "),
            }[r.status]
            print(f"  {status_str} [{r.check.id}] {r.check.description}")
            if r.message:
                print(f"          {dim(r.message)}")
            for f in r.findings[:3]:
                print(f"          {dim(f.file)}:{f.line}  {dim(f.snippet[:80])}")
        print()

    if critical:
        _section(red("CRITICAL") + " (must fix before shipping)", critical, red)
    if high:
        _section(yellow("HIGH") + " (should fix before shipping)", high, yellow)
    if advisory:
        _section(dim("ADVISORY") + " (recommended)", advisory, dim)

    if verbose:
        passed = [r for r in all_results if r.status == Status.PASS]
        if passed:
            _section(green("PASS"), passed, green)
        skipped = [r for r in all_results if r.status == Status.SKIP]
        if skipped:
            _section(dim("SKIP"), skipped, dim)

    if critical:
        print(red(bold(f"VERDICT: DO NOT SHIP ({len(critical)} critical issue{'s' if len(critical) != 1 else ''})")))
        print("Fix critical items and re-run.")
        return 1
    elif high:
        print(yellow(bold(f"VERDICT: SHIP WITH CAUTION ({len(high)} high issue{'s' if len(high) != 1 else ''})")))
        print("Acknowledge risks and proceed only if you accept them.")
        return 2
    else:
        print(green(bold("VERDICT: CLEAR TO SHIP")))
        return 0


def print_json_report(all_results: List[Result], stack: Stack, scan_time: float) -> int:
    critical = [r for r in all_results if r.status in (Status.FAIL, Status.MANUAL)
                and r.check.severity == Severity.CRITICAL]
    high     = [r for r in all_results if r.status in (Status.FAIL, Status.MANUAL)
                and r.check.severity == Severity.HIGH]

    output = {
        "version": VERSION,
        "scan_time": round(scan_time, 2),
        "stack": {
            "framework": stack.framework,
            "has_supabase": stack.has_supabase,
            "has_typescript": stack.has_typescript,
            "deploy_target": stack.deploy_target,
            "has_ai": stack.has_ai,
        },
        "results": [
            {
                "id": r.check.id,
                "description": r.check.description,
                "severity": r.check.severity.value,
                "category": r.check.category,
                "status": r.status.value,
                "message": r.message,
                "findings": [
                    {"file": f.file, "line": f.line, "snippet": f.snippet}
                    for f in r.findings
                ],
            }
            for r in all_results
        ],
        "summary": {
            "critical": len(critical),
            "high": len(high),
            "verdict": "DO_NOT_SHIP" if critical else ("SHIP_WITH_CAUTION" if high else "CLEAR_TO_SHIP"),
        },
    }
    print(json.dumps(output, indent=2))
    return 1 if critical else (2 if high else 0)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    global USE_COLOR

    parser = argparse.ArgumentParser(
        description="Ship Gate — pre-production audit scanner",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("path", nargs="?", default=".",
                        help="Project root directory (default: current directory)")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    parser.add_argument("--no-color", action="store_true", help="Disable color output")
    parser.add_argument("--no-interactive", action="store_true",
                        help="Skip manual confirmation prompts")
    parser.add_argument("--category", metavar="CAT",
                        help="Only run one category: SEC, DB, CODE, DEP, AI, DEPLOY, FE, OBS")
    parser.add_argument("--verbose", action="store_true",
                        help="Show PASS and SKIP results in addition to failures")
    parser.add_argument("--version", action="version", version=f"ship-gate {VERSION}")
    args = parser.parse_args()

    if args.no_color or not sys.stdout.isatty():
        USE_COLOR = False

    root = os.path.abspath(args.path)
    if not os.path.isdir(root):
        print(f"Error: '{root}' is not a directory", file=sys.stderr)
        sys.exit(1)

    start = time.time()

    # Detect stack
    stack = detect_stack(root)

    if not args.json:
        print(bold("Detecting stack..."), end=" ", flush=True)
        parts = []
        if stack.framework:   parts.append(stack.framework.capitalize())
        if stack.has_supabase: parts.append("Supabase")
        if stack.deploy_target: parts.append(stack.deploy_target.capitalize())
        if stack.has_python and stack.py_framework: parts.append(stack.py_framework.capitalize())
        if stack.has_ai:      parts.append(f"AI({','.join(stack.ai_providers)})")
        print(", ".join(parts) if parts else "generic project")

    # Run automated checks
    all_results: List[Result] = []
    categories = [args.category.upper()] if args.category else CATEGORY_ORDER

    for i, cat in enumerate(categories, 1):
        fns = CATEGORY_CHECKS.get(cat, [])
        cat_results = []
        for fn in fns:
            try:
                r = fn(root, stack)
            except Exception as e:
                chk_id = fn.__name__.replace("check_", "").replace("_", "-").upper()
                cat_results.append(Result(
                    CheckDef(chk_id, fn.__doc__ or fn.__name__, Severity.ADVISORY, cat),
                    Status.SKIP, f"Scanner error: {e}",
                ))
                continue
            cat_results.append(r)

        all_results.extend(cat_results)

        if not args.json:
            n_fail = sum(1 for r in cat_results if r.status == Status.FAIL)
            n_pass = sum(1 for r in cat_results if r.status == Status.PASS)
            n_skip = sum(1 for r in cat_results if r.status == Status.SKIP)
            label = red(f"{n_fail} FAIL") if n_fail else green("0 FAIL")
            print(f"  [{i}/{len(categories)}] {cat}: {label}, {n_pass} PASS, {dim(str(n_skip) + ' SKIP')}")

    # Manual checks
    manual_results = run_manual_checks(stack, not args.no_interactive, args.category)
    all_results.extend(manual_results)

    scan_time = time.time() - start

    if args.json:
        sys.exit(print_json_report(all_results, stack, scan_time))
    else:
        sys.exit(print_report(all_results, stack, scan_time, args.verbose))


if __name__ == "__main__":
    main()
