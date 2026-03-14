#!/usr/bin/env python3
"""
Phase 1: Extract testable claims from CLAUDE.md and .claude/rules/ files.

Parses every instruction into a structured claim with type, source location,
and extracted data. The output (claims.json) feeds into Phase 2 (coherence
verification) and Phase 3 (eval task generation).

Usage:
    python -m scripts.extract_claims <path-to-claude-md> [--rules-dir <path>] [--output <path>]
"""

import argparse
import json
import re
import sys
from pathlib import Path


# ---------------------------------------------------------------------------
# Known patterns for detection
# ---------------------------------------------------------------------------

COMMAND_PREFIXES = {
    "npm", "pnpm", "yarn", "npx", "pip", "pip3", "python", "python3",
    "cargo", "make", "go", "ruby", "bundle", "docker", "docker-compose",
    "kubectl", "terraform", "gradle", "mvn", "dotnet", "mix", "composer",
    "php", "jest", "vitest", "pytest", "ruff", "black", "eslint",
    "prettier", "tsc", "turbo", "nx", "lerna", "bun",
}

FRAMEWORK_NAMES = {
    # JS/TS
    "react", "next.js", "next", "nextjs", "vue", "angular", "svelte",
    "express", "fastify", "nestjs", "nest", "nuxt", "remix", "astro",
    "vite", "webpack", "esbuild", "rollup", "parcel",
    "tailwind", "tailwindcss", "emotion", "styled-components",
    "prisma", "drizzle", "typeorm", "sequelize", "mongoose", "knex",
    "jest", "vitest", "playwright", "cypress", "testing-library",
    "eslint", "prettier", "storybook", "msw", "zod",
    "tanstack", "react-query", "swr", "axios", "trpc",
    "zustand", "jotai", "recoil", "redux", "mobx",
    # Python
    "django", "flask", "fastapi", "sqlalchemy", "alembic", "pytest",
    "pydantic", "celery", "redis", "ruff", "black", "mypy",
    "poetry", "pipenv", "uvicorn", "gunicorn",
    # Rust
    "tokio", "actix", "axum", "diesel", "seaorm", "serde", "clap",
    # Go
    "gin", "echo", "fiber", "gorm", "sqlx",
    # Ruby
    "rails", "sinatra", "rspec", "sidekiq",
    # General
    "docker", "kubernetes", "k8s", "terraform",
    "postgresql", "postgres", "mysql", "mongodb", "sqlite",
    "redis", "elasticsearch", "opensearch",
    "graphql", "grpc", "kafka", "rabbitmq",
    "sentry", "datadog", "grafana",
}

VAGUE_PATTERNS = [
    (r"(?i)\bwrite clean\b", "write clean ..."),
    (r"(?i)\bfollow best practices\b", "follow best practices"),
    (r"(?i)\bformat code properly\b", "format code properly"),
    (r"(?i)\btest your changes\b", "test your changes"),
    (r"(?i)\bkeep files organized\b", "keep files organized"),
    (r"(?i)\buse good naming\b", "use good naming"),
    (r"(?i)\bhandle errors well\b", "handle errors well"),
    (r"(?i)\bwrite meaningful\b", "write meaningful ..."),
    (r"(?i)\bcode should be\s+(clean|readable|maintainable)\b", "code should be clean/readable"),
    (r"(?i)\bproperly\s+(handle|format|structure|organize)\b", "properly ..."),
    (r"(?i)\bensure\s+quality\b", "ensure quality"),
    (r"(?i)\bmaintain\s+consistency\b", "maintain consistency"),
]

GENERIC_PATTERNS = [
    (r"(?i)\bdon'?t repeat yourself\b", "DRY principle"),
    (r"(?i)\bDRY\s+principle\b", "DRY principle"),
    (r"(?i)\bKISS\s+principle\b", "KISS principle"),
    (r"(?i)\bSOLID\s+principles?\b", "SOLID principles"),
    (r"(?i)\bkeep functions small\b", "keep functions small"),
    (r"(?i)\buse meaningful variable names\b", "meaningful variable names"),
    (r"(?i)\bsingle responsibility\b", "single responsibility"),
    (r"(?i)\bseparation of concerns\b", "separation of concerns"),
]

NAMING_KEYWORDS = [
    "PascalCase", "camelCase", "snake_case", "kebab-case",
    "UPPER_SNAKE_CASE", "SCREAMING_SNAKE_CASE",
]

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def read_file(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except (FileNotFoundError, PermissionError):
        return ""


def parse_sections(content: str) -> list[dict]:
    """Split markdown content into sections by headers."""
    sections: list[dict] = []
    current_section = "Top"
    current_lines: list[tuple[int, str]] = []

    for i, line in enumerate(content.splitlines(), 1):
        header_match = re.match(r"^(#{1,4})\s+(.+)", line)
        if header_match:
            if current_lines:
                sections.append({"name": current_section, "lines": current_lines})
            current_section = header_match.group(2).strip()
            current_lines = [(i, line)]
        else:
            current_lines.append((i, line))

    if current_lines:
        sections.append({"name": current_section, "lines": current_lines})

    return sections


# ---------------------------------------------------------------------------
# Extractors — each returns a list of claim dicts
# ---------------------------------------------------------------------------


def extract_commands(sections: list[dict], source_file: str) -> list[dict]:
    """Extract CLI commands from backtick-enclosed text."""
    claims = []
    cmd_id = 0

    for section in sections:
        for line_num, line in section["lines"]:
            # Pattern: `command args` — description  OR  - `command args` — description
            matches = re.finditer(r"`([^`]+)`", line)
            for m in matches:
                text = m.group(1).strip()
                first_word = text.split()[0] if text.split() else ""

                # Check if first word is a known command prefix
                if first_word.lower() in COMMAND_PREFIXES:
                    cmd_id += 1
                    # Try to extract description after — or -
                    desc_match = re.search(r"[—–\-]\s*(.+)$", line[m.end():])
                    description = desc_match.group(1).strip() if desc_match else ""

                    claims.append({
                        "id": f"cmd-{cmd_id}",
                        "type": "command",
                        "raw_text": line.strip(),
                        "source_file": source_file,
                        "source_line": line_num,
                        "source_section": section["name"],
                        "extracted": {
                            "command": text,
                            "description": description,
                        },
                        "testable": True,
                    })

    return claims


def extract_paths(sections: list[dict], source_file: str) -> list[dict]:
    """Extract file/directory path references."""
    claims = []
    path_id = 0
    seen_paths = set()

    for section in sections:
        for line_num, line in section["lines"]:
            matches = re.finditer(r"`([^`]+)`", line)
            for m in matches:
                text = m.group(1).strip()

                # Skip if it looks like a command (already handled)
                first_word = text.split()[0] if text.split() else ""
                if first_word.lower() in COMMAND_PREFIXES:
                    continue

                # Check if it looks like a path
                if re.match(r"^\.?/?[\w@.-]+(/[\w@.*{}\[\]-]+)+/?$", text):
                    # Skip URLs
                    if text.startswith("http") or text.startswith("//"):
                        continue
                    if text in seen_paths:
                        continue
                    seen_paths.add(text)

                    path_id += 1
                    claims.append({
                        "id": f"path-{path_id}",
                        "type": "path_reference",
                        "raw_text": line.strip(),
                        "source_file": source_file,
                        "source_line": line_num,
                        "source_section": section["name"],
                        "extracted": {
                            "path": text,
                            "is_directory": text.endswith("/"),
                        },
                        "testable": True,
                    })

    return claims


def extract_frameworks(sections: list[dict], source_file: str) -> list[dict]:
    """Extract framework/library references."""
    claims = []
    fw_id = 0
    seen_frameworks = set()

    for section in sections:
        section_text = " ".join(line for _, line in section["lines"])

        for fw_name in FRAMEWORK_NAMES:
            # Case-insensitive search with word boundary
            pattern = r"(?i)\b" + re.escape(fw_name) + r"\b"
            match = re.search(pattern, section_text)
            if match and fw_name.lower() not in seen_frameworks:
                # Find the actual line
                matched_line_num = section["lines"][0][0]
                for ln, lt in section["lines"]:
                    if re.search(pattern, lt):
                        matched_line_num = ln
                        break

                seen_frameworks.add(fw_name.lower())
                fw_id += 1

                # Check for config path reference nearby
                config_path = None
                config_match = re.search(
                    r"`([^`]*" + re.escape(fw_name.lower().replace(".", "")) + r"[^`]*)`",
                    section_text, re.IGNORECASE
                )
                if config_match:
                    candidate = config_match.group(1)
                    if "/" in candidate:
                        config_path = candidate

                claims.append({
                    "id": f"fw-{fw_id}",
                    "type": "framework_reference",
                    "raw_text": match.group(0),
                    "source_file": source_file,
                    "source_line": matched_line_num,
                    "source_section": section["name"],
                    "extracted": {
                        "framework": fw_name.lower(),
                        **({"config_path": config_path} if config_path else {}),
                    },
                    "testable": True,
                })

    return claims


def extract_conventions(sections: list[dict], source_file: str) -> list[dict]:
    """Extract coding conventions and rules from directive language."""
    claims = []
    conv_id = 0

    directive_patterns = [
        # "Use X" / "Always use X"
        r"(?i)^\s*[-*]?\s*(?:always\s+)?use\s+(.+)",
        # "No X" / "Never X" / "Avoid X" / "X forbidden/prohibited"
        r"(?i)^\s*[-*]?\s*(?:no|never|avoid|don'?t)\s+(.+)",
        # "X only" / "only X"
        r"(?i)^\s*[-*]?\s*(.+?)\s+only\b",
        # "Prefer X over Y"
        r"(?i)^\s*[-*]?\s*prefer\s+(.+)",
        # "X should/must be Y"
        r"(?i)^\s*[-*]?\s*\w+\s+(?:should|must)\s+(?:be|have|use|follow)\s+(.+)",
        # "X instead of Y" / "X, not Y"
        r"(?i)^\s*[-*]?\s*(.+?)\s+instead of\s+(.+)",
    ]

    for section in sections:
        for line_num, line in section["lines"]:
            stripped = line.strip()
            if not stripped or stripped.startswith("#"):
                continue

            # Check directive patterns
            for pattern in directive_patterns:
                if re.search(pattern, stripped):
                    # Skip if it's a command or path (already extracted)
                    first_backtick = re.search(r"`[^`]+`", stripped)
                    if first_backtick:
                        inner = first_backtick.group(0).strip("`")
                        first_word = inner.split()[0] if inner.split() else ""
                        if first_word.lower() in COMMAND_PREFIXES:
                            continue

                    conv_id += 1
                    claims.append({
                        "id": f"conv-{conv_id}",
                        "type": "convention",
                        "raw_text": stripped,
                        "source_file": source_file,
                        "source_line": line_num,
                        "source_section": section["name"],
                        "extracted": {
                            "rule": stripped.lstrip("-* "),
                        },
                        "testable": True,
                    })
                    break  # One match per line is enough

    return claims


def extract_naming_patterns(sections: list[dict], source_file: str) -> list[dict]:
    """Extract naming convention claims."""
    claims = []
    name_id = 0

    for section in sections:
        for line_num, line in section["lines"]:
            for keyword in NAMING_KEYWORDS:
                if keyword in line:
                    name_id += 1
                    claims.append({
                        "id": f"name-{name_id}",
                        "type": "naming_pattern",
                        "raw_text": line.strip(),
                        "source_file": source_file,
                        "source_line": line_num,
                        "source_section": section["name"],
                        "extracted": {
                            "pattern": keyword,
                            "context": line.strip().lstrip("-* "),
                        },
                        "testable": True,
                    })
                    break  # One match per line

    return claims


def extract_env_references(sections: list[dict], source_file: str) -> list[dict]:
    """Extract environment variable references."""
    claims = []
    env_id = 0
    seen_vars = set()

    for section in sections:
        for line_num, line in section["lines"]:
            # Match UPPER_SNAKE_CASE with known prefixes or standalone
            matches = re.finditer(
                r"`?(NEXT_PUBLIC_|VITE_|REACT_APP_|NODE_|DATABASE_|API_|AWS_|REDIS_)[\w]*`?|"
                r"(?<![`\w])([A-Z][A-Z0-9_]{3,})(?![`\w])",
                line
            )
            for m in matches:
                var_name = m.group(0).strip("`")
                if var_name in seen_vars:
                    continue
                # Filter out common non-env words
                if var_name in {"TODO", "NOTE", "FIXME", "HACK", "ALWAYS", "NEVER",
                                "MUST", "SHALL", "SHOULD", "TRUE", "FALSE", "NULL",
                                "YAML", "JSON", "HTML", "HTTP", "HTTPS", "POST",
                                "DELETE", "PATCH", "IMPORTANT", "WARNING", "SKILL"}:
                    continue
                seen_vars.add(var_name)
                env_id += 1
                claims.append({
                    "id": f"env-{env_id}",
                    "type": "env_reference",
                    "raw_text": line.strip(),
                    "source_file": source_file,
                    "source_line": line_num,
                    "source_section": section["name"],
                    "extracted": {
                        "variable": var_name,
                    },
                    "testable": True,
                })

    return claims


def extract_vague_and_generic(sections: list[dict], source_file: str) -> list[dict]:
    """Flag vague and generic instructions."""
    claims = []
    vague_id = 0
    generic_id = 0

    for section in sections:
        for line_num, line in section["lines"]:
            # Check vague
            for pattern, label in VAGUE_PATTERNS:
                if re.search(pattern, line):
                    vague_id += 1
                    claims.append({
                        "id": f"vague-{vague_id}",
                        "type": "vague",
                        "raw_text": line.strip(),
                        "source_file": source_file,
                        "source_line": line_num,
                        "source_section": section["name"],
                        "extracted": {
                            "issue": f"Too vague to verify: '{label}'",
                            "suggestion": "Replace with a specific, verifiable instruction",
                        },
                        "testable": False,
                    })
                    break

            # Check generic
            for pattern, label in GENERIC_PATTERNS:
                if re.search(pattern, line):
                    generic_id += 1
                    claims.append({
                        "id": f"generic-{generic_id}",
                        "type": "generic",
                        "raw_text": line.strip(),
                        "source_file": source_file,
                        "source_line": line_num,
                        "source_section": section["name"],
                        "extracted": {
                            "issue": f"Generic advice Claude already knows: '{label}'",
                            "suggestion": "Remove or replace with project-specific instruction",
                        },
                        "testable": False,
                    })
                    break

    return claims


# ---------------------------------------------------------------------------
# Main extraction pipeline
# ---------------------------------------------------------------------------


def extract_from_file(file_path: Path, source_name: str | None = None) -> list[dict]:
    """Extract all claims from a single file."""
    content = read_file(file_path)
    if not content.strip():
        return []

    source = source_name or file_path.name
    sections = parse_sections(content)

    all_claims = []
    all_claims.extend(extract_commands(sections, source))
    all_claims.extend(extract_paths(sections, source))
    all_claims.extend(extract_frameworks(sections, source))
    all_claims.extend(extract_conventions(sections, source))
    all_claims.extend(extract_naming_patterns(sections, source))
    all_claims.extend(extract_env_references(sections, source))
    all_claims.extend(extract_vague_and_generic(sections, source))

    return all_claims


def extract_claims(claude_md_path: Path, rules_dir: Path | None = None) -> dict:
    """Extract claims from CLAUDE.md and optional .claude/rules/ directory."""
    claims = extract_from_file(claude_md_path, "CLAUDE.md")

    rules_files = []
    if rules_dir and rules_dir.exists():
        for rule_file in sorted(rules_dir.glob("**/*.md")):
            rel_path = str(rule_file.relative_to(rules_dir.parent))
            rules_files.append(rel_path)
            file_claims = extract_from_file(rule_file, rel_path)

            # Re-number IDs to avoid collisions
            for claim in file_claims:
                prefix = claim["id"].rsplit("-", 1)[0]
                existing_max = max(
                    (int(c["id"].rsplit("-", 1)[1]) for c in claims if c["id"].startswith(prefix + "-")),
                    default=0,
                )
                claim["id"] = f"{prefix}-{existing_max + 1}"
                existing_max += 1  # noqa: Not needed but makes intent clear

            claims.extend(file_claims)

    # Deduplicate by raw_text (keep first occurrence)
    seen_texts = set()
    unique_claims = []
    for claim in claims:
        normalized = claim["raw_text"].strip().lower()
        if normalized not in seen_texts:
            seen_texts.add(normalized)
            unique_claims.append(claim)

    return {
        "source_file": str(claude_md_path),
        "rules_files": rules_files,
        "total_claims": len(unique_claims),
        "claims": unique_claims,
    }


def main():
    parser = argparse.ArgumentParser(description="Extract claims from CLAUDE.md")
    parser.add_argument("claude_md", type=Path, help="Path to CLAUDE.md")
    parser.add_argument("--rules-dir", type=Path, default=None)
    parser.add_argument("--output", type=Path, default=None, help="Output JSON path")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON")
    args = parser.parse_args()

    result = extract_claims(args.claude_md, args.rules_dir)

    output_json = json.dumps(result, indent=2 if args.pretty else None, ensure_ascii=False)

    if args.output:
        args.output.write_text(output_json, encoding="utf-8")
        print(f"Extracted {result['total_claims']} claims → {args.output}")
    else:
        print(output_json)


if __name__ == "__main__":
    main()
