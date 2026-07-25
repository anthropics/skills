#!/usr/bin/env python3
"""Skill recommender for the handoff doc.

Scans repo SKILL.md files, scores each against the user's goal text, and
returns the top 3-5 matches with a one-line *why*. Hard cap at 5 — Matt's
discipline: do not list 20 skills.

Stdlib-only.
"""


import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import config_loader  # noqa: E402

# Domains the recommender knows about, ordered by typical relevance.
DOMAIN_DIRS = [
    "productivity",
    "engineering",
    "engineering-team",
    "marketing-skill",
    "marketing",
    "research",
    "product-team",
    "project-management",
    "c-level-advisor",
    "ra-qm-team",
    "business-growth",
    "business-operations",
    "commercial",
    "finance",
]

MAX_RESULTS = 5
MIN_SCORE = 1


@dataclass
class SkillCard:
    slug: str
    domain: str
    title: str
    description: str
    path: Path


def _find_repo_root(start: Path) -> Path:
    """Walk parents and return the OUTERMOST dir containing CLAUDE.md.

    Plugin folders also carry .claude-plugin/, so we cannot stop at the
    first match — that would pin the recommender to a single plugin.
    """
    cur = start.resolve()
    outermost: Path | None = None
    for parent in [cur, *cur.parents]:
        if (parent / "CLAUDE.md").exists():
            outermost = parent
    if outermost is not None:
        return outermost
    for parent in [cur, *cur.parents]:
        if (parent / ".claude-plugin").exists():
            return parent
    return start


def _parse_frontmatter(text: str) -> dict[str, str]:
    if not text.startswith("---"):
        return {}
    end = text.find("\n---", 3)
    if end == -1:
        return {}
    block = text[3:end].strip()
    out: dict[str, str] = {}
    key: str | None = None
    buf: list[str] = []
    for raw in block.splitlines():
        if not raw.strip():
            continue
        m = re.match(r"^([A-Za-z0-9_\-]+)\s*:\s*(.*)$", raw)
        if m and not raw.startswith(" ") and not raw.startswith("\t"):
            if key is not None:
                out[key] = " ".join(buf).strip().strip('"').strip("'")
            key = m.group(1)
            buf = [m.group(2)]
        elif key is not None:
            buf.append(raw.strip().strip('"').strip("'"))
    if key is not None:
        out[key] = " ".join(buf).strip().strip('"').strip("'")
    return out


def _collect_skills(repo_root: Path, scope: str, current_domain: str | None) -> list[SkillCard]:
    cards: list[SkillCard] = []
    if scope == "off":
        return cards
    domains = DOMAIN_DIRS
    if scope == "current_domain" and current_domain:
        domains = [current_domain]
    for d in domains:
        domain_root = repo_root / d
        if not domain_root.is_dir():
            continue
        for skill_md in domain_root.rglob("SKILL.md"):
            if any(p.name in {"node_modules", ".git", "documentation"} for p in skill_md.parents):
                continue
            try:
                text = skill_md.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
            fm = _parse_frontmatter(text)
            slug = fm.get("name") or skill_md.parent.name
            description = fm.get("description") or ""
            title = slug.replace("-", " ").title()
            cards.append(
                SkillCard(
                    slug=slug,
                    domain=d,
                    title=title,
                    description=description,
                    path=skill_md,
                )
            )
    return cards


def _tokenize(text: str) -> list[str]:
    return [t.lower() for t in re.findall(r"[A-Za-z][A-Za-z0-9_-]{2,}", text)]


_STOPWORDS = {
    "the", "and", "for", "with", "from", "into", "that", "this", "next",
    "session", "skill", "skills", "agent", "user", "should", "would",
    "using", "use", "uses", "used", "make", "made", "have", "has",
    "into", "your", "their", "them", "they", "where", "what", "when",
    "who", "how", "why", "than", "then", "also", "more", "less",
}


def _score(card: SkillCard, goal_tokens: list[str], goal_set: set[str]) -> int:
    if not goal_tokens:
        return 0
    haystack = f"{card.slug} {card.title} {card.description}".lower()
    score = 0
    for tok in goal_set:
        if tok in _STOPWORDS:
            continue
        if len(tok) < 3:
            continue
        occurrences = haystack.count(tok)
        score += occurrences
        if tok in card.slug.lower():
            score += 3
    return score


def _short_description(description: str, limit: int = 140) -> str:
    description = re.sub(r"\s+", " ", description).strip()
    if len(description) <= limit:
        return description
    cut = description[:limit]
    last_space = cut.rfind(" ")
    if last_space > 80:
        cut = cut[:last_space]
    return cut.rstrip() + "..."


def recommend(goal: str, repo_root: Path, scope: str, current_domain: str | None) -> list[dict]:
    cards = _collect_skills(repo_root, scope=scope, current_domain=current_domain)
    goal_tokens = _tokenize(goal)
    goal_set = set(goal_tokens)
    scored: list[tuple[int, SkillCard]] = []
    for c in cards:
        s = _score(c, goal_tokens, goal_set)
        if s >= MIN_SCORE:
            scored.append((s, c))
    scored.sort(key=lambda x: (-x[0], x[1].slug))
    top = scored[:MAX_RESULTS]
    out = []
    for score, card in top:
        out.append(
            {
                "slug": card.slug,
                "domain": card.domain,
                "score": score,
                "why": _short_description(card.description),
                "path": str(card.path.relative_to(repo_root)),
            }
        )
    return out


def _format_markdown(results: list[dict], goal: str) -> str:
    if not results:
        return (
            "_<!-- No matching skills found for this goal. Pick 3-5 manually. -->_"
        )
    lines = [f"_Recommendations for goal: {goal!r} (top {len(results)} of max {MAX_RESULTS})_", ""]
    for r in results:
        lines.append(f"- **{r['slug']}** ({r['domain']}) — {r['why']}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Recommend 3-5 skills for the next session.")
    parser.add_argument("--goal", default="", help="Goal text to match against.")
    parser.add_argument(
        "--repo-root",
        default="",
        help="Repo root (defaults to autodetect from CWD).",
    )
    parser.add_argument(
        "--scope",
        choices=["all", "current_domain", "off"],
        default=None,
        help="Override config scope.",
    )
    parser.add_argument(
        "--current-domain",
        default=None,
        help="Used when --scope current_domain (e.g. 'productivity').",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON.")
    parser.add_argument("--sample", action="store_true", help="Run on a fixed goal and exit.")
    args = parser.parse_args(argv)

    if args.sample:
        repo_root = _find_repo_root(Path(__file__).resolve())
        results = recommend(
            goal="implement redaction linter for handoff documents",
            repo_root=repo_root,
            scope="all",
            current_domain=None,
        )
        if args.json:
            print(json.dumps(results, indent=2))
        else:
            print(_format_markdown(results, "implement redaction linter for handoff documents"))
        return 0

    config = config_loader.load_config()
    scope = args.scope or config.get("skill_recommendation_scope", "all")

    repo_root = Path(args.repo_root).resolve() if args.repo_root else _find_repo_root(Path.cwd())
    results = recommend(
        goal=args.goal,
        repo_root=repo_root,
        scope=scope,
        current_domain=args.current_domain,
    )
    if args.json:
        print(json.dumps(results, indent=2))
    else:
        print(_format_markdown(results, args.goal or "(no goal)"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
