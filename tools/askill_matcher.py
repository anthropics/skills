#!/usr/bin/env python3
"""
askill_matcher.py — Zero-dependency BM25 & Semantic Skill Matcher for Agent Skills
Allows AI coding agents (Claude Code, Antigravity, Cursor) to search local skills
and format them directly into XML (<agent_skill>) or system prompt preambles.
"""

import os
import sys
import math
import re
import argparse
from pathlib import Path

def tokenize(text: str) -> list[str]:
    return [w.lower() for w in re.findall(r'[a-zA-Z0-9_-]+', text) if len(w) > 1]

def load_skills(skills_dir: Path) -> list[dict]:
    skills = []
    if not skills_dir.exists():
        return skills
    for p in skills_dir.rglob("SKILL.md"):
        try:
            content = p.read_text(encoding="utf-8", errors="replace")
            name, desc = p.parent.name, ""
            if content.startswith("---"):
                parts = content.split("---", 2)
                if len(parts) >= 3:
                    frontmatter = parts[1]
                    for line in frontmatter.splitlines():
                        if line.startswith("name:"):
                            name = line.replace("name:", "").strip()
                        elif line.startswith("description:"):
                            desc = line.replace("description:", "").strip()
            skills.append({
                "name": name,
                "description": desc,
                "path": str(p),
                "content": content,
                "tokens": tokenize(f"{name} {desc} {p.name}")
            })
        except Exception:
            continue
    return skills

def bm25_search(query: str, skills: list[dict], top_k: int = 5) -> list[dict]:
    q_tokens = tokenize(query)
    if not q_tokens or not skills:
        return skills[:top_k]
    
    N = len(skills)
    avgdl = sum(len(s["tokens"]) for s in skills) / max(1, N)
    k1 = 1.5
    b = 0.75
    
    df = {}
    for t in q_tokens:
        df[t] = sum(1 for s in skills if t in s["tokens"])
        
    scored = []
    for s in skills:
        score = 0.0
        doc_len = len(s["tokens"])
        for t in q_tokens:
            if df[t] == 0:
                continue
            tf = s["tokens"].count(t)
            idf = math.log((N - df[t] + 0.5) / (df[t] + 0.5) + 1.0)
            score += idf * ((tf * (k1 + 1)) / (tf + k1 * (1 - b + b * (doc_len / avgdl))))
        if score > 0:
            scored.append((score, s))
            
    scored.sort(key=lambda x: x[0], reverse=True)
    return [s for _, s in scored[:top_k]]

def main():
    parser = argparse.ArgumentParser(description="BM25 Agent Skill Discovery & Prompt Formatter")
    parser.add_argument("query", nargs="*", help="Query task description")
    parser.add_argument("--skills-dir", default="./skills", help="Directory containing SKILL.md files")
    parser.add_argument("--format", choices=["text", "xml", "system", "json"], default="text", help="Output format")
    parser.add_argument("--top", type=int, default=3, help="Top matches count")
    args = parser.parse_args()

    query_str = " ".join(args.query) if args.query else ""
    skills = load_skills(Path(args.skills_dir))
    if not skills:
        skills = load_skills(Path("."))
        
    results = bm25_search(query_str, skills, top_k=args.top) if query_str else skills[:args.top]

    if args.format == "json":
        print(json.dumps([{"name": r["name"], "description": r["description"], "path": r["path"]} for r in results], indent=2))
    elif args.format == "xml":
        for r in results:
            print(f"<agent_skill name=\"{r['name']}\">\n{r['content']}\n</agent_skill>\n")
    elif args.format == "system":
        print("### RELEVANT AGENT SKILLS ###\n")
        for r in results:
            print(f"#### Skill: {r['name']}\n{r['description']}\n")
    else:
        print(f"Found {len(results)} matching skills for query: '{query_str}'")
        for i, r in enumerate(results, 1):
            print(f"  {i}. {r['name']} - {r['description']} ({r['path']})")

if __name__ == "__main__":
    main()
