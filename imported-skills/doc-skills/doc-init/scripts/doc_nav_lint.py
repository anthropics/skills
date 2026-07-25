#!/usr/bin/env python3
"""
检查项目文档导航和 doc-init 生成物的结构一致性。

该脚本只报告问题，不自动改写文件；需要修复导航时配合 upsert_agents_nav.py 使用。

本脚本同时是 doc-init 与其它文档治理类 skill（如 doc-compact）之间的共享检查入口：
- 涉及 AGENTS.md/CLAUDE.md 结构、孤儿文档、自我导航、反向全局引用等检查只在此维护一份；
- 其它 skill 应直接调用本脚本获取结果，不要另写一份相近但写法不同的检查逻辑。
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


DOC_LINK_RE = re.compile(r"(?:\[[^\]]+\]\()?`?(\.?/?(?:docs|specs)/[^\s`)]+?\.md)`?\)?")
GLOBAL_REF_RE = re.compile(r"(@?\s*(?:~|\$HOME|/Users/[^/\s`，。；；、)]+)/(?:\.claude|\.codex|\.config/opencode)/[^\s`，。；；、)]+)", re.I)
NEGATIVE_EXAMPLE_RE = re.compile(r"(不要|不应|禁止|例如|示例|常见路径|路径形态|不是)")
SELF_NAV_RE = re.compile(r"(何时该读|什么时候该读|前必读|前读|必读)")
FORBIDDEN_INDEX_NAMES = {"TABLE_INDEX.md", "CODE_INDEX.md"}

# doc-init 在根 AGENTS.md 维护的记账段标题；这两段是 Step 6 续接判定的唯一依据，
# 任何其它 skill（如 doc-compact）整理/压缩文档时都不得删除、折叠或改写它们。
DOMAIN_MAP_HEADING_RE = re.compile(r"^(#{1,4})\s*领域地图（doc-init）\s*$", re.M)
BACKLOG_HEADING_RE = re.compile(r"^(#{1,4})\s*待补充知识库（doc-init backlog）\s*$", re.M)

PRUNE_DIR_NAMES = {
    "node_modules", "target", "build", "dist", "out", ".build",
    ".git", ".claude", ".stversions", "vendor",
}


def rel(path: Path, root: Path) -> str:
    return path.relative_to(root).as_posix()


def add_issue(issues: list[dict[str, Any]], severity: str, code: str, message: str, path: str = "", line: int | None = None) -> None:
    item: dict[str, Any] = {
        "severity": severity,
        "code": code,
        "message": message,
    }
    if path:
        item["path"] = path
    if line is not None:
        item["line"] = line
    issues.append(item)


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def normalize_doc_path(value: str) -> str:
    value = value.strip().replace("\\", "/")
    if value.startswith("./"):
        value = value[2:]
    return value


def find_protected_sections(agents_text: str) -> dict[str, Any]:
    domain_map_match = DOMAIN_MAP_HEADING_RE.search(agents_text)
    backlog_match = BACKLOG_HEADING_RE.search(agents_text)
    protected = []
    if domain_map_match:
        protected.append(domain_map_match.group(0).strip())
    if backlog_match:
        protected.append(backlog_match.group(0).strip())
    return {
        "domain_map_present": domain_map_match is not None,
        "backlog_present": backlog_match is not None,
        "protected_sections": protected,
    }


def collect_index_text(root: Path, agents_text: str) -> str:
    """汇总「索引文本」：根 AGENTS.md + 所有 README.md + 所有 *_INDEX.md。

    与 doc-compact/scripts/audit.sh 的检查 E 保持同一套并集逻辑，避免两边各算一份、
    结果不一致——任何一边改了并集规则，都要同步改另一边。
    """
    parts = [agents_text]
    for sub in ("docs", "specs"):
        sub_dir = root / sub
        if not sub_dir.exists():
            continue
        for p in sub_dir.rglob("*.md"):
            if p.name == "README.md" or p.name.endswith("_INDEX.md"):
                try:
                    parts.append(p.read_text(encoding="utf-8", errors="ignore"))
                except OSError:
                    continue
    return "\n".join(parts)


def lint(root: Path) -> dict[str, Any]:
    issues: list[dict[str, Any]] = []
    agents = root / "AGENTS.md"
    claude = root / "CLAUDE.md"

    agents_text = ""
    protected_info = {"domain_map_present": False, "backlog_present": False, "protected_sections": []}
    if not agents.exists():
        add_issue(issues, "error", "missing-agents", "项目根目录缺少 AGENTS.md", "AGENTS.md")
    else:
        agents_text = agents.read_text(encoding="utf-8", errors="ignore")
        protected_info = find_protected_sections(agents_text)
        if "文档导航" not in agents_text:
            add_issue(issues, "error", "missing-doc-nav", "AGENTS.md 缺少「文档导航」章节", "AGENTS.md")
        for current_line, line in enumerate(agents_text.splitlines(), start=1):
            if NEGATIVE_EXAMPLE_RE.search(line):
                continue
            if not line.lstrip().startswith("@"):
                continue
            for match in GLOBAL_REF_RE.finditer(line):
                add_issue(
                    issues,
                    "error",
                    "global-ref-in-project-agents",
                    f"项目根 AGENTS.md 不应引用用户级或全局指令文件：{match.group(1).strip()}",
                    "AGENTS.md",
                    current_line,
                )

    if claude.exists():
        claude_text = claude.read_text(encoding="utf-8", errors="ignore").strip()
        if claude_text != "@AGENTS.md":
            add_issue(issues, "error", "invalid-claude-md", "项目根 CLAUDE.md 应只包含单行 @AGENTS.md", "CLAUDE.md")
    else:
        add_issue(issues, "warning", "missing-claude-md", "项目根目录缺少 CLAUDE.md", "CLAUDE.md")

    docs_files: list[Path] = []
    found_docs_dir = False
    for sub in ("docs", "specs"):
        sub_dir = root / sub
        if sub_dir.exists():
            found_docs_dir = True
            docs_files.extend(sorted(p for p in sub_dir.rglob("*.md") if p.is_file()))
    if not found_docs_dir:
        add_issue(issues, "warning", "missing-docs-dir", "项目根目录缺少 docs/ 目录", "docs")

    referenced_docs = set()
    if agents_text:
        for match in DOC_LINK_RE.finditer(agents_text):
            doc_path = normalize_doc_path(match.group(1))
            referenced_docs.add(doc_path)
            if not (root / doc_path).exists():
                add_issue(
                    issues,
                    "error",
                    "dead-doc-link",
                    f"AGENTS.md 导航引用的文档不存在：{doc_path}",
                    "AGENTS.md",
                    line_number(agents_text, match.start()),
                )

    # 孤儿文档判定的索引文本 = 根 AGENTS.md ∪ 所有 README.md ∪ 所有 *_INDEX.md（合法二级索引）。
    # 只用根 AGENTS.md 会把做了两级索引的项目里全部二级文档误报成孤儿。
    index_text = collect_index_text(root, agents_text)

    for doc in docs_files:
        doc_rel = rel(doc, root)
        if doc.name in FORBIDDEN_INDEX_NAMES:
            add_issue(issues, "warning", "global-index-default", f"发现全局索引文档，确认是否真有必要：{doc_rel}", doc_rel)
            continue
        if doc.name == "README.md":
            continue
        if doc.name.endswith("_INDEX.md"):
            # 具名二级索引自身经根 AGENTS.md 引用即合规，不对自己做孤儿检查
            continue
        if doc.name not in index_text:
            add_issue(issues, "warning", "orphan-doc", f"docs//specs/ 下文档未被根 AGENTS.md 或任何二级索引引用：{doc_rel}", doc_rel)

        text = doc.read_text(encoding="utf-8", errors="ignore")
        for match in SELF_NAV_RE.finditer(text):
            line = line_number(text, match.start())
            add_issue(
                issues,
                "warning",
                "self-navigation-in-doc",
                "docs/ 内部文档疑似重复书写「何时该读 / 必读」自我导航，优先改成文档定位或覆盖范围",
                doc_rel,
                line,
            )
            break

    return {
        "root": str(root),
        "summary": {
            "errors": sum(1 for item in issues if item["severity"] == "error"),
            "warnings": sum(1 for item in issues if item["severity"] == "warning"),
            "docs_count": len(docs_files),
            "referenced_docs_count": len(referenced_docs),
            **protected_info,
        },
        "issues": issues,
    }


def find_project_roots(root: Path) -> list[Path]:
    """递归找出所有包含 AGENTS.md 的目录，跳过常见构建产物/第三方/备份目录。"""
    roots: list[Path] = []
    if (root / "AGENTS.md").exists():
        roots.append(root)
    for dirpath in sorted(root.rglob("*")):
        if not dirpath.is_dir():
            continue
        if any(part in PRUNE_DIR_NAMES for part in dirpath.relative_to(root).parts):
            continue
        if dirpath == root:
            continue
        if (dirpath / "AGENTS.md").exists():
            roots.append(dirpath)
    return roots


def format_text(results: list[dict[str, Any]]) -> str:
    """输出无需 jq 即可被 shell grep/解析的纯文本格式，一行一条。"""
    lines = []
    for data in results:
        for item in data["issues"]:
            lines.append(
                "\t".join(
                    [
                        item["severity"],
                        item["code"],
                        item.get("path", ""),
                        str(item.get("line", "")),
                        item["message"],
                        data["root"],
                    ]
                )
            )
        s = data["summary"]
        lines.append(
            "\t".join(
                [
                    "SUMMARY",
                    f"errors={s['errors']}",
                    f"warnings={s['warnings']}",
                    f"domain_map_present={s['domain_map_present']}",
                    f"backlog_present={s['backlog_present']}",
                    data["root"],
                ]
            )
        )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="检查项目文档导航结构")
    parser.add_argument("--root", default=".", help="项目根目录")
    parser.add_argument("--recursive", action="store_true", help="递归查找所有含 AGENTS.md 的目录并逐一检查（多模块项目用）")
    parser.add_argument("--output", help="输出文件；缺省打印到 stdout")
    parser.add_argument("--format", choices=["json", "text"], default="json", help="输出格式；text 便于 shell grep，不需要 jq")
    parser.add_argument("--fail-on-error", action="store_true", help="存在 error 时返回非 0")
    args = parser.parse_args()

    root = Path(args.root).expanduser().resolve()
    if not root.exists() or not root.is_dir():
        print(f"错误：项目根目录不存在或不是目录：{root}")
        return 2

    if args.recursive:
        roots = find_project_roots(root) or [root]
    else:
        roots = [root]

    results = [lint(r) for r in roots]
    total_errors = sum(r["summary"]["errors"] for r in results)

    if args.format == "text":
        text = format_text(results)
    else:
        payload: Any = results[0] if len(results) == 1 else {"projects": results}
        text = json.dumps(payload, ensure_ascii=False, indent=2)

    if args.output:
        Path(args.output).expanduser().write_text(text + "\n", encoding="utf-8")
    else:
        print(text)
    if args.fail_on_error and total_errors:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
