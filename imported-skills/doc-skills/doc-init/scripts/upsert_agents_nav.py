#!/usr/bin/env python3
"""
幂等新增或更新项目根 AGENTS.md 的文档导航条目，或登记待补充 backlog 条目。

普通文档导航模式（默认）：
  upsert_agents_nav.py --root . --path docs/CUSTOMER_KNOWLEDGE_BASE.md --when-to-read "改客户域前"

待补充 backlog 模式（--backlog）：
  upsert_agents_nav.py --root . --backlog --name "渠道体系 KB" --anchor "src/channels/" --when-to-read "改任意渠道接入前"
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


NAV_HEADING_RE = re.compile(r"^(#{1,4})\s*文档导航\s*$", re.M)
BACKLOG_HEADING_RE = re.compile(r"^(#{1,4})\s*待补充知识库（doc-init backlog）\s*$", re.M)


def normalize_path(path: str) -> str:
    value = path.strip().replace("\\", "/")
    if value.startswith("./"):
        value = value[2:]
    return value


def ensure_sentence_end(text: str) -> str:
    text = text.strip()
    if text and text[-1] not in "。.!！?？":
        text += "。"
    return text


def make_nav_line(doc_path: str, when_to_read: str) -> str:
    return f"- `{doc_path}`：{ensure_sentence_end(when_to_read)}"


def make_backlog_line(name: str, anchor: str, when_to_read: str) -> str:
    return f"- [待补充] {name} —— 入口锚点：{anchor}；触发场景：{ensure_sentence_end(when_to_read)}"


def find_section_end(text: str, heading_match: re.Match[str]) -> int:
    """返回 heading 所在段落的结束位置（下一个同级或更高级 heading 的起始）。"""
    heading_level = len(heading_match.group(1))
    rest = text[heading_match.end():]
    next_heading = re.search(rf"^#{{1,{heading_level}}}\s+\S.*$", rest, re.M)
    if next_heading:
        return heading_match.end() + next_heading.start()
    return len(text)


def upsert(root: Path, doc_path: str, when_to_read: str) -> str:
    """在 AGENTS.md 的"文档导航"段幂等写入一条导航条目。"""
    agents = root / "AGENTS.md"
    doc_path = normalize_path(doc_path)
    new_line = make_nav_line(doc_path, when_to_read)

    if agents.exists():
        text = agents.read_text(encoding="utf-8", errors="ignore")
    else:
        text = "# 项目说明\n\n## 文档导航\n\n"

    # 若条目已存在则原地替换，否则追加到导航段末尾
    line_pattern = re.compile(
        rf"^[-*]\s+.*(?:`|\()\.?/?{re.escape(doc_path)}(?:`|\)).*$", re.M
    )
    if line_pattern.search(text):
        text = line_pattern.sub(new_line, text, count=1)
    else:
        match = NAV_HEADING_RE.search(text)
        if not match:
            if not text.endswith("\n"):
                text += "\n"
            text += "\n## 文档导航\n\n" + new_line + "\n"
        else:
            section_end = find_section_end(text, match)
            before = text[:section_end].rstrip()
            after = text[section_end:]
            text = before + "\n" + new_line + "\n" + after

    agents.write_text(text.rstrip() + "\n", encoding="utf-8")
    return new_line


def upsert_backlog(root: Path, name: str, anchor: str, when_to_read: str) -> str:
    """在 AGENTS.md 的"待补充知识库（doc-init backlog）"段幂等写入一条 backlog 条目。"""
    agents = root / "AGENTS.md"
    new_line = make_backlog_line(name, anchor, when_to_read)

    if agents.exists():
        text = agents.read_text(encoding="utf-8", errors="ignore")
    else:
        text = "# 项目说明\n\n"

    # 若同名条目已存在则原地替换（按领域名匹配）
    escaped_name = re.escape(name)
    line_pattern = re.compile(
        rf"^[-*]\s+\[待补充\]\s+{escaped_name}.*$", re.M
    )
    if line_pattern.search(text):
        text = line_pattern.sub(new_line, text, count=1)
    else:
        match = BACKLOG_HEADING_RE.search(text)
        if not match:
            # 创建 backlog 段，追加到文件末尾
            if not text.endswith("\n"):
                text += "\n"
            text += "\n## 待补充知识库（doc-init backlog）\n\n" + new_line + "\n"
        else:
            section_end = find_section_end(text, match)
            before = text[:section_end].rstrip()
            after = text[section_end:]
            text = before + "\n" + new_line + "\n" + after

    agents.write_text(text.rstrip() + "\n", encoding="utf-8")
    return new_line


def main() -> int:
    parser = argparse.ArgumentParser(description="幂等更新根 AGENTS.md 文档导航或 backlog 条目")
    parser.add_argument("--root", default=".", help="项目根目录")
    parser.add_argument(
        "--backlog",
        action="store_true",
        help="写入待补充 backlog 段，而非文档导航段",
    )
    # 普通导航模式参数
    parser.add_argument("--path", help="要登记的文档路径，例如 docs/CUSTOMER_KNOWLEDGE_BASE.md")
    # backlog 模式参数
    parser.add_argument("--name", help="（backlog 模式）领域名，例如「渠道体系 KB」")
    parser.add_argument("--anchor", help="（backlog 模式）入口锚点，例如 src/channels/")
    # 两种模式共用
    parser.add_argument("--when-to-read", required=True, help="何时该读/触发场景描述")
    args = parser.parse_args()

    root = Path(args.root).expanduser().resolve()
    if not root.exists() or not root.is_dir():
        print(f"错误：项目根目录不存在或不是目录：{root}")
        return 2

    if args.backlog:
        if not args.name or not args.anchor:
            print("错误：--backlog 模式需要同时提供 --name 和 --anchor")
            return 2
        line = upsert_backlog(root, args.name, args.anchor, args.when_to_read)
        print(f"已登记 backlog：{line}")
    else:
        if not args.path:
            print("错误：普通导航模式需要提供 --path")
            return 2
        line = upsert(root, args.path, args.when_to_read)
        print(f"已更新文档导航：{line}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
