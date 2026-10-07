"""Mechanical packaging checks only; these do not prove agent behavior."""

from pathlib import Path
import re
from types import SimpleNamespace

import pytest
import yaml

ROOT = Path(__file__).parents[1]
RESOURCE = re.compile(r"(?:\]\(|`)((?:references|scripts|assets)/[^\s)`#]+)")
SCAFFOLD = re.compile(r"\b(?:TODO|TBD|FIXME)\b|\[INSERT[^\]]*\]", re.I)


def inspect_skill(directory):
    entrypoint = directory / "SKILL.md"
    assert entrypoint.is_file(), f"Missing skill entrypoint: {entrypoint}"
    raw = entrypoint.read_bytes()
    assert b"\r" not in raw, f"Skill frontmatter must use LF: {entrypoint}"
    text = raw.decode("utf-8")
    header = re.match(r"\A---\n(.*?)\n---(?:\n|\Z)", text, re.S)
    assert header, f"Invalid frontmatter delimiters: {entrypoint}"
    frontmatter = yaml.safe_load(header.group(1))
    assert isinstance(frontmatter, dict), f"Expected frontmatter mapping: {entrypoint}"
    assert isinstance(frontmatter.get("name"), str)
    assert isinstance(frontmatter.get("description"), str)
    assert re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", frontmatter["name"])
    assert len(frontmatter["name"]) < 64
    missing = {"references": [], "scripts": [], "assets": []}
    scaffold = []
    inspected = set()
    pending = [entrypoint]
    while pending:
        document = pending.pop()
        if document in inspected:
            continue
        inspected.add(document)
        content = document.read_text(encoding="utf-8")
        scaffold.extend(f"{document.name}:{match.group(0)}" for match in SCAFFOLD.finditer(content))
        for relative in RESOURCE.findall(content):
            target = (directory / relative).resolve()
            assert target.is_relative_to(directory.resolve()), f"Escaping resource path: {relative}"
            if not target.is_file():
                missing[relative.split("/", 1)[0]].append(relative)
            elif target.suffix == ".md":
                pending.append(target)
    return SimpleNamespace(
        frontmatter=frontmatter,
        unfinished_scaffold_markers=scaffold,
        missing_references=missing["references"],
        missing_scripts=missing["scripts"],
        missing_assets=missing["assets"],
    )


@pytest.fixture
def load_skill():
    return lambda name: inspect_skill(ROOT / name)


def test_orchestrator_has_required_enforcement(load_skill):
    # A missing entrypoint, invalid frontmatter or dangling resource fails here.
    # Decision quality and enforcement need an independent forward-test.
    skill = load_skill("cloud-estimation-orchestrator")
    assert skill.frontmatter["name"] == "cloud-estimation-orchestrator"
    assert skill.frontmatter["description"].strip()
    assert skill.unfinished_scaffold_markers == []
    assert skill.missing_references == []
    assert skill.missing_scripts == []
    assert skill.missing_assets == []
