import json
import re
from pathlib import Path

SUITE = Path(__file__).resolve().parents[1]
REPOSITORY = SUITE.parents[2]
GUIDES = {
    "fr": REPOSITORY / "docs/guide-cloud-estimation.md",
    "en": REPOSITORY / "docs/cloud-estimation-guide.md",
}
SECTIONS = {
    "fr": (
        "Pourquoi utiliser la suite",
        "Ce que la suite produit",
        "Choisir le bon skill",
        "Installation",
        "Préparer le brief",
        "Parcours standard",
        "Prompts copiables",
        "Exemples de bout en bout",
        "Lire et contrôler le XLSX",
        "Limites et sécurité",
        "Dépannage",
    ),
    "en": (
        "Why use the suite",
        "What the suite produces",
        "Choose the right skill",
        "Installation",
        "Prepare the brief",
        "Standard workflow",
        "Copy-ready prompts",
        "End-to-end examples",
        "Read and validate the XLSX",
        "Limits and safety",
        "Troubleshooting",
    ),
}
REGISTRY = json.loads(
    (SUITE / "tooling/domain-registry.json").read_text(encoding="utf-8")
)
SKILLS = tuple(item["name"] for item in REGISTRY["skills"])
LOCAL_LINK = re.compile(r"\[[^]]+\]\(([^)]+)\)")


def text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_bilingual_guides_have_the_complete_navigation_contract():
    for language, path in GUIDES.items():
        content = text(path)
        for heading in SECTIONS[language]:
            assert f"## {heading}" in content
        for name in SKILLS:
            assert content.count(f"`{name}`") >= 2


def test_every_guide_preserves_the_delivery_and_evidence_contract():
    required = (".xlsx", "JH", "JH/month", "source")
    for path in GUIDES.values():
        content = text(path)
        for token in required:
            assert token.lower() in content.lower()
        assert "cloud-estimation-orchestrator" in content
        assert "à chiffrer" in content.lower() or "to be priced" in content.lower()


def test_all_local_guide_links_resolve():
    for path in (*GUIDES.values(), SUITE / "README.md"):
        for target in LOCAL_LINK.findall(text(path)):
            clean = target.split("#", 1)[0]
            if not clean or "://" in clean or clean.startswith("mailto:"):
                continue
            assert (path.parent / clean).resolve().exists(), (path, target)


def test_suite_readme_links_both_user_guides():
    content = text(SUITE / "README.md")
    assert "../../../docs/guide-cloud-estimation.md" in content
    assert "../../../docs/cloud-estimation-guide.md" in content


def test_guides_have_matching_skill_and_prompt_coverage():
    french = text(GUIDES["fr"])
    english = text(GUIDES["en"])
    for name in SKILLS:
        assert french.count(f"`{name}`") == english.count(f"`{name}`")
    assert french.count("```text") == english.count("```text") == 14
