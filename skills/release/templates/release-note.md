# Release Note Templates

This file defines multiple release note format templates. The skill auto-detects
the appropriate format from the project's historical GitHub Releases, or uses the
`release_note_style` setting in the project's `.release.json`.

---

## Variant: `bilingual`

For projects that maintain bilingual (Chinese/English) release notes.
Detection signal: release body contains both CJK characters AND Latin paragraphs.

```markdown
# v{version} Release Notes

{project_name} v{version}。{summary_zh}。
{project_name} v{version}. {summary_en}.

---

{body}

---

## 验证 / Validation

{validation}

---

**完整 CHANGELOG** 见 [CHANGELOG.md]({changelog_url})。

**Full Changelog**: https://github.com/{owner}/{repo}/compare/{prev_version}...{version}
```

### Body Format

Each section from CHANGELOG becomes a bilingual block:

```markdown
## {section_zh} / {section_en}

- {point_zh}
- {point_en}

**涉及文件 / Files**:
`File.swift`, `File.swift`
```

### Variables

| Variable | Source |
|----------|--------|
| `{version}` | Tag name (vX.Y.Z) |
| `{project_name}` | From README.md heading or `.release.json` |
| `{summary_zh}` | First line of CHANGELOG entry, or from `summary` field in `.release.json` |
| `{summary_en}` | English translation of summary, or from `summary_en` in `.release.json` |
| `{body}` | Generated from CHANGELOG sections in bilingual format |
| `{validation}` | From `.release.json` `validation` field, or auto-generated from build command |
| `{changelog_url}` | `https://github.com/{owner}/{repo}/blob/main/CHANGELOG.md` |
| `{prev_version}` | Previous tag name |
| `{owner}/{repo}` | From git remote |

---

## Variant: `simple`

For projects with single-language release notes.
Detection signal: single language, structured with "What's Changed" or similar headings.

```markdown
# {version} Release Notes

{project_name} {version}.

---

## Changes

{body}

---

## Validation

{validation}

---

**Full Changelog**: https://github.com/{owner}/{repo}/compare/{prev_version}...{version}
```

---

## Variant: `changelog`

For projects that simply dump the CHANGELOG entry as the release body.
Detection signal: release body starts with `## [v` or matches Keep-a-Changelog format.

```markdown
{body}

---

**Full Changelog**: https://github.com/{owner}/{repo}/compare/{prev_version}...{version}
```
