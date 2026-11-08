---
name: ios-localization
description: This skill should be used when the user asks to "translate iOS app", "localize xcstrings", "add translations to Localizable.xcstrings", "translate strings to multiple languages", or mentions iOS localization, xcstrings files, or app translation workflows.
---

# iOS Localization Skill

Translate `Localizable.xcstrings` files in iOS projects efficiently using haiku agents for each target language.

## Overview

This skill provides a workflow for translating iOS app strings to multiple languages:
1. Extract strings needing translation
2. Mark non-translatable strings (aspect ratios, brands, etc.)
3. Launch sequential haiku agents for each language
4. Verify completion and fix gaps

## Script Location

All helper scripts are located in `./scripts/` relative to this skill's install directory. Determine the skill's installed path and use it to reference scripts. For example, if installed at `$SKILL_DIR`, run scripts as `python3 $SKILL_DIR/scripts/<script>.py`.

## Quick Start Workflow

### Step 1: Locate the xcstrings File

Find the `Localizable.xcstrings` file in the iOS project:
```bash
find . -name "*.xcstrings" -type f
```

### Step 2: Mark Non-Translatable Strings

Identify and mark strings that should not be translated:

```bash
python3 $SKILL_DIR/scripts/mark_non_translatable.py path/to/Localizable.xcstrings \
  "1:2" "2:3" "3:4" "4:3" "9:16" "16:9" \
  "A4" "A5" "OK" "PDF" \
  "FB Cover" "IG 5:4"
```

Common non-translatable strings:
- Aspect ratios: `1:2`, `16:9`, `4:3`
- Paper sizes: `A4`, `A5`
- Universal terms: `OK`, `PDF`, `USB`
- Brand names: Product names, company names
- Social media formats: `FB Cover`, `IG Post`

### Step 3: Verify Current State

Check translation completion status:
```bash
python3 $SKILL_DIR/scripts/verify_translations.py path/to/Localizable.xcstrings
```

Or specify target languages:
```bash
python3 $SKILL_DIR/scripts/verify_translations.py path/to/Localizable.xcstrings fr,de,es,ja,ko,zh-Hans
```

### Step 4: Launch Translation Agents

For each target language, launch a haiku agent sequentially:

```
Use the Task tool with:
- subagent_type: "general-purpose"
- model: "haiku"
- prompt: Translation instructions (see below)
```

**Translation Agent Prompt Template:**

```
Translate iOS app strings from English to [LANGUAGE] ([LANG_CODE]).

## Instructions

1. Extract strings needing translation:
   python3 $SKILL_DIR/scripts/extract_strings.py path/to/Localizable.xcstrings [LANG_CODE]

2. Translate ALL strings to [LANGUAGE]. Rules:
   - Preserve format specifiers (%lld, %@, %d) exactly
   - Keep & symbol in strings like "& BACKGROUND"
   - Use natural [LANGUAGE] phrasing for a photo editing app

3. Save translations and update:
   cat > /tmp/translations_[LANG_CODE].json << 'EOF'
   { "English key": "Translation", ... }
   EOF
   python3 $SKILL_DIR/scripts/update_translations.py path/to/Localizable.xcstrings [LANG_CODE] /tmp/translations_[LANG_CODE].json

Complete ALL translations. Do not skip any strings.
```

### Step 5: Verify Completion

After all agents complete, verify:
```bash
python3 $SKILL_DIR/scripts/verify_translations.py path/to/Localizable.xcstrings
```

Fix any gaps by launching targeted agents for incomplete languages.

## Helper Scripts

All scripts are located at `./scripts/` relative to this skill's install directory.

### extract_strings.py

Extract strings needing translation for a language:
```bash
python3 $SKILL_DIR/scripts/extract_strings.py <xcstrings_path> <lang_code>
# Output: JSON with {"key": "english_value", ...}
```

### update_translations.py

Update xcstrings with translations:
```bash
python3 $SKILL_DIR/scripts/update_translations.py <xcstrings_path> <lang_code> <translations.json>
```

### verify_translations.py

Check translation completion:
```bash
python3 $SKILL_DIR/scripts/verify_translations.py <xcstrings_path> [lang1,lang2,...]
```

### mark_non_translatable.py

Mark strings as non-translatable:
```bash
python3 $SKILL_DIR/scripts/mark_non_translatable.py <xcstrings_path> "key1" "key2" ...
```

## Common Target Languages

| Priority | Languages |
|----------|-----------|
| Tier 1 | en, zh-Hans, zh-Hant, ja, ko, es, fr, de |
| Tier 2 | pt-BR, it, nl, pl, ru, tr, ar |
| Tier 3 | vi, th, id, ms, cs, da, sv, no, fi |

## Translation Rules

### Always Preserve

- Format specifiers: `%lld`, `%@`, `%d`, `%f`
- Positional arguments: `%1$@`, `%2$d`
- Special symbols in context: `&`, `+`
- Newlines: `\n`

### Keep As-Is (shouldTranslate: false)

- Technical identifiers
- Aspect ratios and dimensions
- Brand and product names
- Universal abbreviations

### Translate

- UI labels and buttons
- Status and error messages
- Feature names and descriptions
- Settings and preferences
- Onboarding text

## Sequential Agent Execution

Launch agents **one at a time** to avoid file conflicts:

```
Order: zh-Hans -> zh-Hant -> ja -> ko -> es -> fr -> de -> ...
```

Each agent:
1. Reads current file state
2. Extracts untranslated strings
3. Translates all strings
4. Updates file with translations

## Troubleshooting

### JSON Parse Errors

If xcstrings file becomes corrupted:
```bash
python3 -m json.tool Localizable.xcstrings > /dev/null
```

### Missing Translations After Agent

Re-run extract to check:
```bash
python3 $SKILL_DIR/scripts/extract_strings.py Localizable.xcstrings <lang_code> | jq 'keys | length'
```

If count > 0, translations are missing. Re-run agent.

### Format Specifier Mismatch

Verify format specifiers match between source and translation. Common issues:
- `%lld` changed to `%d`
- `%@` removed or duplicated
- Positional arguments reordered incorrectly

## Additional Resources

### Reference Files

- **`references/xcstrings-format.md`** - Detailed xcstrings format documentation

### Scripts

- **`scripts/extract_strings.py`** - Extract untranslated strings
- **`scripts/update_translations.py`** - Update xcstrings with translations
- **`scripts/verify_translations.py`** - Verify translation completion
- **`scripts/mark_non_translatable.py`** - Mark non-translatable strings
