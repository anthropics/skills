# Ninth Circuit Brief Data Map

This reference links every data file the brief generator reads so that each section can be populated with **exact text** and record citations.

## Core JSON Inputs (`legal_brief_system/data/`)

| File | Required | Purpose | Key Fields |
| --- | --- | --- | --- |
| `case_info.json` | ✅ | Case numbers, party names, disclosure text, jurisdictional facts, signature block data. | `case.ninth_circuit_number`, `parties.appellant`, `jurisdiction.*`, `conclusion.text` |
| `issues_presented.json` | ✅ | Issues, headings, and standards of review. | `issues[].number`, `issues[].issue_statement`, `issues[].standard_of_review`, `issues[].standard_citation` |
| `arguments.json` | ✅ | Argument headings and citation lists used to build the outline. | `arguments[].number`, `arguments[].heading`, `arguments[].subarguments[].letter`, `arguments[].subarguments[].citations[]` |
| `argument_content.json` | ✅ | Exact narrative text for the Introduction, Summary of Argument, and each argument/subargument body. | `content_sections.introduction.content`, `content_sections.summary_of_argument.content`, `content_sections.arguments["I"].content`, `content_sections.arguments["I"].A.content`, etc. |
| `evidence_pool.json` | ✅ | Master fact statements with ER cites. Drives Statement of the Case and inserts fact paragraphs under each argument heading. | `facts[].statement`, `facts[].record_cite`, `facts[].used_in_sections[]`, `facts[].date`, `facts[].category` |
| `timeline.json` | ✅ (fallback) | Chronology used only when no `statement_of_case` facts are mapped. | `events[].date`, `events[].event`, `events[].er_cite` |
| `authorities.json` | ✅ | Populates the Table of Authorities. | `cases[]`, `statutes[]`, `rules[]`, `constitutional_provisions[]` |

## `used_in_sections` Keys for `evidence_pool.json`

The generator copies facts into any section listed in each fact's `used_in_sections`. Supported keys are:

- `statement_of_case`
- `argument_I`, `argument_II`, `argument_III` (Roman numerals must match `arguments.json`)
- `argument_I_A`, `argument_I_B`, `argument_II_A`, etc. for subarguments

> Example: To place fact `F002` under Argument I.A, include both `"argument_I"` and `"argument_I_A"` in its `used_in_sections` array. Every fact remains verbatim—no paraphrasing occurs.

## Output Targets

- `legal_brief_system/output/` – First DOCX copy from `generate_brief.py`
- `OUTBOX/briefs/` – Primary copy named `{Case}-{Filing}-{timestamp}.docx`
- `OUTBOX/chronological/` – Read-only chronological log `{timestamp}-{Case}-{Filing}.docx`

## Quality Checklist

1. **Data freshness:** Update JSON files before running `generate_brief.py`.
2. **Exact quotes:** All substantive text must originate from the JSON files; do not rewrite in prompts.
3. **Section coverage:** Confirm every required section in FRAP 28 has either JSON-driven text or an intentional placeholder.
4. **Citation integrity:** Ensure each fact includes an `record_cite` value (e.g., `ER-102`). Facts lacking cites will be inserted without parentheticals.
