# Catalog Collection (Local, Before Any Cloud Run)

> Purpose: the LoomLoom cloud pipeline's `text-generate` steps have **no web
> access**. Any cloud run that needs real course data MUST receive it as input.
> This document defines how to collect and quality-gate the official catalog
> locally, before spending the user's money on a cloud run.

## Why

Verified 2026-08: submitting a cloud run without a pre-collected catalog makes
the model reply "无法查询" or emit unverified memory-based course codes
(e.g. 60/100 rows with unverified codes, 40/100 empty shells in a real batch).
Never repeat that.

## Procedure

1. **Research the official catalog** with WebSearch / WebFetch, preferring the
   university's own handbook / unit pages (e.g. `sydney.edu.au/units/*`,
   `*handbook*` pages). Extract: course code, name, credits, session(s),
   prerequisites, prohibitions, assessment summary.

### BEFORE RETURNING EMPTY — 7-step search protocol (mandatory)

Never output an empty catalog, "not found", or "please paste the catalog" without
first exhausting ALL of these sources, in this order:

1. **Official university handbook** — WebSearch: `<university> handbook <program>`
2. **Faculty website** — `<faculty> course units <program>`
3. **Program structure page** — `<university> <program> program structure`
4. **Course handbook page** (per course) — `<course code> <university> handbook`
5. **Prerequisites** — `<course code> prerequisites <university>`
6. **Assessment** — `<course code> assessment <university>`
7. **Timetable / class schedule** (per course, **MANDATORY**) — `<course code> <university> timetable 2026` or `<university> timetable <program>`
   **Why this is MANDATORY**: the cloud pipeline's schedule step needs meeting times
   (day, start_time, end_time) to generate a timetable. Without this data, it returns
   a default timetable with only 1-2 sessions per course — the schedule will be
   incomplete and marked `"default_timetable": true`. You would need to either
   accept the default or collect timetable data locally after the run (which costs
   the same ¥5, but the cloud run already paid).
   **Collecting timetable data BEFORE the cloud run means one submission = one complete result.**

Only if ALL seven fail should you return empty or ask the user to paste the catalog.

This is a hard requirement: the cloud pipeline (or any downstream agent) can only
work with the text you hand it. If you return empty without exhausting these six
searches, the downstream pipeline will produce placeholder output and the user
wastes money/time.

2. **Quality gate — pass ALL of (mode-aware, matching cloud v5.8 semantics):**
   - collected text ≥ 500 characters (Chinese or English)
   - Course count (MODE-AWARE):
     - planning_mode = `ai_recommend`: ≥ 5 real, named courses with codes
       (e.g. `CHEM1111`, `MATH1021`)
     - planning_mode = `user_decided`: ≥ 1 real course with a code — the user's
       own selection IS a complete input; a short list of 1-4 chosen courses
       is NOT "truncated" and must NOT be treated as a gate failure
   - **Timetable data present for 100% of target courses** (new courses without published timetable can be exempted with a `TBC` marker)
     - Existence: each target course has ≥1 TIMETABLE entry
     - Completeness: total TIMETABLE entries ≥ 2 × target course count (catches the "only 1 lecture, no lab" case)
   - Catalog text is valid UTF-8 and contains no unprintable control characters (except \n, \t, \r)
   - source URLs recorded for traceability

   **Timetable data format (must be in the catalog text)**:
   ```
   TIMETABLE:
   BIOL1020 | Lecture | Monday | 10:00-11:00 | weeks 1-13
   BIOL1020 | Tutorial | Wednesday | 10:00-11:00 | weeks 1-13
   BIOL1020 | Practical | Friday | 09:00-12:00 | weeks 1-12
   CHEM1100 | Lecture | Monday | 14:00-15:00 | weeks 1-13
   CHEM1100 | Lab | Thursday | 13:00-16:00 | weeks 2,4,6,8,10,12
   ```
   Each line: `course_code | session_type | day | start_time-end_time | week_range`

3. If the gate fails: try a second source (e.g. official unit pages, archived
   handbooks). If still failing after all six searches, **ask the user to paste
   their official 培养方案/handbook text** — do not proceed with an empty catalog.
4. Structure the catalog as the `course_catalog` input for the cloud run
   (one column per row in workbook mode, or the `course_catalog` field).
5. Record the gate result and source URLs in the run notes.

### User confirmation loop (MANDATORY — before any cloud submission)

After the catalog passes the quality gate, BEFORE running `loomloom market quote`
or requesting fee confirmation, present a collection summary to the user:

1. **Show what was collected**: course codes + names, the source URLs used,
   quality-gate results (chars / course count / timetable coverage), and any
   NOT_FOUND / TBC items.
2. **Ask**: "以上课程目录来自官方来源（来源链接已记录）。确认无误后提交云端（¥0.5/次）？
   如有缺漏请告诉我，我会补充后再提交。"
3. **User confirms** → proceed to quote + fee confirmation.
4. **User reports missing/wrong courses** → re-collect those courses, re-run the
   gate, show the updated summary, ask again. Loop until confirmed or abandoned.
5. **Collection failed / gate failed** → do NOT show a fake summary; tell the user
   honestly and ask them to paste their official handbook text.

### user_decided mode — chosen-courses column (agent fills it, MANDATORY)

When planning_mode = `user_decided`:
- Extract the chosen course codes from the user's request/conversation (or ask
  "你决定选哪几门课？请告诉我课程代码。").
- Write them into the chosen-courses column before submitting to the cloud.
- NEVER submit user_decided with an empty chosen column — the cloud pipeline will
  mark it `partial` and return an empty result, wasting the user's money.

## Two-tier strategy (optional, for large catalogs)

If the raw catalog text is too large for a single cell or too messy to paste:
- Tier 1: WebFetch the raw official text (local agent).
- Tier 2: if structuring is needed, use a cheap/free model to summarize into
  the canonical `code | name | credits | session | prereq | prohibition`
  lines, then pass the structured text to the cloud run.

## Rule

Never submit a cloud run with an empty or failed catalog. It produces
placeholder output and wastes the user's money.
