# Interaction Flow — 7-Step Guided Conversation

This document defines the exact conversation script for Agents using the
University Course Planner skill. Follow each step in order. Ask one question
at a time. Do not proceed to the next step until the current one is answered.

---

## Step 1 — University Name

**Prompt:** "What university are you studying at? Please give me the full name."

**Why:** The university name is used to search for the course catalog, credit
system, and academic calendar online.

**Example answer:** "University of Melbourne"

If the student is undecided, ask for 2-3 candidates and pick one.

---

## Step 2 — Country / Education System

**Prompt:** "Which country or credit system does your university use? Pick one:
US Credits, ECTS, Australian Credit Points, UK Credits (CATS), Canadian Credits,
Singapore Modular Credits, Hong Kong Credits, Chinese Credits, or Other."

**Why:** Different countries use different credit frameworks. This affects how
we calculate total credits and compare against degree requirements.

**Example answer:** "Australian Credit Points"

If the student doesn't know, infer from the university's country.

---

## Step 3 — Major / Field of Study

**Prompt:** "What is your major or field of study?"

**Why:** To filter relevant courses from the catalog and match prerequisite
chains.

**Example answer:** "Computer Science"

---

## Step 4 — Year Level

**Prompt:** "What year of study are you in? Year 1, Year 2, Year 3, Year 4,
or Master?"

**Why:** Determines course difficulty level and which prerequisites are
likely already met.

**Example answer:** "Year 1"

---

## Step 5 — Planning Mode

**Prompt:** "Do you want me to recommend courses for you (AI recommend), or have
you already chosen your courses and just need scheduling (user decided)?"

**Why:** Determines whether the AI selects courses or validates the student's
choices.

**Example answer:** "AI recommend"

### Step 5a (if AI recommend) — Goals & Schedule Preferences

**Prompt:** "What are your academic goals and schedule preferences? For example:
GPA-focused, employment-focused, interest-driven, grad-school prep, or easy
load. For schedule: no 8am classes, three-day concentrated, evenly distributed,
etc."

**Example answer:** "Goals: GPA. Preferences: no 8am, lunch break 12-1pm,
evenly distributed across the week."

### Step 5b (if user decided) — Chosen Courses

**Prompt:** "List the course codes you have chosen, in JSON array format.
Example: [\"MATH101\", \"COMPSCI230\", \"PHYS150\"]"

---

## Step 6 — Semester Information

**Prompt:** "What semester are you planning for? Please provide the semester
code, start date, end date, and number of teaching weeks. Example: 2026-S1,
starts 2026-02-24, ends 2026-06-05, 12 teaching weeks."

**Why:** Used to expand the weekly schedule to cover the full semester with
correct dates.

**Example answer:** "2026-S1, starts 2026-02-24, ends 2026-06-05, 12 teaching weeks"

---

## Step 7 — Generate Excel

After collecting all inputs:

1. If LoomLoom CLI is available, run the 3-step cloud pipeline:
   - Step 1: Course Catalog Analysis (stp_catalog)
   - Step 2: Course Recommendation (stp_recommend)
   - Step 3: Schedule Generation (stp_schedule)
   Then pass the combined JSON output to `scripts/generate_excel.py`.

2. If LoomLoom is not available, use local reasoning:
   - The Agent analyzes the course catalog using web search
   - The Agent generates recommendations based on the student's goals
   - The Agent creates a weekly schedule with conflict detection
   - Save the combined JSON to a temp file
   - Run `scripts/generate_excel.py` on the JSON file

3. Validate the output:
   ```bash
   python3 scripts/validate_schedule.py <excel_file.xlsx>
   ```

4. Deliver the .xlsx file to the student.

---

## Optional: Course Catalog Upload

At any point during steps 1-6, if the student has a course catalog file (PDF,
text, or HTML), accept it and pass it as the `course_catalog` input field.
This significantly improves accuracy when the university's catalog is not
easily searchable online.
