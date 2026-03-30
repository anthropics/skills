# Cross-MCP Integration Plays

Combine linkedin-intel with other connected MCP servers and skills
for deeper research. Each play lists the tools from each source.

---

## 1. Company Intel Brief (LinkedIn + /company-research)

Full FBI-grade company dossier for job applications.

**LinkedIn tools:**


1. `get_company_profile` sections="posts,jobs,people,life"
2. `search_people` for leadership team
3. `get_person_profile` on CEO/CSO/VP BD with sections="experience,posts"

**Then invoke /company-research** for the same company. It adds:
SEC filings, clinical trials, FDA data, FAERS adverse events, publications,
Indeed sentiment, competitive landscape, and financial analysis.

**Output:** merged brief combining LinkedIn people/culture data with
regulatory, financial, and scientific intelligence.

---

## 2. Resume Tailoring (LinkedIn + /job-application-weapon)

1. `get_job_details` — extract exact JD keywords and requirements
2. `get_company_profile` — understand company values and language

**Then invoke /job-application-weapon** with the JD text. It generates
a targeted resume and cover letter using the extracted keywords.

---

## 3. Outreach Drafter (LinkedIn + Gmail)

1. `search_people` to find target (recruiter, HM, peer)
2. `get_person_profile` sections="experience,posts,interests,contact_info"
3. Draft personalized outreach referencing their recent posts or shared interests
4. `gmail_create_draft` to stage the email (if email found in contact_info)

**Gmail MCP tools:** gmail_search_messages, gmail_create_draft, gmail_read_message

---

## 4. Interview Prep Deep Dive (LinkedIn + /company-research + Google Calendar)

1. `get_person_profile` on each interviewer (experience, posts, publications)
2. `get_job_details` for full JD
3. Invoke /company-research for pipeline, financials, competitive landscape
4. Generate per-interviewer talking points and likely questions
5. `gcal_find_my_free_time` for scheduling follow-ups

**Google Calendar MCP tools:** gcal_list_events, gcal_find_my_free_time, gcal_create_event

---

## 5. Pipeline Due Diligence (LinkedIn + ToolUniverse)

Evaluate a company's scientific credibility before joining.


**LinkedIn tools:**

1. `get_company_profile` + `search_people` for R&D team
2. `get_person_profile` sections="publications" on key scientists

**ToolUniverse tools:**
3. `PubMed_search_articles` for their recent publications
4. `ClinicalTrials_search_studies` for active trials
5. `OpenTargets` for target validation
6. `clinvar_search_variants` if genetic medicine

**Output:** scientific credibility scorecard combining team expertise
with publication record and pipeline validation.

---

## 6. Competitive Landscape Map (LinkedIn + ToolUniverse + Chrome DevTools)

1. `search_jobs` across 5+ competitors for same role type
2. `get_company_profile` on each for size, growth, focus
3. `ClinicalTrials_search_studies` for each company's pipeline
4. Chrome DevTools: screenshot each company's careers page
5. Synthesize into competitive matrix (salary, pipeline, culture, growth)

**Chrome DevTools MCP tools:** navigate_page, take_screenshot

---

## 7. Network Warm Intro Finder (LinkedIn + Gmail)

1. `get_person_profile` on target — note mutual connections
2. `get_person_profile` on mutual connections — find strongest link
3. `gmail_search_messages` to check if you've emailed the mutual before
4. Draft warm intro request to the mutual connection
5. `gmail_create_draft` the message

---

## 8. Job Market Monitor (LinkedIn + /schedule)

Track the market over time with recurring checks.

1. `search_jobs` with target keywords, date_posted="past_24_hours"
2. `get_job_details` on new postings
3. Compare against previous results
4. Alert on: new roles at target companies, salary band changes, hiring surges

Automate via `/schedule` skill for recurring execution.
