# LinkedIn Intel Plays

8 composite workflows. Each play chains multiple linkedin-mcp tools
in sequence. Execute tool calls **one at a time** (never parallel).

---

## 1. Find the Hiring Manager

Identify who owns a role before applying.

1. `search_jobs` with target keywords + location
2. `get_job_details` on hits — note company, role level, reporting line
3. `search_people` with "VP/Director {function} {company}" + location
4. `get_person_profile` with sections="experience,posts" on likely HM

**Output:** table of roles with identified hiring managers, their tenure,
and recent posts signaling priorities.

---

## 2. Map an Org Chart

Reconstruct a team's hierarchy from LinkedIn data.

1. `search_people` with "{department} {company}"
2. `get_person_profile` on each with sections="experience" for reporting lines
3. Cross-reference titles and tenure to infer hierarchy
4. `get_company_profile` with sections="people" for the full employee directory

**Output:** inferred org chart with name, title, tenure, and reporting
relationships. Flag uncertainty where hierarchy is ambiguous.

---

## 3. Hidden Job Market

Find backfill openings from recent departures.

1. `search_people` with "just started {company}" or "new role {company}"
2. Their previous company now has a backfill opening
3. `get_company_profile` with sections="jobs" on previous company to confirm

**Output:** table of recent movers, their former roles, and confirmed
backfill openings at their previous employers.

---

## 4. Interview Prep

Build a comprehensive interview prep package.

1. `get_company_profile` with sections="posts,jobs,life" for full company context
2. `get_person_profile` on each interviewer with sections="experience,posts,interests,publications"
3. `get_job_details` for the target role
4. Cross-reference interviewer backgrounds with JD requirements

**Output:** per-interviewer brief (background, likely questions, shared
interests), company talking points, and JD alignment analysis.

---

## 5. Recruiter Finder

Locate recruiters active in a specific domain.

1. `search_people` with "biotech recruiter {therapeutic area}" + location
2. `get_person_profile` with sections="posts,contact_info" for outreach info
3. Check recent posts for active searches matching your profile

**Output:** ranked recruiter list with specialization, recent activity,
and contact info where available.

---

## 6. Consulting Lead Gen

Identify companies with capability gaps you can fill.

1. `get_company_profile` with sections="jobs,people" to find capability gaps
2. `search_people` with "{function} {company}" to map the team
3. `get_person_profile` on team lead with sections="experience,posts,skills"
4. Tailor pitch to gaps between their team and their open roles

**Output:** target company brief with identified gaps, team composition,
and recommended pitch angle for each lead.

---

## 7. Salary Benchmarking

Compare compensation across companies for a target role.

1. `search_jobs` with target title + location, max_pages=5
2. `get_job_details` on each — extract salary bands
3. Compare ranges across companies, levels, and locations

**Output:** salary comparison table with min/median/max by company,
location, and seniority level.

---

## 8. Competitive Intelligence

Track competitor hiring and strategic direction.

1. `get_company_profile` on competitors with sections="posts,jobs,people"
2. Track which departments are growing (from job details hiring trends)
3. `search_people` for recent departures — where are they going?

**Output:** competitive matrix with headcount trends, hiring focus areas,
recent departures, and strategic signals from job postings.
