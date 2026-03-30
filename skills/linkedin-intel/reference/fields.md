# LinkedIn Intel Field Inventory

Every extractable field per entity type. Use this to determine which
sections to request for a given research task.

---

## Person Dossier (16 sections)

| Category | Fields | Section |
|---|---|---|
| Identity | Full name, headline, location, profile photo URL, connection degree | main_profile |
| Summary | About/bio text, featured content links | main_profile |
| Network | Connection count, follower count, mutual connections | main_profile |
| Work history | Title, company, dates, duration, description per role | experience |
| Career gaps | Inferred from date gaps between roles | experience |
| Promotions | Same company, title changes over time | experience |
| Industry moves | Company/sector changes across career | experience |
| Education | School, degree, field, dates, activities, GPA if listed | education |
| Skills | Each skill, endorsement count, who endorsed | skills |
| Credibility | Recommendation text, recommender name/title, relationship | recommendations |
| Credentials | Certification name, issuer, date, credential ID | certifications |
| Track record | Project descriptions, collaborators, URLs | projects |
| Research | Publications, journals, co-authors | publications |
| Training | Courses completed | courses |
| Affiliations | Professional organizations, memberships | organizations |
| Character | Volunteer work, causes supported | volunteer |
| Interests | Companies followed, groups joined, influencers followed | interests |
| Awards | Honors, patents, test scores | honors |
| Languages | Languages spoken, proficiency level | languages |
| Contact | Email, phone, websites, birthday, connected date | contact_info |
| Voice | Recent posts, articles, reshares, engagement | posts |

**Full dossier call:**

```
get_person_profile("{username}", sections="experience,education,skills,recommendations,certifications,projects,publications,courses,organizations,volunteer,interests,honors,languages,contact_info,posts")
```

---

## Company Dossier (5 sections)

| Category | Fields | Section |
|---|---|---|
| Overview | Name, industry, size, HQ, founded, website, specialties | about |
| Description | Company mission/about text | about |
| Voice | Recent posts, announcements, content themes | posts |
| Openings | All current job listings | jobs |
| Team | Employee directory with titles and connections | people |
| Culture | Company life page, photos, employee perspectives | life |
| Hiring trends | Headcount growth by dept, median tenure (via job details) | jobs (embedded) |
| Competitors | Competitive landscape analysis (via job details) | jobs (embedded) |
| Financials | Revenue signals, funding (via job detail insights) | jobs (embedded) |

**Full dossier call:**

```
get_company_profile("{slug}", sections="posts,jobs,people,life")
```

---

## Job Intel (from get_job_details)

| Category | Fields |
|---|---|
| Role | Title, company, location, work type, employment type |
| Compensation | Salary band (min-max), bonus, equity, benefits list |
| Requirements | Years experience, degree, hard skills, soft skills |
| Description | Full JD text with responsibilities and qualifications |
| Applicants | Total count, past-day count, seniority breakdown, education breakdown |
| Company intel | Headcount by dept, 2-year growth rate, median tenure |
| Competitors | Named competitors with strategic positioning analysis |
| Hiring velocity | Department-level headcount growth trends |
| Apply link | Direct external application URL |

---

## Section Selection Guide

Choose the minimum sections needed for the task:

| Task | Person sections | Company sections |
|---|---|---|
| Quick lookup | (main_profile only — default) | (about only — default) |
| Career analysis | experience, education | — |
| Skill assessment | skills, certifications, projects | — |
| Academic profile | publications, education, honors | — |
| Outreach prep | posts, interests, contact_info | — |
| Full dossier | all 16 | all 5 |
| Hiring analysis | — | jobs, people |
| Culture check | — | life, posts |
| Team mapping | — | people |
