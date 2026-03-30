# LinkedIn MCP Tools Reference

7 tools exposed by the linkedin-mcp server. All read-only.

## Table of Contents

1. [get_person_profile](#1-get_person_profile)
2. [search_people](#2-search_people)
3. [get_company_profile](#3-get_company_profile)
4. [get_company_posts](#4-get_company_posts)
5. [search_jobs](#5-search_jobs)
6. [get_job_details](#6-get_job_details)
7. [close_session](#7-close_session)

---

## 1. get_person_profile

Scrape a LinkedIn user's profile by username.

| Param | Type | Required | Notes |
|---|---|---|---|
| linkedin_username | string | yes | URL slug: "williamhgates", "stickerdaniel" |
| sections | string | no | Comma-separated. Default: main_profile only |

**16 available sections:**

| Section | Returns |
|---|---|
| main_profile | Always included. Headline, about, top card, connections |
| experience | Full work history with dates, descriptions |
| education | Schools, degrees, dates, activities |
| skills | Skill endorsements + who endorsed |
| recommendations | Given and received recommendations |
| certifications | Certs with issuers, dates, credential ID |
| projects | Project descriptions and collaborators |
| publications | Academic publications, journals, co-authors |
| courses | Courses listed on profile |
| organizations | Professional orgs and memberships |
| volunteer | Volunteer experience and causes |
| interests | Companies, groups, influencers followed |
| honors | Awards, test scores, patents |
| languages | Languages spoken and proficiency level |
| contact_info | Email, phone, website, birthday (overlay) |
| posts | Recent activity, articles, reshares |

**Full dossier call:**

```
get_person_profile("username", sections="experience,education,skills,recommendations,certifications,projects,publications,courses,organizations,volunteer,interests,honors,languages,contact_info,posts")
```

**Return shape:** `{url, sections: {section_name: text}, references, job_ids}`

---

## 2. search_people

Search LinkedIn's people directory.

| Param | Type | Required | Notes |
|---|---|---|---|
| keywords | string | yes | Free text: name, title, company, skills |
| location | string | no | e.g. "Boston", "San Francisco" |

Returns: list of people with name, headline, location, current role, mutual connections.

---

## 3. get_company_profile

Scrape a company's LinkedIn page.

| Param | Type | Required | Notes |
|---|---|---|---|
| company_name | string | yes | URL slug: "anthropic", "eli-lilly-and-company" |
| sections | string | no | Comma-separated. Default: about only |

**5 available sections:**

| Section | Returns |
|---|---|
| about | Always included. Description, industry, size, HQ, specialties |
| posts | Recent company posts and updates |
| jobs | Current open positions |
| people | Employee directory with titles and connections |
| life | Culture page, photos, employee perspectives |

**Full dossier call:**

```
get_company_profile("slug", sections="posts,jobs,people,life")
```

---

## 4. get_company_posts

Dedicated tool for company feed. Use when you only need posts.

| Param | Type | Required | Notes |
|---|---|---|---|
| company_name | string | yes | URL slug |

---

## 5. search_jobs

Search LinkedIn's job board with filters.

| Param | Type | Required | Notes |
|---|---|---|---|
| keywords | string | yes | e.g. "business development biotech" |
| location | string | no | e.g. "Boston", "Remote" |
| max_pages | number | no | 1-10, default 3 (25 results/page) |
| date_posted | string | no | past_hour, past_24_hours, past_week, past_month |
| job_type | string | no | full_time, part_time, contract, temporary, volunteer, internship, other |
| experience_level | string | no | internship, entry, associate, mid_senior, director, executive |
| work_type | string | no | on_site, remote, hybrid |
| easy_apply | boolean | no | Only Easy Apply jobs |
| sort_by | string | no | date or relevance |

Returns: search results text + `job_ids` array for use with get_job_details.

---

## 6. get_job_details

Full job posting details by ID (from search_jobs results).

| Param | Type | Required | Notes |
|---|---|---|---|
| job_id | string | yes | Numeric ID from search_jobs |

Returns: full JD, requirements, salary band, benefits, applicant insights
(seniority breakdown, education breakdown, total applicants), competitor
intel, hiring trends, headcount growth by department.

---

## 7. close_session

Close browser and free resources. No parameters. Call when done with a
LinkedIn research session to release the headless Chromium instance.

---

## Constraints

- **Read-only**: cannot post, message, connect, like, or comment
- **Rate limiting**: mixture-model timing (1.2-12s), sequential execution only
- **Auth**: persistent Chromium profile at `~/.linkedin-mcp/profile/`
- **Max results**: 25/page, up to 10 pages (250 jobs per search)
- **Anti-detection**: stealth JS, Bezier mouse, time-of-day pacing
