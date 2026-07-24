---
name: resume-quality
description: Review, score, and improve resumes, CVs, LinkedIn profiles, cover letters, and role-targeted application materials. Use when the user asks for resume feedback, ATS optimization, recruiter review, bullet rewrites, career-story positioning, keyword alignment against a job description, or production-quality edits for job applications.
license: Complete terms in LICENSE.txt
---

# Resume Quality

Use this skill to give direct, evidence-based application-material feedback. Optimize for recruiter clarity, role fit, credibility, and interview conversion rather than generic resume advice.

## Core Workflow

1. Start with intake when the request does not already provide enough context:
   - Ask whether the user wants a job-specific review or a general resume review.
   - For a job-specific review, ask for the target job title, seniority, industry or company type, and the full job description or posting link/content.
   - For a general review, ask for the target role family, seniority, location or market if relevant, and whether the user wants recruiter feedback, ATS cleanup, bullet rewrites, or a score.
   - If the user only wants a quick edit of specific bullets, proceed with the available text and ask only for missing facts that would materially improve those bullets.
2. Identify the target:
   - Resume, CV, LinkedIn profile, cover letter, or specific bullets.
   - Role, seniority, industry, geography, and job description if provided.
   - Constraints such as one-page limit, academic CV norms, federal resume norms, or applicant tracking system requirements.
3. Build a dynamic content inventory before judging quality:
   - Detect sections by meaning, not only by heading names or order.
   - Map all content into candidate profile, target role, experience, projects, education, skills, certifications, awards, publications, volunteer work, and gaps or unclear items.
   - Note missing expected sections, duplicate sections, misplaced content, weak chronology, unclear dates, and unsupported claims.
   - If content is pasted out of order, reconstruct the likely resume structure mentally before reviewing it.
4. If a job description is provided, extract the hiring signal:
   - Must-have skills, preferred skills, domain keywords, seniority signals, business outcomes, and repeated phrases.
   - Separate actual requirements from generic company language.
5. Review the material in layers:
   - Strategy: fit for the target role and story coherence.
   - Structure: section order, scanability, length, and prioritization.
   - Evidence: quantified impact, scope, ownership, technical depth, and business context.
   - Language: action verbs, specificity, tense consistency, repetition, filler, and jargon.
   - ATS: parse-friendly formatting, exact keyword coverage, acronyms plus spelled-out terms, and avoidable formatting risks.
6. Return findings before rewrites:
   - Lead with the highest-impact issues.
   - Cite the exact section, bullet, or phrase when possible.
   - Explain why each issue hurts the application.
7. Rewrite only after diagnosing:
   - Preserve truthful scope and avoid inventing metrics, credentials, employers, dates, or tools.
   - Use placeholders like `[metric]`, `[scale]`, or `[tool]` when the resume needs facts the user has not supplied.
   - Keep the user's real seniority and domain; do not inflate claims.

## Document Skill Handoff

When the resume or application material is provided as a file, use the file-specific skill for extraction or editing, then apply this resume-quality workflow to the extracted content:

- For `.docx` files, use the `docx` skill to read, edit, preserve formatting, or produce a revised Word document.
- For `.pdf` files, use the `pdf` skill to extract text, inspect parsing issues, or identify scanned/OCR limitations.
- For pasted text, markdown, plain text, or copied profile content, use this skill directly.

After extraction, check whether the document structure survived conversion. Flag missing headings, merged bullets, broken dates, table artifacts, image-only content, or text that appears out of order because these can affect both review quality and ATS readiness.

If the user asks for a revised file, first complete the resume review and rewrites, then use the appropriate document skill to write the final version back into the requested format.

## Dynamic Resume Planner

Use this planner for every full resume review, regardless of the resume's ordering, formatting, or completeness:

1. Classify the resume type:
   - Entry-level, internship, experienced professional, leadership, technical, academic CV, federal, creative, career change, return-to-work, or mixed.
2. Infer the intended story:
   - Current role or student status, target next role, strongest proof points, likely differentiators, and visible risk factors.
3. Create a section map:
   - List what sections are present, what each section is trying to do, and whether the content belongs there.
   - Suggest a better order when the current order hides the strongest evidence.
4. Check completeness:
   - Contact block, headline or summary when useful, experience, projects when relevant, skills, education, certifications, links, dates, location, and authorization details only when appropriate.
5. Check role alignment:
   - Compare the most valuable resume real estate against the target role or general role family.
   - Flag strong content that is buried, weak content that is overemphasized, and content that should be removed.
6. Produce an action plan:
   - Separate fixes into `Do first`, `Improve next`, and `Optional polish`.

## Review Rubric

Score each category from 1 to 5 when the user asks for a score, audit, or rating:

- Target fit: the resume clearly maps to the desired role.
- Impact evidence: bullets show outcomes, scope, and measurable change.
- Credibility: claims are specific, plausible, and supported by context.
- Scanability: a recruiter can understand the candidate in 10 seconds.
- ATS readiness: keywords and formatting are likely to parse cleanly.
- Concision: every line earns its space.

Also provide an overall score out of 10 with the top three fixes that would raise it fastest.

## ATS Score

When the user asks for ATS scoring, job matching, or a full audit, provide an `ATS score` from 0 to 100. Make clear that this is a heuristic quality score, not a guarantee from any specific hiring system.

Calculate the score using these weighted areas:

- Parseability and formatting: 25 points for simple text structure, standard headings, readable dates, no tables/images/text boxes for critical content, and consistent bullets.
- Keyword alignment: 25 points for matching the target role or job description, including exact phrases, related terms, acronyms, and expanded terms.
- Required qualifications coverage: 20 points for visible evidence of required skills, years or level signals, credentials, tools, domains, and responsibilities.
- Section completeness: 15 points for having the right sections for the resume type and enough context to understand career progression.
- Evidence quality: 15 points for quantified achievements, scope, ownership, and outcomes tied to the target role.

For the ATS score, output:

- `ATS score: X/100`
- `Likely parsing risks`
- `Missing or weak keywords`
- `Required qualifications not clearly proven`
- `Fastest changes to improve the score`

If no job description is available, score against the stated target role family and label it `general ATS readiness`.

## Bullet Rewrite Standard

Prefer this shape:

`Action verb + specific work + scope/context + measurable result or business relevance`

Examples of acceptable result types:

- Revenue, cost, conversion, retention, latency, reliability, accuracy, risk, compliance, adoption, time saved, tickets reduced, users served, team size, project scale, or operational volume.
- If no metric is available, use concrete scope: systems owned, stakeholders served, release cadence, data volume, customer segment, or decision impact.

Avoid:

- Empty verbs: responsible for, worked on, helped with, participated in.
- Unsupported adjectives: highly scalable, best-in-class, innovative, successful.
- Dense tool lists with no outcome.
- Bullets that describe duties without impact.

## ATS And Formatting Checks

Recommend conservative formatting unless the user explicitly needs a designed resume:

- Single-column layout for ATS-heavy applications.
- Standard section headings: Summary, Experience, Projects, Education, Skills, Certifications.
- Text-based bullets rather than tables, icons, images, text boxes, or charts.
- File names that include the candidate name and target role.
- Both acronym and expanded form for important terms when space permits, for example `CI/CD (continuous integration and delivery)`.

Do not overpromise ATS behavior. Say "likely ATS-friendly" rather than claiming a guaranteed pass.

## Output Formats

For a full review, use:

1. Overall assessment: 2-4 sentences.
2. Dynamic planner: inferred resume type, section map, and ordering recommendations.
3. Scorecard: category scores, overall score, and ATS score when applicable.
4. Highest-impact fixes: prioritized list with rationale.
5. Section notes: targeted findings by section.
6. Rewrites: improved bullets or summary text, using placeholders for missing facts.
7. Next questions: only ask for facts that would materially improve the resume.

For quick edits, skip the full scorecard and provide:

- Before/after rewrite.
- Why the rewrite is stronger.
- Missing facts that would make it stronger.

For job-description matching, provide:

- Match summary.
- Missing or weak keywords.
- Experience that should be emphasized.
- Suggested resume edits mapped to the job description.

## Integrity Rules

- Do not fabricate accomplishments, dates, degrees, certifications, employers, tools, metrics, awards, publications, or security clearances.
- Do not encourage keyword stuffing or deceptive optimization.
- Flag potential legal or ethical risks such as misrepresented employment dates or unverifiable credentials.
- Respect domain norms: academic CVs value publications and teaching; federal resumes require detail and exact eligibility language; creative portfolios can support more visual design; technical resumes need stack depth and shipped outcomes.
- If the resume contains sensitive personal data, avoid repeating unnecessary personal details in the response.
