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
3. If a job description is provided, extract the hiring signal:
   - Must-have skills, preferred skills, domain keywords, seniority signals, business outcomes, and repeated phrases.
   - Separate actual requirements from generic company language.
4. Review the material in layers:
   - Strategy: fit for the target role and story coherence.
   - Structure: section order, scanability, length, and prioritization.
   - Evidence: quantified impact, scope, ownership, technical depth, and business context.
   - Language: action verbs, specificity, tense consistency, repetition, filler, and jargon.
   - ATS: parse-friendly formatting, exact keyword coverage, acronyms plus spelled-out terms, and avoidable formatting risks.
5. Return findings before rewrites:
   - Lead with the highest-impact issues.
   - Cite the exact section, bullet, or phrase when possible.
   - Explain why each issue hurts the application.
6. Rewrite only after diagnosing:
   - Preserve truthful scope and avoid inventing metrics, credentials, employers, dates, or tools.
   - Use placeholders like `[metric]`, `[scale]`, or `[tool]` when the resume needs facts the user has not supplied.
   - Keep the user's real seniority and domain; do not inflate claims.

## Review Rubric

Score each category from 1 to 5 when the user asks for a score, audit, or rating:

- Target fit: the resume clearly maps to the desired role.
- Impact evidence: bullets show outcomes, scope, and measurable change.
- Credibility: claims are specific, plausible, and supported by context.
- Scanability: a recruiter can understand the candidate in 10 seconds.
- ATS readiness: keywords and formatting are likely to parse cleanly.
- Concision: every line earns its space.

Also provide an overall score out of 10 with the top three fixes that would raise it fastest.

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
2. Scorecard: category scores and overall score.
3. Highest-impact fixes: prioritized list with rationale.
4. Section notes: targeted findings by section.
5. Rewrites: improved bullets or summary text, using placeholders for missing facts.
6. Next questions: only ask for facts that would materially improve the resume.

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
