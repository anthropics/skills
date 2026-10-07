---
name: recommended-reading-list
description: "Generate a curated supplementary reading list from any course syllabus using Consensus academic search. Use this skill whenever a user uploads a syllabus, course outline, or curriculum document and wants to find recent research papers, build a reading list, or discover literature related to course topics. Also trigger when the user says 'find papers for my course', 'create a reading list from this syllabus', 'recent research for my class', 'supplementary readings', 'find journal articles for these topics', or 'what recent papers cover this material'. Even casual mentions like 'any new research on these course topics?' or 'update my syllabus with recent papers' should trigger this skill. This skill parses the syllabus to extract topics and learning outcomes, searches Consensus for recent peer-reviewed papers, and produces a professionally formatted .docx reading list with clickable Consensus links, one-sentence summaries, and discussion questions tied to course learning goals."
---

# Recommended Reading List Generator

## Overview

This skill takes a course syllabus (PDF, DOCX, or text) and produces a professional Word document containing a curated reading list of recent peer-reviewed research. It uses the Consensus MCP tool — powered by a database of 200+ million academic papers — to find papers that map to each course topic. The output includes clickable links to each paper on Consensus, a one-sentence plain-language summary, and a thought-provoking discussion question that ties the paper back to the course's learning goals.

The instructor or student walks away with a ready-to-distribute .docx that supplements their textbook with the latest research.

## Data Integrity Principles

This skill calls an external search tool (Consensus) and builds a document from the results. The user is trusting that every paper in the final reading list actually came from Consensus in this session — not from your training data, not from a prior conversation, not hallucinated. This matters because fabricated citations in academic contexts can damage an instructor's credibility and mislead students.

To earn that trust, follow these principles throughout:

**Only use what Consensus returns.** Every paper title, author list, journal name, year, and URL in the final document must come from a Consensus search result received during this session. If you know of a great paper from your training data but Consensus didn't return it, do not include it. If you want to mention it conversationally, label it clearly: `[Not from Consensus — model knowledge]`.

**Confirm before moving on.** A search is not complete until you've seen the results come back. Don't mark a section as "done" based on having sent the query — wait for the response, inspect the papers returned, and then proceed to the next query.

**Track your numbers.** Throughout the search phase, maintain a running tally of three separate counts:
- **Queries sent**: how many Consensus searches you executed
- **Papers received**: how many total papers Consensus returned across all searches
- **Papers cited**: how many papers you selected for the final document

These numbers will appear in the audit log (see Phase 4). They help the user understand coverage — for instance, if the free tier returned 3 papers per query and you ran 12 queries, the user knows you worked with a pool of ~36 candidates.

**Surface gaps, don't fill them silently.** If a search returns zero results, or fewer results than expected, tell the user. Don't quietly substitute model knowledge. A section with one paper and a note saying "Consensus returned limited results for this topic — consider broadening the search or checking manually" is far more honest than padding with fabricated entries.

## Workflow

### Phase 1: Parse the Syllabus

Read the uploaded syllabus file and extract two things:

1. **Course topics** — the ordered list of subjects/units covered (e.g., "Protein Structure", "Enzyme Kinetics", "Lipid Metabolism"). These become the sections of the reading list.
2. **Learning outcomes** — the course-level goals (e.g., "Describe the central pathways that provide living organisms with energy"). These inform the discussion questions you'll write for each paper.

If the syllabus doesn't have explicit learning outcomes, infer 3-5 from the course description and topic list.

Group closely related topics together into sections (e.g., "Protein Structure" and "Protein Function" can become one section). Aim for 6-12 sections — enough granularity to be useful, but not so many that the document feels fragmented. Present this grouping to the user and confirm before searching.

### Phase 2: Search Consensus for Each Section

For each section, craft 1-2 targeted search queries and run them using the Consensus MCP search tool. The goal is to find papers that are recent (set `year_min` to the current year minus 1), relevant to the topic, and ideally connected to real-world applications (food science, nutrition, health, disease — whatever the course emphasizes).

**Query design tips:**
- Include the core topic plus an applied angle. For example, for a biochemistry course with a nutrition focus, don't just search "enzyme kinetics" — search "enzyme kinetics food processing applications" or "enzyme kinetics nutrition digestion".
- If the course has an obvious applied domain (food science, medicine, environmental science, etc.), weave that into every query. This surfaces papers that bridge theory and application, which makes for much better supplementary reading.
- Keep queries to 4-8 words. Overly long queries dilute relevance.

**Example queries for a Biochemistry & Nutrition course:**

| Section | Query |
|---------|-------|
| Nucleic Acids | `nucleic acid structure function food safety` |
| Amino Acids | `amino acid nutrition metabolism health` |
| Protein Structure & Function | `protein structure function food science` |
| Enzyme Function & Kinetics | `enzyme kinetics food processing applications` |
| Lipids & Membranes | `lipids biological membranes lipoproteins nutrition` |
| Carbohydrate Metabolism | `carbohydrate metabolism glycolysis nutrition` |
| Citric Acid Cycle & Oxidative Phosphorylation | `citric acid cycle oxidative phosphorylation energy` |
| Lipid Metabolism | `lipid metabolism fatty acid oxidation dietary` |
| Energy Metabolism in Disease | `energy metabolism diabetes insulin resistance` |
| Nitrogen Metabolism | `nitrogen metabolism urea cycle amino acid catabolism` |

**Rate limiting and sequential execution:** The Consensus search tool has a rate limit of one query per second. Run searches one at a time — send a query, wait for the response, process the results, then run `sleep 1` before sending the next query. Do not batch multiple Consensus searches into a single message or run them in parallel; they will be rate-limited and fail. This sequential approach also naturally ensures you confirm each result before moving on.

**Handling search failures:** If a Consensus search fails (timeout, error, empty response when results were expected):
1. Wait 3 seconds, then retry the same query once.
2. If the retry also fails, log the failure (section name, query, error) and move on to the next section.
3. If you hit 3 consecutive failures across any queries, stop searching and alert the user — Consensus may be experiencing issues. Share what you've collected so far and ask how they'd like to proceed.
4. Never silently skip a failed search. Every failure must be noted in the audit log.

**After each search, record what you got.** For each query, note: the query string, how many papers were returned, and which papers (if any) you're selecting. This is the raw material for the audit log.

**Tool constraints to be aware of:** The Consensus free tier returns up to 3 papers per search. With ~10 sections and 1-2 queries each, expect 30-60 candidate papers total. This is a hard ceiling imposed by the tool — not a limitation of your searching. Report this to the user so they understand the scope of coverage. If they have a Consensus Pro account, more results per search are available.

**Paper selection criteria** (in priority order):
1. Relevance to the course topic
2. Review papers and meta-analyses over narrow primary research (reviews give students a broader entry point)
3. Higher citation counts (signals quality and influence)
4. Clear connection to the course's applied domain

Select 1-3 papers per section from what Consensus returned, aiming for 15-25 papers total in the final document.

### Phase 3: Write Summaries and Discussion Questions

For each selected paper, write two things. Base your summaries only on information present in the Consensus search results (title, abstract, metadata). If the search result doesn't provide enough context for a meaningful summary, say so briefly rather than inventing details.

**One-sentence summary:** A plain-language sentence that captures what the paper found or reviewed, written for an undergraduate audience. Avoid jargon where possible; if a technical term is necessary, define it in parentheses. The summary should make a student think "I want to read this."

Good: "This review maps how different diets — Mediterranean, Nordic, and vegetarian — reshape the types of fat molecules circulating in your blood, with implications for heart disease risk."

Bad: "This paper reviews lipidomic profiles across dietary interventions and their cardiometabolic implications." (Too jargon-heavy for undergrads.)

**Discussion question:** A thought-provoking question that connects the paper's findings back to one of the course's learning outcomes. The question should push students beyond recall — ask them to apply, analyze, or evaluate. Frame it as something an instructor might pose in class or on an assignment.

Good: "If dietary fat quality can reshape your lipoprotein lipidome, what does this suggest about the biochemical basis for dietary guidelines recommending unsaturated over saturated fats?"

Bad: "What did the authors find?" (Too simple — just recall.)

### Phase 4: Generate the .docx Document

Use the bundled script at `scripts/generate_reading_list.js` to produce the Word document. The script expects a JSON file as input with this structure:

```json
{
  "courseTitle": "Biochemistry 2288A",
  "courseSubtitle": "Biochemistry and Molecular Biology for Foods and Nutrition",
  "generatedDate": "March 17, 2026",
  "yearRange": "2025-2026",
  "introText": "This reading list was curated using Consensus...",
  "learningOutcomes": [
    "Demonstrate basic knowledge about the structure, roles, and functions of the different classes of biomolecules.",
    "..."
  ],
  "sections": [
    {
      "heading": "Topics 1-2: Foundations & Nucleic Acids",
      "papers": [
        {
          "title": "Paper Title Here",
          "authors": "Author A., Author B., Author C.",
          "journal": "Journal Name",
          "year": 2025,
          "url": "https://consensus.app/papers/details/...",
          "summary": "One-sentence plain-language summary.",
          "question": "Discussion question tied to a learning outcome."
        }
      ]
    }
  ],
  "auditLog": {
    "totalQueriesSent": 12,
    "totalPapersReceived": 34,
    "totalPapersCited": 18,
    "toolConstraints": "Consensus free tier: max 3 papers per query",
    "searchDetails": [
      {
        "section": "Nucleic Acids",
        "query": "nucleic acid structure function food safety",
        "papersReturned": 3,
        "papersSelected": 2,
        "status": "success"
      }
    ],
    "failures": []
  }
}
```

Note the `auditLog` field — this captures the full search trail so the user (and anyone reviewing the document later) can verify exactly what was searched, what came back, and what was included. The document generation script doesn't render the audit log into the .docx itself, but the data is preserved in the JSON. You'll also surface a summary in your chat response (see Phase 5).

**To generate the document:**

1. First, ensure the `docx` npm package is installed: `npm install docx` (run in the skill's directory or any directory with a package.json).

2. Write the JSON data to a temp file (e.g., `/tmp/reading_list_data.json`).

3. Run the script:
```bash
node <skill-path>/scripts/generate_reading_list.js /tmp/reading_list_data.json "<output-path>/Reading_List.docx"
```

4. Validate the output:
```bash
python <docx-skill-path>/scripts/office/validate.py "<output-path>/Reading_List.docx"
```

The script produces a clean, professional document with:
- A title page section with course name, subtitle, and date
- An introduction explaining how the list was curated (with a clickable link to consensus.app)
- A "Course Learning Outcomes" box for reference
- Numbered papers organized under section headings, each with:
  - Clickable paper title linking to Consensus
  - Author, journal, and year in italic gray
  - A "Summary" line in plain language
  - A "Discussion Question" line in blue
- A footer with generation metadata

### Phase 5: Deliver to User

Save the .docx to the user's workspace folder and provide a `computer://` link.

Along with the link, include a brief **audit summary** in your chat message. Apply the same sourcing and attribution standards here as in the document — your chat message is part of the deliverable. Format it something like:

> **Search summary:** Ran 12 Consensus queries across 10 topic sections. Consensus returned 34 papers total (free tier cap: 3 per query). Selected 18 for the final reading list. No search failures.
>
> **Sections with limited results:** "Nitrogen Metabolism" returned only 1 relevant paper. You may want to supplement this section manually.
>
> **Failures:** None (or list any that occurred with the query and error).

If any searches failed, any sections had zero results, or any model knowledge was used for any reason, surface those facts here. The goal is full transparency — the user should never have to wonder "did this actually come from Consensus?"

## Important Notes

- **Year range:** Default to papers from the last 1-2 years. If the user asks for a wider range, adjust `year_min` in the Consensus searches accordingly.
- **Consensus free tier:** Returns 3 papers per search. With ~10 topic sections, expect ~30 candidates. If the user has a Consensus Pro account, you can get more results per search.
- **Non-English syllabi:** The skill works with any language — extract topics and search in English (Consensus indexes English-language papers), but note in the document if the course is taught in another language.
- **Multiple file types:** The syllabus might be a PDF, DOCX, image, or even pasted text. Use the appropriate tool to extract content (Read for PDF/text, pandoc for DOCX, vision for images).
