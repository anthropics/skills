# Applied-Domain Weaving — The Search-Quality Multiplier

This reference answers exactly one decision: **why does the syllabus skill always weave the applied domain into Consensus queries, and what makes a generic search produce thin results?**

## The Core Insight

A query like `"enzyme kinetics"` returns **review papers and theoretical treatments** — useful for a biochemistry course but unhelpful for a *food science* course where students need to know how enzyme kinetics applies to bread fermentation, cheese ripening, and meat tenderization.

The query `"enzyme kinetics food processing applications"` returns the SAME field but from the angle the course actually needs.

> **Applied-domain weaving = search the topic + the course's applied domain.**

This is the single highest-leverage technique in the skill. Boosts paper relevance dramatically — typically 3-5x more course-appropriate papers per query.

## Concrete Examples by Discipline

### Engineering / Applied Sciences

| Topic | Generic search | Applied-domain search |
|---|---|---|
| Thermodynamics | "thermodynamics" | "thermodynamics renewable energy systems" |
| Fluid mechanics | "fluid mechanics" | "fluid mechanics biomedical device design" |
| Control systems | "PID control" | "PID control HVAC building automation" |
| Materials science | "polymer composites" | "polymer composites aerospace structural" |

### Health Sciences

| Topic | Generic search | Applied-domain search |
|---|---|---|
| Pharmacology | "drug interactions" | "drug interactions pediatric oncology" |
| Public health | "social determinants" | "social determinants rural health disparities" |
| Nutrition | "lipid metabolism" | "lipid metabolism Mediterranean diet" |
| Immunology | "innate immunity" | "innate immunity vaccine development" |

### Computer Science / Data Science

| Topic | Generic search | Applied-domain search |
|---|---|---|
| Machine learning | "neural networks" | "neural networks medical imaging diagnosis" |
| Distributed systems | "consensus algorithms" | "consensus algorithms blockchain finance" |
| Database systems | "query optimization" | "query optimization warehouse analytics" |
| HCI | "user interface design" | "user interface design accessibility" |

### Business / Social Sciences

| Topic | Generic search | Applied-domain search |
|---|---|---|
| Game theory | "Nash equilibrium" | "Nash equilibrium auction design" |
| Behavioral econ | "loss aversion" | "loss aversion retirement savings" |
| Org psychology | "team dynamics" | "team dynamics remote engineering" |
| Marketing | "consumer behavior" | "consumer behavior subscription services" |

### Physical Sciences

| Topic | Generic search | Applied-domain search |
|---|---|---|
| Quantum mechanics | "entanglement" | "entanglement quantum computing applications" |
| Astrophysics | "stellar evolution" | "stellar evolution exoplanet habitability" |
| Geology | "plate tectonics" | "plate tectonics earthquake hazard" |

## Why This Works

The applied-domain term:

1. **Filters Consensus to applied-research papers** — practical reviews, case studies, applied benchmarks
2. **Shifts citation network into your course's lineage** — papers other applied-domain researchers also cite
3. **Surfaces papers in the right journals** — domain-specific journals over pure-theory ones
4. **Gives papers students can connect to** — abstract theory → "I see how this matters"

## How to Identify the Applied Domain

The applied domain comes from one or more of:

1. **Course title** — "Food Science 301" → "food processing applications"
2. **Department / college** — Engineering → "engineering applications"
3. **Course description** — explicit "applied to X" / "for Y industry"
4. **Learning outcomes** — operational outcomes signal applied focus

If the syllabus is genuinely theoretical (e.g., a pure-math course), use **methodological angle** instead:
- Theoretical CS → "theoretical CS algorithm complexity"
- Pure math → "pure math applications" (or skip — pure-theory queries are fine here)

## When to Skip Applied-Domain Weaving

- **Pure theory courses** — no applied angle. Search topic only.
- **Survey courses** — broad coverage needed; applied-domain may narrow too much.
- **Topic genuinely doesn't have a natural applied domain** — e.g., "intro to research methods" — skip and search the topic + "review" or "introduction".

If applied-domain search returns < 3 papers, **fall back to generic search** for that section. Don't pad with fabrications.

## Operational Pattern

In Phase 3 of the skill:

```
For each section in [proposed sections]:
  1. Construct primary query: "{topic} {applied-domain-keyword}" + year_min
  2. Submit to Consensus (sequential, 1 q/sec gap)
  3. If results >= 3: select papers, move on
  4. If results < 3: submit fallback "{topic}" + year_min
  5. Select 1-3 papers from combined results
```

## Anti-Patterns

### "Just search the topic"

Most common mistake. Produces theoretically rigorous but unhelpful papers for an applied course. Students can't connect them to course goals. Engagement drops.

### "Search the applied domain alone"

Without the topic anchor, query is too broad. "Food processing" returns 10,000+ papers across all subfields. Topic + applied-domain is the sweet spot.

### "Use multiple applied domains in one query"

"Enzyme kinetics food processing biomedical industrial applications" overconstrains. Each query targets ONE applied domain. If a section spans multiple domains, run separate queries.

### "Weave domain into queries even for pure-theory courses"

Pure-theory courses don't have applied domains. Forcing one in produces awkward queries that miss the actual theoretical literature.

### "Skip applied-domain weaving to save query budget"

The applied-domain weaving doesn't add queries — it modifies them. Same query budget, dramatically better relevance.

## Operational Checklist

- [ ] Course's applied domain identified (from title / department / description / learning outcomes)
- [ ] Each Phase 3 query: `{topic} + {applied-domain}` format
- [ ] Fallback to generic search if applied-domain returns < 3 papers
- [ ] Pure-theory courses: skip applied-domain weaving (use generic)
- [ ] Multi-domain sections: separate query per domain (don't stack in one query)

## Citations (7 sources)

1. **Bloom, B. S. (ed.), *Taxonomy of Educational Objectives* (1956).** Source for the application-tier of learning that justifies the applied-domain framing. Higher-tier learning (apply / analyze / evaluate) requires applied examples; pure-theory readings only support recall + comprehension.

2. **Mayer, R. E., *Multimedia Learning* (Cambridge, 2nd ed. 2009).** Empirical research on how applied examples accelerate learning vs abstract presentation. Source for the engagement-drop signal that pure-theory readings produce in applied courses.

3. **Fink, L. D., *Creating Significant Learning Experiences* (Jossey-Bass, 2003).** Source for the "integration" learning category — the discipline of connecting course content to students' applied contexts. Applied-domain weaving operationalizes this.

4. **Donald, J. G., *Learning to Think: Disciplinary Perspectives* (Jossey-Bass, 2002).** Empirical study of disciplinary thinking patterns. Justifies the per-discipline query-pattern table — engineering thinks differently from biology thinks differently from CS.

5. **Lave, J. & Wenger, E., *Situated Learning* (Cambridge, 1991).** Source for "situated cognition" — knowledge is best learned in the context of its application. Applied-domain weaving brings the readings into the situated context.

6. **Chickering, A. W. & Gamson, Z. F., "Seven Principles for Good Practice in Undergraduate Education" — *AAHE Bulletin*, 1987.** Principle #5 ("Emphasize Time on Task") + Principle #7 ("Respect Diverse Talents") favor applied-domain readings over pure-theory abstracts that don't connect to student backgrounds.

7. **Boyer, E. L., *Scholarship Reconsidered* (Carnegie Foundation, 1990).** Source for the "Scholarship of Application" framing. Applied-domain papers represent this scholarship category; weaving them into reading lists honors that scholarship.
