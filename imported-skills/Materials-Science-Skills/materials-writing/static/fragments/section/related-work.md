# Section: Related Work (writing)

> **Domain context**: The `domain` axis has loaded domain-specific writing guidance for [detected domain]. The grouping expectations below apply generally; the domain guide contains field-specific characterization and mechanism standards to cite against.

## Default structure

`topic scope -> representative methods grouped by mechanism -> limitation tied to this paper -> distinction`

## Drafting rules

- **Group by technical topic and mechanism, not by publication year or author.** A paragraph titled "Fiber reinforcement in cementitious systems" with three contrasting approaches is stronger than three single-paper paragraphs.
- Each subsection ends with a limitation that **this paper addresses**. If a subsection's limitation does not connect back to your contribution, the subsection probably does not belong.
- Avoid both extremes: do not bash prior work, do not flatter it. State what prior work showed and where its scope ended.
- Cite the source you actually read. Do not chain-cite review papers as if they were primary sources.
- For materials work, group by material system or mechanism (e.g., `polymer-modified asphalt`, `SCM-blended cement`, `fiber-reinforced composite`), not by author chronology.

## Materials-specific grouping examples

- By material system: `cementitious composites`, `modified asphalt`, `polymer nanocomposites`, `ceramic toughening`.
- By mechanism: `interfacial bonding`, `pore refinement`, `crack bridging`, `phase transformation`.
- By performance demand: `durability under freeze-thaw`, `high-temperature stability`, `fatigue life`.

## When Related Work is a separate section vs folded into Introduction

- **Separate Related Work** is common when the field has many competing approaches and the contribution depends on distinguishing among them.
- **Folded into Introduction** is common in materials journals that prefer a short gap statement over a dedicated survey (CBM, JBE often fold; CCC sometimes separates).
- The target venue decides. Ask the user if unclear, and check the `journal_family` fragment for venue conventions.

## Citing characterization and standards

When summarizing prior work, note the characterization technique and test standard the authors used, not just the result. This makes the limitation concrete: "Prior work reported X using SEM and FTIR but did not quantify Y under service-condition aging."

## When to open the deep reference

For section-pattern synthesis and concrete paragraph skeletons, open `references/section-patterns/review-synthesis-patterns.md` (review papers) or `references/argument-chain.md` (full manuscript logic).

## Common failure modes

- Listing papers chronologically instead of grouping by mechanism.
- Subsections whose limitation does not connect to this paper's contribution.
- Chain-citing reviews as if they were primary sources.
- Bashing or flattering prior work instead of stating its scope.

## Checklist

- [ ] Is each subsection grouped by mechanism or material system, not by author/year?
- [ ] Does each subsection end with a limitation this paper addresses?
- [ ] Are primary sources cited where primary claims are made?
- [ ] Is the venue convention (separate vs folded) confirmed?
