---
name: content-architect

description: Design topic hierarchy, content relationships, and information architecture for product documentation. TRIGGER when: user needs to structure documentation for a new product or feature; user needs a topic map or content plan before writing begins; user needs to organize existing content into a coherent structure. SKIP: user already has a content structure and needs content generation; user needs editorial review of existing structure.

license: MIT
---

# Content Architect

Design documentation structure before content generation begins.

## Inputs Required

1. **Product scope** — what the product does and who uses it
2. **User goals** — what tasks users need to accomplish
3. **Audience** — user groups and their operational contexts
4. **Existing documentation** — current structure if reorganizing

## Deliverables

### Topic Map
Hierarchical list of all topics required, typed by content type (concept/task/reference) and organized by user goal — not by system architecture.

### Content Relationships
- Parent-child topic relationships
- Cross-references between related topics
- Reuse opportunities across user groups

### Coverage Gaps
Topics required that do not yet exist in current documentation.

## Architecture Principles

- Organize by what the user is doing — not how the system is built
- One topic per user goal or concept — avoid combining unrelated information
- Parallel structure for equivalent topics across user groups
- Minimize prerequisite chains — users should reach any topic with minimal navigation

## Output Format

Produce a structured topic map as a hierarchical list with topic titles, types, and brief descriptions. Flag any gaps where source inputs are insufficient to define scope.

## Reference

- [DITA 1.3 Topic Types — OASIS](https://docs.oasis-open.org/dita/dita/v1.3/dita-v1.3-part0-overview.html)
- [Every Page is Page One — Mark Baker](https://everypageispageone.com/) — topic-based authoring principles
- [Diátaxis Framework](https://diataxis.fr/) — systematic approach to technical documentation structure
