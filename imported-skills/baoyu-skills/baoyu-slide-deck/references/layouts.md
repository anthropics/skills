# Layout Gallery

Optional layout hints for individual slides. Specify in outline's `// LAYOUT` section.

## Slide-Specific Layouts

| Layout | Description | Best For |
|--------|-------------|----------|
| `title-hero` | Large centered title + subtitle | Cover slides, section breaks |
| `quote-callout` | Featured quote with attribution | Testimonials, key insights |
| `key-stat` | Single large number as focal point | Impact statistics, metrics |
| `split-screen` | Half image, half text | Feature highlights, comparisons |
| `icon-grid` | Grid of icons with labels | Features, capabilities, benefits |
| `two-columns` | Content in balanced columns | Paired information, dual points |
| `three-columns` | Content in three columns | Triple comparisons, categories |
| `image-caption` | Full-bleed image + text overlay | Visual storytelling, emotional |
| `agenda` | Numbered list with highlights | Session overview, roadmap |
| `bullet-list` | Structured bullet points | Simple content, lists |

## Infographic-Derived Layouts

| Layout | Description | Best For |
|--------|-------------|----------|
| `linear-progression` | Sequential flow left-to-right | Timelines, step-by-step |
| `binary-comparison` | Side-by-side A vs B | Before/after, pros-cons |
| `comparison-matrix` | Multi-factor grid | Feature comparisons |
| `hierarchical-layers` | Pyramid or stacked levels | Priority, importance |
| `hub-spoke` | Central node with radiating items | Concept maps, ecosystems |
| `bento-grid` | Varied-size tiles | Overview, summary |
| `funnel` | Narrowing stages | Conversion, filtering |
| `dashboard` | Metrics with charts/numbers | KPIs, data display |
| `venn-diagram` | Overlapping circles | Relationships, intersections |
| `circular-flow` | Continuous cycle | Recurring processes |
| `winding-roadmap` | Curved path with milestones | Journey, timeline |
| `tree-branching` | Parent-child hierarchy | Org charts, taxonomies |
| `iceberg` | Visible vs hidden layers | Surface vs depth |
| `bridge` | Gap with connection | Problem-solution |

**Usage**: Add `Layout: <name>` in slide's `// LAYOUT` section.

## Layout Selection Tips

**Match Layout to Content**:
| Content Type | Recommended Layouts |
|--------------|-------------------|
| Single narrative | `bullet-list`, `image-caption` |
| Two concepts | `split-screen`, `binary-comparison` |
| Three items | `three-columns`, `icon-grid` |
| Process/Steps | `linear-progression`, `winding-roadmap` |
| Data/Metrics | `dashboard`, `key-stat` |
| Relationships | `hub-spoke`, `venn-diagram` |
| Hierarchy | `hierarchical-layers`, `tree-branching` |

**Layout Flow Patterns**:
| Position | Recommended Layouts |
|----------|-------------------|
| Opening | `title-hero`, `agenda` |
| Middle | Content-specific layouts |
| Closing | `quote-callout`, `key-stat` |

**Common Mistakes to Avoid**:
- Using 3-column layout for 2 items (leaves columns empty)
- Stacking charts/tables below text (use side-by-side instead)
- Image layouts without actual images
- Quote layouts for emphasis (use only for real quotes with attribution)
