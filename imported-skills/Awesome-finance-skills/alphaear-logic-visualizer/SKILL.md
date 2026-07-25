---
name: alphaear-logic-visualizer
description: Create visualize finance logic diagrams (e.g., Draw.io XML) to explain complex finance transmission chains or finance logic flows.
---

# AlphaEar Logic Visualizer Skill

## Overview

This skill specializes in creating visual representations of logic flows, specifically generating Draw.io XML compatible diagrams. It is useful for visualizing investment theses or signal transmission chains.

## Capabilities

### 1. Generate Draw.io Diagrams

### 1. Generate Draw.io Diagrams (Agentic Workflow)

**YOU (the Agent)** are the Visualizer. Use the prompts in `references/PROMPTS.md` to generate the XML.

**Workflow:**
1.  **Generate XML**: Use the **Draw.io XML Generation Prompt** from `references/PROMPTS.md` to convert your logical chain into XML.
2.  **Save/Render**: Use `scripts/visualizer.py` method `render_drawio_to_html(xml_content, filename)` to save the XML into a viewable HTML file for the user.

**Example Usage (Conceptual):**
- **Agent Action**: "I will now generate a Draw.io XML for the transmission chain..."
- **Tool Call**: `visualizer.render_drawio_to_html(xml_content="<mxGraphModel>...", filename="chain_visual.html")`


## Dependencies

-   None (Standard Library for string manipulation).
