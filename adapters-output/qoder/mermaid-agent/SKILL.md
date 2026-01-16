---
name: mermaid
description: A comprehensive skill for creating all types of Mermaid diagrams including flowcharts, sequence diagrams, class diagrams, state diagrams, entity relationship diagrams, user journey diagrams, Gantt charts, pie charts, quadrant charts, requirement diagrams, Git graphs, C4 diagrams, mindmaps, timelines, ZenUML, Sankey diagrams, XY charts, block diagrams, packet diagrams, Kanban boards, architecture diagrams, radar charts, and treemaps. Use this skill whenever the user requests to create, draw, or visualize any diagram, flowchart, or structured chart using Mermaid syntax.
license: Complete terms in LICENSE.txt
---

## When to use this skill

Use this skill whenever the user wants to:
- Create any type of diagram or flowchart
- Visualize processes, workflows, or system architectures
- Draw sequence diagrams, class diagrams, or state diagrams
- Create project timelines (Gantt charts)
- Visualize data relationships (ER diagrams, entity relationships)
- Create user journey maps
- Generate pie charts, quadrant charts, or other data visualizations
- Draw Git branching structures
- Create mindmaps or hierarchical structures
- Visualize system architectures (C4 diagrams)
- Create timelines or event sequences
- Generate any other diagram type supported by Mermaid

## How to use this skill

To create a Mermaid diagram:

1. **Identify the diagram type** from the user's request:
   - Flowchart/flow chart/流程图 → `flowchart` or `graph`
   - Sequence diagram/时序图 → `sequenceDiagram`
   - Class diagram/类图 → `classDiagram`
   - State diagram/状态图 → `stateDiagram` or `stateDiagram-v2`
   - Entity relationship diagram/实体关系图 → `erDiagram`
   - User journey/用户旅程图 → `journey`
   - Gantt chart/甘特图 → `gantt`
   - Pie chart/饼图 → `pie`
   - Quadrant chart/象限图 → `quadrantChart`
   - Requirement diagram/需求图 → `requirementDiagram`
   - Git graph/Git图 → `gitGraph`
   - C4 diagram/C4图 → `C4Context` or other C4 types
   - Mindmap/思维导图 → `mindmap`
   - Timeline/时间线图 → `timeline`
   - ZenUML/禅UML → `zenuml`
   - Sankey diagram/桑基图 → `sankey`
   - XY chart/XY图 → `xychart`
   - Block diagram/方块图 → `block`
   - Packet diagram/数据包图 → `packet`
   - Kanban/看板图 → `kanban`
   - Architecture diagram/架构图 → `architecture-beta`
   - Radar chart/雷达图 → `radar-beta`
   - Treemap/树状图 → `treemap-beta`

2. **Load the appropriate example file** from the `examples/` directory:
   - `examples/flowchart.md` - For flowcharts and process diagrams
   - `examples/sequence.md` - For sequence diagrams showing interactions
   - `examples/class.md` - For class diagrams and object-oriented designs
   - `examples/state.md` - For state diagrams and state machines
   - `examples/er.md` - For entity relationship diagrams
   - `examples/journey.md` - For user journey maps
   - `examples/gantt.md` - For Gantt charts and project timelines
   - `examples/pie.md` - For pie charts
   - `examples/quadrant.md` - For quadrant charts
   - `examples/requirement.md` - For requirement diagrams
   - `examples/gitgraph.md` - For Git branching diagrams
   - `examples/c4.md` - For C4 architecture diagrams
   - `examples/mindmap.md` - For mindmaps
   - `examples/timeline.md` - For timeline diagrams
   - `examples/zenuml.md` - For ZenUML diagrams
   - `examples/sankey.md` - For Sankey flow diagrams
   - `examples/xychart.md` - For XY charts (bar/line charts)
   - `examples/block.md` - For block diagrams
   - `examples/packet.md` - For packet diagrams
   - `examples/kanban.md` - For Kanban boards
   - `examples/architecture.md` - For architecture diagrams
   - `examples/radar.md` - For radar charts
   - `examples/treemap.md` - For treemap diagrams

3. **Follow the specific instructions** in that example file for syntax, structure, and best practices

4. **Generate the Mermaid code** wrapped in a code block:
   ```mermaid
   <diagram-type>
   ...diagram content...
   ```

5. **Include styling and configuration** when needed:
   - Use `%%{ init: { theme: 'base' } }%%` for theme configuration
   - Apply `style` directives for node styling
   - Use `classDef` for reusable style classes

6. **Validate the syntax**:
   - Ensure all required elements are present
   - Check that relationships and connections are properly defined
   - Verify date formats for Gantt charts
   - Confirm data formats for charts (pie, quadrant, etc.)

If the diagram type doesn't match any existing example, refer to the Mermaid documentation or ask the user for clarification about the desired visualization.

## Keywords

mermaid, diagram, flowchart, flow chart, sequence diagram, class diagram, state diagram, entity relationship, ER diagram, user journey, Gantt chart, pie chart, quadrant chart, requirement diagram, Git graph, C4 diagram, mindmap, timeline, ZenUML, Sankey diagram, XY chart, block diagram, packet diagram, Kanban, architecture diagram, radar chart, treemap, 流程图, 时序图, 类图, 状态图, 实体关系图, 用户旅程图, 甘特图, 饼图, 象限图, 需求图, Git图, C4图, 思维导图, 时间线图, 桑基图, XY图, 方块图, 数据包图, 看板图, 架构图, 雷达图, 树状图
