---
name: ux-journey-mapper
description: Create detailed, versioned UX journey maps with multi-format export (Mermaid, JSON, HTML, Markdown). Maps user flows, pain points, touchpoints, emotional arcs, and system interactions with Git-backed version control.
license: MIT
---

# UX Journey Mapper

Create comprehensive user journey maps for any application or product. This tool generates interactive journey visualizations, structured data exports, and maintains version history with automatic changelog generation.

## When to Use

- Designing new user experiences
- Understanding current user flows
- Identifying pain points and opportunities
- Documenting emotional arcs across customer journeys
- Presenting user research to stakeholders
- Iterating on journey designs with version tracking

## Core Capabilities

### 1. Journey Creation

Define a user journey with:
- **User Persona**: Who is the user (e.g., "New SaaS User", "Enterprise Admin")
- **Journey Stage**: awareness | consideration | decision | retention | advocacy
- **Touchpoints**: Array of { name, channel, emotion, system }
- **Pain Points**: Key friction areas
- **Opportunities**: Moments for improvement

### 2. Multi-Format Export

Outputs include:
- **Mermaid Diagram**: Interactive flowchart visualization
- **JSON Structure**: Programmatic access to journey data
- **HTML Interactive**: Web view with hover interactions
- **Markdown Report**: Version-control friendly format

### 3. Git-Backed Versioning

- Automatic semantic versioning (v1.0.0 → v1.1.0)
- Visual diffs between versions
- Changelog generation
- Commit hash tracking for audit trails

## Usage Examples

### Basic Journey Mapping

```json
{
  "user_persona": "First-time Mobile App User",
  "journey_stage": "awareness",
  "touchpoints": [
    {
      "name": "App Store Discovery",
      "channel": "mobile",
      "emotion": "curious",
      "system": "App Store Search"
    },
    {
      "name": "Download & Install",
      "channel": "mobile",
      "emotion": "hopeful",
      "system": "Device Storage"
    },
    {
      "name": "First Launch",
      "channel": "mobile",
      "emotion": "confused",
      "system": "App Onboarding"
    }
  ],
  "pain_points": [
    "Unclear value proposition on first screen",
    "Complex permission requests",
    "No guided tutorial"
  ],
  "opportunities": [
    "Add animated onboarding walkthrough",
    "Show value before asking permissions",
    "Include contextual help tooltips"
  ]
}
```

### Export to Mermaid

Generates interactive journey swimlane diagrams showing:
- User actions
- System responses
- Emotional state changes
- Touchpoint interactions

### Export to HTML

Interactive visualization with:
- Timeline scrubbing
- Hover tooltips for details
- Responsive layout for presentations
- Print-friendly styling

## Integration with Your Workflow

### Use with Claude Code

```
Use the UX journey mapper to create a journey map for [user persona]
in the [product/feature] including pain points and opportunities.
Export to Mermaid diagram.
```

### Use Programmatically

```javascript
import { createJourneyMap, exportFormats } from '@fused-gaming/ux-journey-mapper';

const journey = await createJourneyMap({
  persona: "Power User",
  stage: "retention",
  touchpoints: [...],
  painPoints: [...],
  opportunities: [...]
});

await journey.exportTo(exportFormats.MERMAID);
await journey.exportTo(exportFormats.HTML);
await journey.exportTo(exportFormats.JSON);
```

## Best Practices

- **One Journey Per Session**: Focus on a single user persona and stage per session
- **Be Specific**: Use concrete user actions, not generalizations
- **Include Emotions**: Emotional arcs reveal opportunities and pain points
- **Map System Interactions**: Show how your product responds at each touchpoint
- **Version Your Iterations**: Track how journeys evolve based on feedback
- **Share Versions**: Use HTML or Markdown exports for stakeholder review

## Output Structure

Each journey generates:
- `.journey.md` - Markdown version for Git
- `.journey.json` - Structured data
- `.journey.html` - Interactive visualization
- `.journey.mermaid` - Mermaid diagram code
- `CHANGELOG.md` - Version history

## Attribution

Created by [Fused Gaming](https://github.com/fused-gaming)
