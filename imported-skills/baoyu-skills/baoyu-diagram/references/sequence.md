# Sequence Diagram Layout

## Core Elements

| Element | Visual | Description |
|---------|--------|-------------|
| Actor/Participant | Box at top + dashed vertical lifeline | Each entity in the interaction |
| Sync message | Solid arrow → | Request or call |
| Async message | Open arrowhead → | Fire-and-forget |
| Return message | Dashed arrow ← | Response |
| Activation bar | Narrow filled rect on lifeline | Entity is processing |
| Self-message | Arrow looping back to same lifeline | Internal processing |
| Note | Rounded rect with folded corner | Annotation |
| Alt/Opt frame | Dashed boundary with label tab | Conditional block |
| Loop frame | Dashed boundary with "loop" tab | Repetition |

## Layout Algorithm

1. **Place actors** horizontally across the top, evenly spaced (150-200px apart)
2. **Draw lifelines** as vertical dashed lines from each actor box downward
3. **Place messages** as horizontal arrows between lifelines, top to bottom in time order
4. **Vertical spacing** between messages: 40-50px
5. **Activation bars:** 10px wide, centered on lifeline, spanning from incoming to outgoing message

## Actor Box

```svg
<!-- Actor box -->
<rect x="X" y="20" width="130" height="45" rx="6" fill="#0f172a"/>
<rect x="X" y="20" width="130" height="45" rx="6" fill="rgba(8,51,68,0.4)" stroke="#22d3ee" stroke-width="1.5"/>
<text x="CX" y="47" fill="white" font-size="11" font-weight="600" text-anchor="middle">Actor Name</text>

<!-- Lifeline -->
<line x1="CX" y1="65" x2="CX" y2="BOTTOM" stroke="#334155" stroke-width="1" stroke-dasharray="6,4"/>
```

## Message Arrows

```svg
<!-- Sync message (solid arrow) -->
<line x1="FROM_CX" y1="Y" x2="TO_CX" y2="Y" stroke="#94a3b8" stroke-width="1.5" marker-end="url(#arrow)"/>
<text x="MID_X" y="Y-8" fill="#e2e8f0" font-size="9" text-anchor="middle">methodCall()</text>

<!-- Return message (dashed arrow, reversed direction) -->
<line x1="TO_CX" y1="Y" x2="FROM_CX" y2="Y" stroke="#64748b" stroke-width="1" stroke-dasharray="6,3" marker-end="url(#arrow)"/>
<text x="MID_X" y="Y-8" fill="#94a3b8" font-size="8" text-anchor="middle" font-style="italic">response</text>

<!-- Self-message (loop arrow) -->
<path d="M CX,Y L CX+40,Y L CX+40,Y+25 L CX,Y+25" fill="none" stroke="#94a3b8" stroke-width="1.5" marker-end="url(#arrow)"/>
<text x="CX+45" y="Y+15" fill="#e2e8f0" font-size="8">process()</text>
```

## Activation Bar

```svg
<rect x="CX-5" y="START_Y" width="10" height="H" rx="2" fill="rgba(8,51,68,0.6)" stroke="#22d3ee" stroke-width="1"/>
```

## Conditional / Loop Frames

```svg
<!-- Frame boundary -->
<rect x="X" y="Y" width="W" height="H" rx="4" fill="none" stroke="#64748b" stroke-width="1" stroke-dasharray="4,3"/>
<!-- Frame label tab -->
<rect x="X" y="Y" width="50" height="18" rx="4" fill="rgba(30,41,59,0.8)" stroke="#64748b" stroke-width="1"/>
<text x="X+25" y="Y+13" fill="#94a3b8" font-size="8" font-weight="600" text-anchor="middle">alt</text>
<!-- Condition text -->
<text x="X+60" y="Y+13" fill="#94a3b8" font-size="8" font-style="italic">[condition]</text>
<!-- Divider line for else -->
<line x1="X" y1="MID_Y" x2="X+W" y2="MID_Y" stroke="#64748b" stroke-width="1" stroke-dasharray="4,3"/>
<text x="X+10" y="MID_Y+13" fill="#94a3b8" font-size="8" font-style="italic">[else]</text>
```

## Numbering

For complex sequences (8+ messages), number each message:

```svg
<circle cx="FROM_CX-15" cy="Y" r="8" fill="rgba(59,130,246,0.3)" stroke="#60a5fa" stroke-width="1"/>
<text x="FROM_CX-15" y="Y+3" fill="#60a5fa" font-size="7" font-weight="600" text-anchor="middle">1</text>
```

## Color Assignment

Assign each actor a distinct color from the palette. Use that color for:
- Actor box stroke
- Activation bar on that lifeline
- Outgoing arrows from that actor (optional, for visual clarity in complex diagrams)
