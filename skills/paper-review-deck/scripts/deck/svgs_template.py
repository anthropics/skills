# Copy this file to the deck folder as svgs.py. The functions in SVGS are called in the order
# the "(figure: …)" markers appear in the manuscript. Each returns an '<svg viewBox="0 0 W H">' string.
# The style constants match the deck palette (DECK_PALETTE is set by build.py from the frontmatter).
import os
if os.environ.get("DECK_PALETTE", "mono") != "color":   # default: grayscale diagrams (text, lines and boxes)
    BLUE = "#111"; MAROON = "#111"; INK = "#111"; GRAY = "#6b7280"; LINE = "#cfcfcf"; PALE = "#f3f3f3"
else:
    BLUE = "#004094"; MAROON = "#8C2D2D"; INK = "#111"; GRAY = "#6b7280"; LINE = "#c9d3e3"; PALE = "#f3f6fb"

def lineage(nodes, ax_l, ax_r, note="", fix_label="Fixes"):
    """Fixed "landscape" layout for the multi-paper mode: paper cards above a horizontal arrow (axis labels left/right).
    nodes = [(short name, 'Venue YYYY (Oral) · arXiv YYYY.MM', 'what it fixes', 'one-line method'), ...] in presentation order."""
    W, H = 1312, 470; y = 330; n = len(nodes)
    s = [f'<svg viewBox="0 0 {W} {H}" xmlns="http://www.w3.org/2000/svg" font-family="inherit">',
         f'<defs><marker id="ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="8" markerHeight="8" orient="auto"><path d="M0 0L10 5L0 10z" fill="{GRAY}"/></marker></defs>',
         f'<line x1="40" y1="{y}" x2="{W-40}" y2="{y}" stroke="{GRAY}" stroke-width="3" marker-end="url(#ah)"/>',
         f'<text x="40" y="{y+46}" font-size="22" fill="{GRAY}">{ax_l}</text>',
         f'<text x="{W-40}" y="{y+46}" text-anchor="end" font-size="22" fill="{GRAY}">{ax_r}</text>']
    xs = [W * (0.18 + 0.64 * i / max(n - 1, 1)) for i in range(n)]
    cw = min(420, (W - 80) / n - 20)
    for xx, (name, venue, fix, how) in zip(xs, nodes):
        s += [f'<circle cx="{xx}" cy="{y}" r="14" fill="{MAROON}"/>',
              f'<line x1="{xx}" y1="{y-44}" x2="{xx}" y2="{y-14}" stroke="{LINE}" stroke-width="2"/>',
              f'<rect x="{xx-cw/2}" y="{y-304}" width="{cw}" height="260" rx="14" fill="{PALE}" stroke="{LINE}" stroke-width="2"/>',
              f'<text x="{xx}" y="{y-250}" text-anchor="middle" font-size="36" font-weight="700" fill="{BLUE}">{name}</text>',
              f'<text x="{xx}" y="{y-212}" text-anchor="middle" font-size="21" fill="{GRAY}">{venue}</text>',
              f'<line x1="{xx-cw/2+50}" y1="{y-190}" x2="{xx+cw/2-50}" y2="{y-190}" stroke="{LINE}" stroke-width="2"/>',
              f'<text x="{xx}" y="{y-150}" text-anchor="middle" font-size="22" fill="{GRAY}">{fix_label}</text>',
              f'<text x="{xx}" y="{y-112}" text-anchor="middle" font-size="27" font-weight="600" fill="{MAROON}">{fix}</text>',
              f'<text x="{xx}" y="{y-70}" text-anchor="middle" font-size="22" fill="{INK}">{how}</text>']
    if note: s.append(f'<text x="{W/2}" y="{H-14}" text-anchor="middle" font-size="21" fill="{GRAY}">{note}</text>')
    s.append('</svg>'); return "\n".join(s)

def mapping(rows, lw=430, rw=682):
    """Left (condition/category) -> right (paper/description) mapping. rows = [(left label, right text, is_new), ...];
    new rows are drawn with a dashed maroon outline."""
    W, rh, gap = 1312, 74, 22; H = 10 + len(rows) * (rh + gap)
    lx, rx = 20, W - rw
    s = [f'<svg viewBox="0 0 {W} {H}" xmlns="http://www.w3.org/2000/svg" font-family="inherit">',
         f'<defs><marker id="am" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M0 0L10 5L0 10z" fill="{GRAY}"/></marker>'
         f'<marker id="am2" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M0 0L10 5L0 10z" fill="{MAROON}"/></marker></defs>']
    for i, (l, r, new) in enumerate(rows):
        yy = 10 + i * (rh + gap); col = MAROON if new else BLUE; dash = ' stroke-dasharray="10 7"' if new else ''
        s += [f'<rect x="{lx}" y="{yy}" width="{lw}" height="{rh}" rx="10" fill="#fff" stroke="{col}" stroke-width="2.5"{dash}/>',
              f'<text x="{lx+24}" y="{yy+rh/2+9}" font-size="25" font-weight="600" fill="{col}">{l}</text>',
              f'<rect x="{rx}" y="{yy}" width="{rw}" height="{rh}" rx="10" fill="{PALE}" stroke="{LINE}" stroke-width="2"/>',
              f'<text x="{rx+24}" y="{yy+rh/2+9}" font-size="24" fill="{INK}">{r}</text>',
              f'<line x1="{lx+lw+8}" y1="{yy+rh/2}" x2="{rx-10}" y2="{yy+rh/2}" stroke="{MAROON if new else GRAY}" stroke-width="2.5"{dash} marker-end="url(#{"am2" if new else "am"})"/>']
    s.append('</svg>'); return "\n".join(s)

# Example: only the part below changes from deck to deck
def fig1():
    return lineage([("Paper A", "CoRL 2025 (Oral) · arXiv 2025.05", "simulator params", "sampling SysID"),
                    ("Paper B", "RSS 2025 · arXiv 2025.02", "simulator + Δa", "learned residual action"),
                    ("Paper C", "CoRL 2026 · arXiv 2026.06", "policy executor (IDM)", "2 min, LoRA")],
                   "fix the simulator", "fix the policy", "one lab, three answers")
def fig2():
    return mapping([("C  Domain randomization", "left column — robust without real data", False),
                    ("D  Actuator modeling", "Paper A · Paper B", False),
                    ("E  Few-shot real adaptation (proposed)", "Paper C", True)])
SVGS = [fig1, fig2]
