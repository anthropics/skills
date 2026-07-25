#!/usr/bin/env node
export const ACADEMIC_STYLES = [
  'assertion-evidence',
  'dense-research',
  'diagrammatic-minimalism',
  'diagram-driven-isotype',
  'two-font-consulting',
  'bento-grid'
];

const THEMES = {
  'assertion-evidence': {
    name: 'Assertion Evidence',
    background: '#fbfbf8',
    surface: '#ffffff',
    title: '#171717',
    body: '#2f3437',
    muted: '#737373',
    accent: '#24547a',
    accent2: '#b55b3d',
    rule: '#dad7ce',
    serif: '"Source Serif 4", "Noto Serif SC", Georgia, serif',
    sans: 'Inter, "Noto Sans SC", "Microsoft YaHei", system-ui, sans-serif',
    mono: '"IBM Plex Mono", Consolas, monospace',
    radius: '10px',
    shadow: '0 18px 40px rgba(20, 24, 28, 0.08)'
  },
  'dense-research': {
    name: 'Dense Research Report',
    background: '#ffffff',
    surface: '#f7f9fc',
    title: '#101828',
    body: '#1f2937',
    muted: '#667085',
    accent: '#0066cc',
    accent2: '#d68a2f',
    rule: '#d8dee8',
    serif: '"Source Serif 4", "Noto Serif SC", Georgia, serif',
    sans: 'Inter, "Noto Sans SC", "Microsoft YaHei", system-ui, sans-serif',
    mono: '"IBM Plex Mono", Consolas, monospace',
    radius: '4px',
    shadow: 'none'
  },
  'diagrammatic-minimalism': {
    name: 'Diagrammatic Minimalism',
    background: '#faf9f4',
    surface: '#ffffff',
    title: '#191919',
    body: '#303030',
    muted: '#68645d',
    accent: '#8b1e3f',
    accent2: '#2f6f73',
    rule: '#dfd9cc',
    serif: '"Source Serif 4", "Noto Serif SC", Georgia, serif',
    sans: 'Manrope, "Noto Sans SC", "Microsoft YaHei", system-ui, sans-serif',
    mono: '"IBM Plex Mono", Consolas, monospace',
    radius: '999px',
    shadow: '0 14px 34px rgba(70, 52, 30, 0.08)'
  },
  'diagram-driven-isotype': {
    name: 'Diagram Driven Isotype',
    background: '#f8fbfd',
    surface: '#ffffff',
    title: '#0f172a',
    body: '#253041',
    muted: '#64748b',
    accent: '#0e7490',
    accent2: '#6f8f2f',
    rule: '#cbd8e2',
    serif: '"Source Serif 4", "Noto Serif SC", Georgia, serif',
    sans: 'Inter, "Noto Sans SC", "Microsoft YaHei", system-ui, sans-serif',
    mono: '"IBM Plex Mono", Consolas, monospace',
    radius: '8px',
    shadow: '0 16px 36px rgba(15, 23, 42, 0.08)'
  },
  'two-font-consulting': {
    name: 'Two Font Consulting',
    background: '#f8f7f3',
    surface: '#ffffff',
    title: '#051c2c',
    body: '#1f2933',
    muted: '#5c6773',
    accent: '#00805a',
    accent2: '#b88746',
    rule: '#d9d6ca',
    serif: '"Playfair Display", "Noto Serif SC", Georgia, serif',
    sans: 'Inter, "Noto Sans SC", "Microsoft YaHei", system-ui, sans-serif',
    mono: '"IBM Plex Mono", Consolas, monospace',
    radius: '6px',
    shadow: '0 16px 42px rgba(5, 28, 44, 0.08)'
  },
  'bento-grid': {
    name: 'Bento Grid',
    background: '#f5f5f7',
    surface: '#ffffff',
    title: '#111111',
    body: '#2d2d2d',
    muted: '#6e6e73',
    accent: '#3b5bdb',
    accent2: '#d06b35',
    rule: '#dedee4',
    serif: '"Source Serif 4", "Noto Serif SC", Georgia, serif',
    sans: 'Inter, "Noto Sans SC", "Microsoft YaHei", system-ui, sans-serif',
    mono: '"IBM Plex Mono", Consolas, monospace',
    radius: '18px',
    shadow: '0 18px 42px rgba(30, 30, 40, 0.10)'
  }
};

export function getTheme(style) {
  return THEMES[style] || THEMES['assertion-evidence'];
}

export function sharedCss(style) {
  const theme = getTheme(style);
  return `:root {
  --deck-bg: ${theme.background};
  --deck-surface: ${theme.surface};
  --deck-title: ${theme.title};
  --deck-body: ${theme.body};
  --deck-muted: ${theme.muted};
  --deck-accent: ${theme.accent};
  --deck-accent-2: ${theme.accent2};
  --deck-rule: ${theme.rule};
  --deck-radius: ${theme.radius};
  --deck-shadow: ${theme.shadow};
  --font-serif: ${theme.serif};
  --font-sans: ${theme.sans};
  --font-mono: ${theme.mono};
}
* { box-sizing: border-box; }
html, body { width: 1920px; height: 1080px; margin: 0; overflow: hidden; }
body {
  position: relative;
  background: var(--deck-bg);
  color: var(--deck-body);
  font-family: var(--font-sans);
  letter-spacing: 0;
}
.deck-slide {
  width: 1920px;
  height: 1080px;
  position: relative;
  overflow: hidden;
  padding: 72px 96px 64px;
}
.masthead {
  display: flex;
  justify-content: space-between;
  align-items: flex-start;
  font: 700 15px/1.4 var(--font-mono);
  letter-spacing: 0.18em;
  text-transform: uppercase;
  color: var(--deck-muted);
}
.rule { height: 1px; background: var(--deck-rule); margin-top: 26px; }
.kicker {
  color: var(--deck-accent);
  font: 800 15px/1.2 var(--font-mono);
  text-transform: uppercase;
  letter-spacing: 0.16em;
}
h1 {
  color: var(--deck-title);
  font-family: var(--font-serif);
  font-size: 76px;
  line-height: 1.05;
  letter-spacing: 0;
  margin: 0;
  max-width: 1320px;
}
.cover h1 { font-size: 118px; max-width: 1500px; }
.subtitle {
  color: var(--deck-muted);
  font-size: 30px;
  line-height: 1.38;
  margin-top: 24px;
  max-width: 980px;
}
.content-grid {
  display: grid;
  grid-template-columns: minmax(0, 0.92fr) minmax(0, 1.08fr);
  gap: 64px;
  margin-top: 56px;
}
.card {
  background: var(--deck-surface);
  border: 1px solid var(--deck-rule);
  border-radius: var(--deck-radius);
  box-shadow: var(--deck-shadow);
  padding: 30px 34px;
}
.bullet-list {
  display: grid;
  gap: 20px;
  margin: 0;
  padding: 0;
  list-style: none;
}
.bullet-list li {
  border-left: 5px solid var(--deck-accent);
  padding: 12px 0 12px 22px;
  font-size: 30px;
  line-height: 1.35;
}
.figure-grid { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 22px; }
.figure-grid.single { grid-template-columns: 1fr; }
figure { margin: 0; }
figure img {
  width: 100%;
  height: 420px;
  object-fit: contain;
  background: #fff;
  border: 1px solid var(--deck-rule);
  border-radius: calc(var(--deck-radius) - 2px);
}
figcaption, .source-note {
  color: var(--deck-muted);
  font-size: 18px;
  line-height: 1.35;
  margin-top: 12px;
}
.takeaway {
  background: var(--deck-accent);
  color: #fff;
  border-radius: var(--deck-radius);
  padding: 28px 34px;
  font-size: 30px;
  line-height: 1.28;
}
.metric-grid {
  display: grid;
  grid-template-columns: repeat(3, minmax(0, 1fr));
  gap: 24px;
  margin-top: 54px;
}
.metric-grid .card {
  min-height: 204px;
}
.metric-grid.with-takeaway .takeaway-card {
  grid-column: span 2;
  background: var(--deck-accent);
  color: #fff;
}
.takeaway-card .metric-label {
  color: rgba(255, 255, 255, 0.74);
  margin-top: 0;
}
.takeaway-card p {
  margin: 28px 0 0;
  font-size: 30px;
  line-height: 1.28;
  color: #fff;
}
.metric-value {
  color: var(--deck-title);
  font: 700 82px/1 var(--font-sans);
  font-variant-numeric: tabular-nums;
}
.metric-label {
  color: var(--deck-muted);
  font: 700 18px/1.3 var(--font-mono);
  letter-spacing: 0.12em;
  text-transform: uppercase;
  margin-top: 18px;
}
.diagram-row {
  display: grid;
  grid-template-columns: repeat(4, minmax(0, 1fr));
  gap: 22px;
  margin-top: 58px;
}
.diagram-node {
  min-height: 230px;
  border-top: 8px solid var(--deck-accent);
  display: flex;
  flex-direction: column;
  justify-content: space-between;
}
.node-index {
  font: 700 20px/1 var(--font-mono);
  color: var(--deck-accent);
}
.node-title {
  color: var(--deck-title);
  font-size: 34px;
  line-height: 1.16;
  font-weight: 760;
}
.footer {
  position: absolute;
  left: 96px;
  right: 96px;
  bottom: 42px;
  display: flex;
  justify-content: space-between;
  color: var(--deck-muted);
  font: 600 15px/1.3 var(--font-mono);
  letter-spacing: 0.12em;
  text-transform: uppercase;
}
.watermark {
  position: absolute;
  right: 80px;
  bottom: 94px;
  font: 800 180px/0.8 var(--font-sans);
  color: color-mix(in srgb, var(--deck-accent) 10%, transparent);
  z-index: 0;
}`;
}
