#!/usr/bin/env node
import fs from 'fs/promises';
import { existsSync } from 'fs';
import path from 'path';
import { pathToFileURL } from 'url';
import { ACADEMIC_STYLES, getTheme, sharedCss } from './html_deck_themes.mjs';

function escapeHtml(value) {
  return String(value ?? '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function normalizeText(value) {
  if (Array.isArray(value)) return value.map(normalizeText).filter(Boolean).join('\n');
  if (value == null) return '';
  return String(value).trim();
}

function assertSafeOutDir(outDir) {
  const parsed = path.parse(outDir);
  if (path.resolve(outDir) === parsed.root) {
    throw new Error(`Refusing to write deck into filesystem root: ${outDir}`);
  }
}

function inferAcademicStyle(outline) {
  const text = JSON.stringify(outline).toLowerCase();
  if (text.includes('workflow') || text.includes('process') || text.includes('route')) {
    return 'diagram-driven-isotype';
  }
  if (text.includes('mechanism') || text.includes('model') || text.includes('framework')) {
    return 'diagrammatic-minimalism';
  }
  if (text.includes('trend') || text.includes('dataset') || text.includes('market')) {
    return 'dense-research';
  }
  if (text.includes('summary') || text.includes('matrix') || text.includes('metric')) {
    return 'bento-grid';
  }
  return 'assertion-evidence';
}

function resolveAcademicStyle(outline, styleArg) {
  const requested = normalizeText(styleArg || outline.style_profile || outline.academic_style);
  const style = requested || inferAcademicStyle(outline);
  if (!ACADEMIC_STYLES.includes(style)) {
    throw new Error(`Unknown academic style "${style}". Use one of: ${ACADEMIC_STYLES.join(', ')}`);
  }
  return style;
}

function resolveAssetPath(assetPath, inputPath) {
  if (!assetPath) return '';
  if (path.isAbsolute(assetPath)) return assetPath;
  const candidates = [
    path.resolve(path.dirname(inputPath), assetPath),
    path.resolve(process.cwd(), assetPath)
  ];
  return candidates.find((candidate) => existsSync(candidate)) || candidates[0];
}

function slideNote(slide) {
  return normalizeText(slide.speaker_note || slide.speaker_notes || slide.notes || '');
}

function metricItems(slide) {
  if (Array.isArray(slide.metrics) && slide.metrics.length > 0) return slide.metrics;
  return (Array.isArray(slide.bullets) ? slide.bullets : []).slice(0, 6).map((item, index) => ({
    label: `Evidence ${index + 1}`,
    value: String(index + 1).padStart(2, '0'),
    detail: item
  }));
}

function diagramItems(slide) {
  if (Array.isArray(slide.diagram?.steps)) return slide.diagram.steps;
  if (Array.isArray(slide.diagram)) return slide.diagram;
  return (Array.isArray(slide.bullets) ? slide.bullets : []).slice(0, 4).map((item, index) => ({
    title: item,
    detail: slide.evidence?.[index] || ''
  }));
}

function inferLayout(slide, index) {
  if (slide.layout) return slide.layout;
  if (slide.diagram || normalizeText(slide.title).toLowerCase().includes('mechanism')) return 'diagram';
  if (Array.isArray(slide.metrics) && slide.metrics.length > 0) return 'metrics';
  if (Array.isArray(slide.images) && slide.images.length > 0) return 'evidence';
  if (index === 0) return 'cover';
  if ((slide.bullets || []).length >= 4) return 'metrics';
  return 'assertion';
}

function renderMasthead(outline, slide, index, total) {
  const left = escapeHtml(slide.kicker || outline.deck_type || 'Materials HTML Deck');
  const right = escapeHtml(slide.section || `${String(index + 1).padStart(2, '0')} / ${String(total).padStart(2, '0')}`);
  return `<div class="masthead"><div>${left}</div><div>${right}</div></div><div class="rule"></div>`;
}

function renderTitle(slide) {
  const kicker = slide.kicker ? `<div class="kicker">${escapeHtml(slide.kicker)}</div>` : '';
  const subtitle = slide.subtitle ? `<div class="subtitle">${escapeHtml(slide.subtitle)}</div>` : '';
  return `${kicker}<h1>${escapeHtml(slide.title || 'Untitled slide')}</h1>${subtitle}`;
}

function renderBullets(slide) {
  const bullets = Array.isArray(slide.bullets) ? slide.bullets : [];
  if (!bullets.length) return '';
  return `<ul class="bullet-list">${bullets.map((item) => `<li>${escapeHtml(item)}</li>`).join('')}</ul>`;
}

function renderFigures(slide, inputPath, manifestImages) {
  const images = Array.isArray(slide.images) ? slide.images : [];
  if (!images.length) return '';
  const className = images.length === 1 ? 'figure-grid single' : 'figure-grid';
  const figures = images.map((image, index) => {
    const resolved = resolveAssetPath(String(image.path || ''), inputPath);
    const src = resolved ? pathToFileURL(resolved).href : '';
    const caption = normalizeText(image.caption);
    manifestImages.push({
      path: image.path || '',
      resolved_path: resolved,
      alt: image.alt || `slide image ${index + 1}`,
      caption
    });
    return `<figure>
  <img src="${src}" alt="${escapeHtml(image.alt || `slide image ${index + 1}`)}" />
  ${caption ? `<figcaption>${escapeHtml(caption)}</figcaption>` : ''}
</figure>`;
  }).join('\n');
  return `<div class="${className}">${figures}</div>`;
}

function renderMetrics(slide) {
  const cards = metricItems(slide).slice(0, 6).map((metric) => {
    const value = escapeHtml(metric.value ?? metric.title ?? '');
    const label = escapeHtml(metric.label ?? 'Finding');
    const detail = escapeHtml(metric.detail ?? metric.text ?? '');
    return `<div class="card">
  <div class="metric-value">${value}</div>
  <div class="metric-label">${label}</div>
  ${detail ? `<p class="source-note">${detail}</p>` : ''}
</div>`;
  });
  if (slide.takeaway) {
    cards.push(`<div class="card takeaway-card">
  <div class="metric-label">Takeaway</div>
  <p>${escapeHtml(slide.takeaway)}</p>
</div>`);
  }
  const className = slide.takeaway ? 'metric-grid with-takeaway' : 'metric-grid';
  return `<div class="${className}">${cards.join('\n')}</div>`;
}

function renderDiagram(slide) {
  const nodes = diagramItems(slide).slice(0, 4).map((node, index) => {
    const title = escapeHtml(node.title ?? node.label ?? node);
    const detail = escapeHtml(node.detail ?? node.text ?? '');
    return `<div class="card diagram-node">
  <div class="node-index">${String(index + 1).padStart(2, '0')}</div>
  <div class="node-title">${title}</div>
  ${detail ? `<p class="source-note">${detail}</p>` : ''}
</div>`;
  }).join('\n');
  return `<div class="diagram-row">${nodes}</div>`;
}

function renderTakeaway(slide) {
  if (!slide.takeaway) return '';
  return `<div class="takeaway">${escapeHtml(slide.takeaway)}</div>`;
}

function renderSlideBody(slide, layout, context) {
  const manifestImages = context.manifestImages;
  if (layout === 'cover') {
    return `<main class="cover" style="margin-top:110px">
  <div class="watermark">${String(context.index + 1).padStart(2, '0')}</div>
  ${renderTitle(slide)}
  <div style="margin-top:72px; max-width:760px">${renderBullets(slide)}</div>
</main>`;
  }
  if (layout === 'metrics' || layout === 'bento') {
    return `<main style="margin-top:54px">
  ${renderTitle(slide)}
  ${renderMetrics(slide)}
</main>`;
  }
  if (layout === 'diagram') {
    return `<main style="margin-top:54px">
  ${renderTitle(slide)}
  ${renderDiagram(slide)}
  ${slide.source_note ? `<p class="source-note">${escapeHtml(slide.source_note)}</p>` : ''}
</main>`;
  }
  if (layout === 'evidence') {
    return `<main class="content-grid">
  <section>
    ${renderTitle(slide)}
    <div style="margin-top:34px">${renderBullets(slide)}</div>
    <div style="margin-top:34px">${renderTakeaway(slide)}</div>
  </section>
  <section>${renderFigures(slide, context.inputPath, manifestImages)}</section>
</main>`;
  }
  return `<main class="content-grid">
  <section>${renderTitle(slide)}</section>
  <section>
    <div class="card">${renderBullets(slide)}</div>
    <div style="margin-top:26px">${renderTakeaway(slide)}</div>
  </section>
</main>`;
}

function renderSlideHtml(slide, context) {
  const layout = inferLayout(slide, context.index);
  const body = renderSlideBody(slide, layout, context);
  const source = slide.source_note ? `<div>${escapeHtml(slide.source_note)}</div>` : '<div>HTML deck source</div>';
  return `<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=1920,height=1080,initial-scale=1">
<title>${escapeHtml(slide.title || `Slide ${context.index + 1}`)}</title>
<link rel="stylesheet" href="../shared/tokens.css">
<style>body { width: 1920px; height: 1080px; }</style>
</head>
<body data-academic-style="${context.style}" data-slide-layout="${layout}">
<div class="deck-slide">
  ${renderMasthead(context.outline, slide, context.index, context.total)}
  ${body}
  <footer class="footer">${source}<div>${String(context.index + 1).padStart(2, '0')} / ${String(context.total).padStart(2, '0')}</div></footer>
</div>
</body>
</html>`;
}

function renderIndexHtml({ outline, manifest, notes }) {
  const title = escapeHtml(outline.title || 'Materials HTML Deck');
  return `<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>${title}</title>
<script>
window.DECK_MANIFEST = ${JSON.stringify(manifest, null, 2)};
</script>
<script type="application/json" id="speaker-notes">${escapeHtml(JSON.stringify(notes, null, 2))}</script>
<style>
* { box-sizing: border-box; }
body { margin: 0; background: #111; color: #eee; font-family: Inter, system-ui, sans-serif; }
.topbar { height: 48px; display: flex; align-items: center; justify-content: space-between; padding: 0 18px; background: #181818; border-bottom: 1px solid #2b2b2b; font-size: 13px; }
.stage { height: calc(100vh - 48px); display: grid; place-items: center; }
iframe { width: min(100vw, calc((100vh - 56px) * 16 / 9)); height: min(calc(100vh - 56px), calc(100vw * 9 / 16)); border: 0; background: white; box-shadow: 0 24px 80px rgba(0,0,0,.5); }
.counter { color: #aaa; }
</style>
</head>
<body>
<div class="topbar"><strong>${title}</strong><span class="counter" id="counter"></span></div>
<main class="stage"><iframe id="slide-frame" title="HTML deck slide"></iframe></main>
<script>
const frame = document.getElementById('slide-frame');
const counter = document.getElementById('counter');
let current = 0;
function show(index) {
  current = Math.max(0, Math.min(window.DECK_MANIFEST.length - 1, index));
  const item = window.DECK_MANIFEST[current];
  frame.src = item.file;
  counter.textContent = (current + 1) + ' / ' + window.DECK_MANIFEST.length + ' - ' + item.label;
  location.hash = 'slide-' + (current + 1);
}
window.addEventListener('keydown', (event) => {
  if (event.key === 'ArrowRight' || event.key === 'PageDown' || event.key === ' ') show(current + 1);
  if (event.key === 'ArrowLeft' || event.key === 'PageUp') show(current - 1);
  if (event.key === 'Home') show(0);
  if (event.key === 'End') show(window.DECK_MANIFEST.length - 1);
});
const match = location.hash.match(/slide-(\\d+)/);
show(match ? Number(match[1]) - 1 : 0);
</script>
</body>
</html>`;
}

export async function renderHtmlDeck({ outline, inputPath, outDir, styleArg }) {
  assertSafeOutDir(outDir);
  const style = resolveAcademicStyle(outline, styleArg);
  const theme = getTheme(style);
  const slides = Array.isArray(outline.slides) && outline.slides.length > 0
    ? outline.slides
    : [{ title: outline.title || 'Untitled deck', bullets: [] }];

  await fs.rm(outDir, { recursive: true, force: true });
  await fs.mkdir(path.join(outDir, 'slides'), { recursive: true });
  await fs.mkdir(path.join(outDir, 'shared'), { recursive: true });

  await fs.writeFile(path.join(outDir, 'shared', 'tokens.css'), sharedCss(style), 'utf8');

  const manifest = [];
  const notes = [];
  const assetSlides = [];

  for (let index = 0; index < slides.length; index += 1) {
    const slide = slides[index];
    const file = `slides/slide_${String(index + 1).padStart(3, '0')}.html`;
    const manifestImages = [];
    const html = renderSlideHtml(slide, {
      outline,
      inputPath,
      style,
      theme,
      index,
      total: slides.length,
      manifestImages
    });
    await fs.writeFile(path.join(outDir, file), html, 'utf8');
    manifest.push({ file, label: slide.title || `Slide ${index + 1}` });
    notes.push(slideNote(slide));
    assetSlides.push({
      index: index + 1,
      title: slide.title || `Slide ${index + 1}`,
      layout: inferLayout(slide, index),
      images: manifestImages,
      speaker_note: slideNote(slide)
    });
  }

  await fs.writeFile(path.join(outDir, 'index.html'), renderIndexHtml({ outline, manifest, notes }), 'utf8');
  await fs.writeFile(path.join(outDir, 'speaker_notes.json'), JSON.stringify(notes, null, 2), 'utf8');
  await fs.writeFile(path.join(outDir, 'asset_manifest.json'), JSON.stringify({
    skill: 'materials-html-deck',
    academic_style: style,
    theme: theme.name,
    source: inputPath,
    index: 'index.html',
    slides: assetSlides
  }, null, 2), 'utf8');

  return {
    indexPath: path.join(outDir, 'index.html'),
    slideCount: slides.length,
    style
  };
}
