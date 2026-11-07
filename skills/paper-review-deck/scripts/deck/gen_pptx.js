// layout.json (measured from the HTML deck) -> editable PPTX, 4:3
const fs = require('fs');
const path = require('path');
const pptxgen = require('pptxgenjs');
// Theme application only when apply_theme.js from the Anthropic pptx skill is available (the PPTX is generated either way)
let applyTheme = null;
if (process.env.PPTX_SKILL) { try { applyTheme = require(process.env.PPTX_SKILL + '/scripts/apply_theme.js').applyTheme; } catch (e) { applyTheme = null; } }

const RAW = JSON.parse(fs.readFileSync(process.env.LAYOUT || 'layout.json', 'utf8'));
const L = RAW.slides || RAW; const META = RAW.meta || {};
const FOOT_L = process.env.FOOT_L || META.footer_left || '';
const FOOT_C = process.env.FOOT_C || META.footer_center || '';
const OUT = process.argv[2] || 'deck.pptx';
const PX = 144;                      // 1440 px = 10 in
const X = v => v / PX;
const PT = px => Math.round(px * 0.5 * 10) / 10;   // 1 px = 0.5 pt on this canvas
const FONT = process.env.FONT || 'Malgun Gothic';
const MONO = 'Courier New';

const PAL_MONO = (process.env.DECK_PALETTE || 'mono') !== 'color';   // mono: text, titles, table headers and accents in grayscale (images unchanged)
const COL = PAL_MONO ? { BLUE: '111111', MAROON: '111111', GRAY: '6B7280', LINE: 'D4D4D4', PALE: 'F1F1F1', INK: '111111' }
                 : { BLUE: '004094', MAROON: '8C2D2D', GRAY: '6B7280', LINE: 'D5DCE8', PALE: 'F3F6FB', INK: '111111' };
const THEME = {
  name: 'Paper Review',
  headFontFace: FONT, bodyFontFace: FONT,
  colors: PAL_MONO ? { dk1: '111111', lt1: 'FFFFFF', dk2: '333333', lt2: 'F1F1F1', accent1: '111111', accent2: '333333', accent3: '6B7280', accent4: 'D4D4D4', accent5: '8A8F98', accent6: '555555', hlink: '111111', folHlink: '555555' }
              : { dk1: '111111', lt1: 'FFFFFF', dk2: '004094', lt2: 'F3F6FB',
    accent1: '004094', accent2: '8C2D2D', accent3: '6B7280', accent4: 'D5DCE8', accent5: '8A8F98', accent6: '333333',
    hlink: '004094', folHlink: '8C2D2D' },
};

const pres = new pptxgen();
pres.defineLayout({ name: 'FOUR_THREE', width: 10, height: 7.5 });
pres.layout = 'FOUR_THREE';
pres.theme = { headFontFace: FONT, bodyFontFace: FONT };
pres.author = FOOT_L.split('·')[0].trim() || 'Presenter';
pres.title = process.env.TITLE || META.title || 'Deck';

const footer = [
  { line: { x: X(64), y: X(1024), w: X(1312), h: 0, line: { color: COL.LINE, width: 0.75 } } },
  { text: { text: FOOT_L, options: { x: X(64), y: X(1030), w: 3.2, h: 0.24, fontSize: 9, color: '777777', margin: 0 } } },
  { text: { text: FOOT_C, options: { x: 3.4, y: X(1030), w: 3.2, h: 0.24, fontSize: 9, color: '777777', align: 'center', margin: 0 } } },
];
pres.defineSlideMaster({
  title: 'CONTENT', background: { color: 'FFFFFF' },
  objects: [...footer,
    { placeholder: { options: { name: 'title', type: 'title', x: X(64), y: X(46), w: X(1312), h: X(64), fontSize: 22, bold: true, color: COL.BLUE, align: 'left', valign: 'top', margin: 0 }, text: '' } }],
  slideNumber: { x: X(1376) - 0.6, y: X(1030), w: 0.6, h: 0.24, fontSize: 9, color: '777777', align: 'right', margin: 0 },
});
pres.defineSlideMaster({
  title: 'PART', background: { color: 'FFFFFF' }, objects: [...footer],
  slideNumber: { x: X(1376) - 0.6, y: X(1030), w: 0.6, h: 0.24, fontSize: 9, color: '777777', align: 'right', margin: 0 },
});
pres.defineSlideMaster({ title: 'COVER', background: { color: 'FFFFFF' }, objects: [] });

function runOpts(r, extra = {}) {
  const o = { bold: !!r.bold, italic: !!r.italic, color: r.color || COL.INK, ...extra };
  if (r.mono) o.fontFace = MONO;
  return o;
}
const textRuns = (runs, extra) => runs.map(r => ({ text: r.text, options: runOpts(r, extra) }));
const fitW = (x, w) => w > 6.5 ? Math.min(w * 1.04, 10 - x - 0.15) : w;

let sectionNo = 0;
pres.addSection({ title: 'Intro' });
let section = 'Intro';

L.forEach((s, i) => {
  if (s.kind === 'part') {
    const t = s.items.map(it => (it.runs || []).map(r => r.text).join('')).join(' ');
    section = t; pres.addSection({ title: t });
  }
  const master = s.kind === 'cover' ? 'COVER' : s.kind === 'part' ? 'PART' : 'CONTENT';
  const slide = pres.addSlide({ masterName: master, sectionTitle: section });
  let n = 0;
  const name = k => `${k}-${++n}`;

  for (const it of s.items) {
    const x = X(it.x), y = X(it.y), w = X(it.w), h = X(it.h);
    switch (it.t) {
      case 'title': {
        const runs = [];
        if (it.tag) runs.push({ text: it.tag + '  ', options: { color: COL.MAROON, bold: true } });
        runs.push(...textRuns(it.runs, { bold: true, color: COL.BLUE }));
        slide.addText(runs, { placeholder: 'title' });
        break;
      }
      case 'text': {
        const size = PT(it.size);
        const wide = it.role === 'emph';
        const coverText = s.kind !== 'content' && it.role !== 'sub';
        slide.addText(textRuns(it.runs), {
          x: wide ? X(64) : (it.align === 'center' ? x - w * 0.04 : x), y, w: coverText ? 10 - x - 0.5 : wide ? X(1312) : it.align === 'center' ? w * 1.08 : fitW(x, w), h: Math.max(h * 1.2, size / 72 * 1.5),
          fontSize: size, align: it.align === 'center' ? 'center' : it.align === 'right' ? 'right' : 'left',
          valign: 'top', margin: 0, isTextBox: true, objectName: name('text'),
          lineSpacingMultiple: it.role === 'p' ? 1.15 : 1.0,
        });
        break;
      }
      case 'list': {
        const size = PT(it.size);
        const paras = [];
        it.items.forEach((runs, k) => {
          runs.forEach((r, j) => {
            const o = runOpts(r);
            if (j === 0) o.bullet = it.ordered ? { type: 'number', indent: size * 1.3 } : { indent: size * 1.1 };
            if (j === runs.length - 1 && k < it.items.length - 1) o.breakLine = true;
            if (j === 0) o.paraSpaceAfter = Math.round(size * 0.35);
            paras.push({ text: r.text, options: o });
          });
        });
        slide.addText(paras, { x, y, w: fitW(x, w), h: h * 1.15, fontSize: size, valign: 'top', margin: 0, isTextBox: true,
          lineSpacingMultiple: 1.1, objectName: name('list') });
        break;
      }
      case 'table': {
        const size = PT(it.size);
        const rows = it.rows.map(r => r.map(c => ({
          text: c.runs.length ? textRuns(c.runs, c.head ? { color: COL.BLUE, bold: true } : {}) : '',
          options: { fill: { color: c.head ? COL.PALE : 'FFFFFF' }, valign: 'middle' },
        })));
        slide.addTable(rows, { x, y, w, colW: it.cw.map(X), rowH: it.rh.map(X), fontSize: size, fontFace: FONT,
          border: { type: 'solid', pt: 0.75, color: COL.LINE }, margin: [2, 5, 2, 5], objectName: name('table') });
        break;
      }
      case 'img':
        slide.addImage({ path: it.src, x, y, w, h, objectName: name('figure'), altText: path.basename(it.src) });
        break;
      case 'snap': case 'snapmath':
        slide.addImage({ path: it.file, x, y, w, h, objectName: name(it.t === 'snap' ? 'diagram' : 'equation') });
        break;
      case 'video': {
        const cover = 'image/jpeg;base64,' + fs.readFileSync(it.poster).toString('base64');
        slide.addMedia({ type: 'video', path: it.src, x, y, w, h, cover, objectName: name('video') });
        break;
      }
      case 'ph': {
        slide.addShape(pres.shapes.ROUNDED_RECTANGLE, { x, y, w, h, rectRadius: 0.08,
          fill: { color: 'FAFAFA' }, line: { color: it.color, width: 1.5, dashType: 'dash' }, objectName: name('placeholder-box') });
        const size = PT(it.size);
        const paras = it.lines.map((t, k) => ({ text: t, options: { bold: k === 0, color: k === 0 ? it.color : '333333',
          fontSize: k === 0 ? size * 1.1 : size, breakLine: k < it.lines.length - 1, paraSpaceAfter: 4 } }));
        slide.addText(paras, { x: x + 0.2, y: y + 0.15, w: w - 0.4, h: h - 0.3, valign: 'middle', margin: 0, isTextBox: true,
          objectName: name('placeholder-text') });
        break;
      }
      case 'code':
        slide.addText(it.text, { x, y, w, h: h * 1.1, fontFace: MONO, fontSize: PT(it.size) * 0.95, color: '222222',
          fill: { color: 'F4F5F7' }, margin: [6, 8, 6, 8], valign: 'middle', isTextBox: true, objectName: name('code') });
        break;
      case 'bar':
        slide.addShape(pres.shapes.RECTANGLE, { x, y, w, h, fill: { color: it.color }, line: { color: it.color, width: 0 }, objectName: name('accent') });
        break;
    }
  }
  if (s.notes) slide.addNotes(s.notes);
});

(async () => {
  await pres.writeFile({ fileName: OUT });
  if (applyTheme) await applyTheme(OUT, THEME);
  console.log('wrote', OUT);
})();
