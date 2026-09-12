#!/usr/bin/env node
// Simple deterministic SVG generator for algorithmic-art examples
// Usage: node generator_simple.js --seed=42 --size=800 --count=200 > out.svg

function parseArgs() {
  const args = {};
  for (const a of process.argv.slice(2)) {
    const m = a.match(/^--([a-zA-Z0-9_-]+)=(.*)$/);
    if (m) args[m[1]] = m[2];
  }
  return args;
}

// Mulberry32 PRNG for deterministic output
function mulberry32(a) {
  return function() {
    let t = a += 0x6D2B79F5;
    t = Math.imul(t ^ t >>> 15, t | 1);
    t ^= t + Math.imul(t ^ t >>> 7, t | 61);
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  };
}

function pickPalette(seed) {
  const palettes = [
    ['#d97757','#6a9bcc','#788c5d','#b0aea5','#f1e9e1'],
    ['#0f172a','#0369a1','#06b6d4','#7c3aed','#f8fafc'],
    ['#f97316','#fb923c','#fca5a5','#fde68a','#111827']
  ];
  return palettes[Math.abs(seed) % palettes.length];
}

function generateSVG({seed, size, count}) {
  const rnd = mulberry32(seed >>> 0);
  const palette = pickPalette(seed);
  const cx = size / 2, cy = size / 2;
  const minR = Math.max(2, Math.floor(size * 0.01));
  const maxR = Math.max(6, Math.floor(size * 0.05));

  const out = [];
  out.push('<?xml version="1.0" encoding="UTF-8"?>');
  out.push(`<svg xmlns="http://www.w3.org/2000/svg" width="${size}" height="${size}" viewBox="0 0 ${size} ${size}">`);
  out.push(`<rect width="100%" height="100%" fill="${palette[4] || '#ffffff'}"/>`);

  for (let i = 0; i < count; i++) {
    const a = rnd() * Math.PI * 2;
    const r = (0.05 + rnd() * 0.95) * (size * 0.45);
    const x = cx + Math.cos(a) * r + (rnd() - 0.5) * size * 0.02;
    const y = cy + Math.sin(a) * r + (rnd() - 0.5) * size * 0.02;
    const rr = Math.floor(minR + rnd() * (maxR - minR));
    const color = palette[Math.floor(rnd() * palette.length)];
    const opacity = (0.5 + rnd() * 0.5).toFixed(2);
    out.push(`<circle cx="${x.toFixed(2)}" cy="${y.toFixed(2)}" r="${rr}" fill="${color}" fill-opacity="${opacity}"/>`);
  }

  out.push('</svg>');
  return out.join('\n');
}

function main() {
  const args = parseArgs();
  const seed = parseInt(args.seed || process.env.SEED || '42', 10) || 42;
  const size = parseInt(args.size || '800', 10) || 800;
  const count = parseInt(args.count || '200', 10) || 200;
  const svg = generateSVG({seed, size, count});
  process.stdout.write(svg);
}

if (require.main === module) main();
