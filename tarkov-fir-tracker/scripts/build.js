#!/usr/bin/env node
/**
 * Build script: Embed FiR data into HTML
 */

const fs = require('fs');
const path = require('path');

const PROCESSED_DIR = path.join(__dirname, '../data/processed');
const ROOT_DIR = path.join(__dirname, '..');

// Load processed data
const firData = JSON.parse(
  fs.readFileSync(path.join(PROCESSED_DIR, 'fir-requirements.json'), 'utf8')
);

// Read HTML template
let html = fs.readFileSync(path.join(ROOT_DIR, 'index.html'), 'utf8');

// Embed data
html = html.replace('PLACEHOLDER_DATA', JSON.stringify(firData));

// Write output
fs.writeFileSync(path.join(ROOT_DIR, 'dist', 'index.html'), html);

console.log('Build complete: dist/index.html');
console.log(`Embedded ${Object.keys(firData.items).length} items`);
