#!/usr/bin/env node
import fs from 'fs/promises';
import path from 'path';
import { spawn } from 'child_process';
import { fileURLToPath } from 'url';
import { renderHtmlDeck } from './render_html_deck.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const SKILL_ROOT = path.resolve(__dirname, '..');
const DEFAULT_INPUT = path.resolve(SKILL_ROOT, 'output', 'ppt_outline_cn.json');
const DEFAULT_OUT_DIR = path.resolve(SKILL_ROOT, 'output', 'final_deck_html');
const VERIFY_DECK_PATH = path.resolve(__dirname, 'verify_deck_html.mjs');

function usage() {
  return [
    'Usage:',
    '  node scripts/build_deck.mjs [input.json] [output-dir] [--out-dir dir] [--html-dir dir] [--style style-id]',
    '',
    'Output is always an HTML deck directory. PPTX/PDF output paths are rejected.'
  ].join('\n');
}

function parseArgs() {
  const positional = [];
  let outDirArg = null;
  let styleArg = null;
  const args = process.argv.slice(2);

  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    if (arg === '--out-dir' || arg === '--html-dir') {
      outDirArg = args[i + 1];
      i += 1;
    } else if (arg === '--style') {
      styleArg = args[i + 1];
      i += 1;
    } else if (arg === '--help' || arg === '-h') {
      console.log(usage());
      process.exit(0);
    } else {
      positional.push(arg);
    }
  }

  const [inputArg, outputArg] = positional;
  const outDir = path.resolve(outDirArg || outputArg || DEFAULT_OUT_DIR);
  const ext = path.extname(outDir).toLowerCase();
  if (ext === '.pptx' || ext === '.pdf') {
    throw new Error(
      'PPTX/PDF output has been removed from materials-html-deck. Pass an HTML output directory instead.'
    );
  }

  return {
    input: path.resolve(inputArg || DEFAULT_INPUT),
    outDir,
    style: styleArg
  };
}

async function readOutline(inputPath) {
  const raw = await fs.readFile(inputPath, 'utf8');
  return JSON.parse(raw.replace(/^\uFEFF/, ''));
}

function runVerifier(outDir) {
  return new Promise((resolve, reject) => {
    const child = spawn(
      process.execPath,
      [
        VERIFY_DECK_PATH,
        '--html-dir',
        outDir,
        '--screenshots',
        path.join(outDir, 'screenshots'),
        '--report-json',
        path.join(outDir, 'qa_report.json'),
        '--report-md',
        path.join(outDir, 'qa_report.md')
      ],
      {
        cwd: SKILL_ROOT,
        stdio: 'inherit'
      }
    );
    child.on('error', reject);
    child.on('close', (code) => {
      if (code === 0) resolve();
      else reject(new Error(`verify_deck_html.mjs failed with exit code ${code}`));
    });
  });
}

async function main() {
  try {
    const options = parseArgs();
    const outline = await readOutline(options.input);
    const result = await renderHtmlDeck({
      outline,
      inputPath: options.input,
      outDir: options.outDir,
      styleArg: options.style
    });
    await runVerifier(options.outDir);
    console.log(`HTML deck generated: ${result.indexPath}`);
    console.log(`Slides: ${result.slideCount}`);
    console.log(`QA report: ${path.join(options.outDir, 'qa_report.md')}`);
  } catch (error) {
    console.error(error.message);
    if (String(error.message || '').includes('PPTX/PDF')) {
      console.error(usage());
    }
    process.exit(1);
  }
}

main();
