#!/usr/bin/env node

/**
 * Universal Playwright script runner for generate-screenshot skill.
 *
 * Usage:
 *   node run.js script.js          - Execute from file
 *   node run.js 'inline code'      - Execute inline Playwright code
 *   cat script.js | node run.js    - Execute from stdin
 */

const { execFileSync } = require('child_process');
const fs = require('fs');
const path = require('path');

function ensurePlaywright() {
  try {
    require.resolve('playwright');
    return true;
  } catch {
    console.log('Playwright not found. Installing...');
    execFileSync('npm', ['install'], { cwd: __dirname, stdio: 'inherit' });
    console.log('Installing Chromium browser...');
    execFileSync('npx', ['playwright', 'install', 'chromium'], { cwd: __dirname, stdio: 'inherit' });
    return true;
  }
}

function getCode() {
  const arg = process.argv[2];

  // From file
  if (arg && fs.existsSync(arg)) {
    return { code: fs.readFileSync(arg, 'utf-8'), source: arg };
  }

  // Inline code
  if (arg) {
    return { code: arg, source: 'inline' };
  }

  // From stdin
  if (!process.stdin.isTTY) {
    return {
      code: fs.readFileSync('/dev/stdin', 'utf-8'),
      source: 'stdin',
    };
  }

  console.error('Usage: node run.js <script.js | "inline code">');
  process.exit(1);
}

function needsWrapping(code) {
  return !code.includes('require(') && !code.includes('import ');
}

function wrapCode(code) {
  const helpersPath = path.join(__dirname, 'lib', 'helpers').replace(/\\/g, '\\\\');
  return `
const { chromium, firefox, webkit, devices } = require('playwright');
const helpers = require('${helpersPath}');

(async () => {
  ${code}
})().catch(err => {
  console.error('Script error:', err.message);
  process.exit(1);
});
`;
}

async function main() {
  ensurePlaywright();

  const { code, source } = getCode();
  console.log(`Running script from: ${source}`);

  const finalCode = needsWrapping(code) ? wrapCode(code) : code;

  // Write to a temporary file for execution
  const tmpFile = path.join('/tmp', `generate-screenshot-exec-${Date.now()}.js`);
  fs.writeFileSync(tmpFile, finalCode);

  try {
    execFileSync('node', [tmpFile], {
      stdio: 'inherit',
      env: { ...process.env, NODE_PATH: path.join(__dirname, 'node_modules') },
    });
  } finally {
    // Clean up execution file
    try { fs.unlinkSync(tmpFile); } catch { /* ignore */ }
  }
}

main();
