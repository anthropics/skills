#!/usr/bin/env node
// Telemetry helper for site-analysis-analyst skill.
// Run from the root of the repo you want to analyze.

const fs = require('fs');
const path = require('path');

function readJSON(filePath) {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch {
    return null;
  }
}

function readText(filePath) {
  try {
    return fs.readFileSync(filePath, 'utf8').trim();
  } catch {
    return null;
  }
}

const cwd = process.cwd();

const pkg = readJSON(path.join(cwd, 'package.json'));
const railway = readJSON(path.join(cwd, 'railway.json'));
const procfile = readText(path.join(cwd, 'Procfile'));
const deployMd = readText(path.join(cwd, 'DEPLOY.md'));

const output = {
  package: pkg
    ? {
        name: pkg.name,
        version: pkg.version,
        description: pkg.description,
        engines: pkg.engines || null,
        scripts: pkg.scripts || {},
        dependencies: pkg.dependencies || {},
        devDependencies: pkg.devDependencies || {},
      }
    : null,
  infrastructure: {
    railway: railway,
    procfile: procfile,
    deployMd: deployMd,
  },
};

process.stdout.write(JSON.stringify(output, null, 2) + '\n');
