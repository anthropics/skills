#!/usr/bin/env node
/**
 * Skill Validator - Validates a skill directory structure and SKILL.md frontmatter
 *
 * Usage:
 *   validate.js <skill-directory>
 *
 * Example:
 *   validate.js ~/.claude/skills/my-skill
 */

import fs from 'fs';
import path from 'path';

// All frontmatter fields officially supported by Claude Code
const ALLOWED_FIELDS = new Set([
  'name',
  'description',
  'argument-hint',
  'disable-model-invocation',
  'user-invocable',
  'allowed-tools',
  'model',
  'context',
  'agent',
  'hooks',
  'license',
  'metadata',
  'compatibility',
]);

function parseFrontmatter(content) {
  if (!content.startsWith('---')) {
    return { error: 'No YAML frontmatter found (must start with ---)' };
  }

  const endIndex = content.indexOf('\n---', 3);
  if (endIndex === -1) {
    return { error: 'Invalid frontmatter format (missing closing ---)' };
  }

  const yaml = content.slice(4, endIndex).trim();
  const fields = {};
  let currentKey = null;

  for (const line of yaml.split('\n')) {
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith('#')) continue;

    // Indented line = continuation of multi-line value
    if (line.startsWith(' ') || line.startsWith('\t')) {
      if (currentKey) {
        fields[currentKey] += ' ' + trimmed;
      }
      continue;
    }

    const colonIndex = trimmed.indexOf(':');
    if (colonIndex === -1) continue;

    const key = trimmed.slice(0, colonIndex).trim();
    let value = trimmed.slice(colonIndex + 1).trim();

    // Strip YAML multi-line indicators (>-, >, |-, |)
    if (/^[>|]-?$/.test(value)) {
      value = '';
    }

    currentKey = key;
    fields[key] = value;
  }

  return { fields };
}

export function validateSkill(skillPath) {
  const resolvedPath = path.resolve(skillPath);

  // Check directory exists
  if (!fs.existsSync(resolvedPath)) {
    return { valid: false, message: `Directory not found: ${resolvedPath}` };
  }

  if (!fs.statSync(resolvedPath).isDirectory()) {
    return { valid: false, message: `Not a directory: ${resolvedPath}` };
  }

  // Check SKILL.md exists
  const skillMd = path.join(resolvedPath, 'SKILL.md');
  if (!fs.existsSync(skillMd)) {
    return { valid: false, message: 'SKILL.md not found' };
  }

  const content = fs.readFileSync(skillMd, 'utf-8');

  // Parse frontmatter
  const { fields, error } = parseFrontmatter(content);
  if (error) {
    return { valid: false, message: error };
  }

  // Check required fields
  if (!fields.name) {
    return { valid: false, message: "Missing 'name' in frontmatter" };
  }
  if (!fields.description) {
    return { valid: false, message: "Missing 'description' in frontmatter" };
  }

  // Validate name format (kebab-case)
  const name = fields.name;
  if (!/^[a-z0-9-]+$/.test(name)) {
    return { valid: false, message: `Name '${name}' should be kebab-case (lowercase letters, digits, and hyphens only)` };
  }
  if (name.startsWith('-') || name.endsWith('-') || name.includes('--')) {
    return { valid: false, message: `Name '${name}' cannot start/end with hyphen or contain consecutive hyphens` };
  }
  if (name.length > 64) {
    return { valid: false, message: `Name is too long (${name.length} characters). Maximum is 64.` };
  }

  // Validate description
  const description = fields.description;
  if (description.includes('<') || description.includes('>')) {
    return { valid: false, message: 'Description cannot contain angle brackets (< or >)' };
  }
  if (description.length > 1024) {
    return { valid: false, message: `Description is too long (${description.length} characters). Maximum is 1024.` };
  }

  // Check for unexpected fields
  const unexpectedFields = Object.keys(fields).filter(k => !ALLOWED_FIELDS.has(k));
  if (unexpectedFields.length > 0) {
    return {
      valid: false,
      message: `Unexpected field(s) in frontmatter: ${unexpectedFields.join(', ')}. Allowed: ${[...ALLOWED_FIELDS].sort().join(', ')}`,
    };
  }

  return { valid: true, message: 'Skill is valid!' };
}

// CLI entry point
const skillPath = process.argv[2];
if (!skillPath) {
  console.error('Usage: validate.js <skill-directory>');
  process.exit(1);
}

const { valid, message } = validateSkill(skillPath);
console.log(message);
process.exit(valid ? 0 : 1);
