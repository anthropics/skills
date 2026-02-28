#!/usr/bin/env node
/**
 * Skill Initializer - Creates a new skill from template
 *
 * Usage:
 *   init-skill.js <skill-name> [--path <output-directory>]
 *
 * Default output path: ~/zylos/.claude/skills
 *
 * Examples:
 *   init-skill.js my-new-skill
 *   init-skill.js my-api-helper --path ~/.claude/skills
 */

import fs from 'fs';
import path from 'path';
import os from 'os';

const DEFAULT_PATH = path.join(os.homedir(), 'zylos', '.claude', 'skills');

function titleCase(name) {
  return name.split('-').map(w => w.charAt(0).toUpperCase() + w.slice(1)).join(' ');
}

function generateSkillMd(name) {
  const title = titleCase(name);
  return `---
name: ${name}
description: [TODO: What this skill does. Use when <specific trigger conditions>.]
---

# ${title}

[TODO: 1-2 sentences explaining what this skill enables.]

## How to Use

[TODO: Step-by-step instructions for Claude to follow when this skill is invoked.]

## Resources

This skill includes example resource directories:

### scripts/
Executable code for tasks that require deterministic reliability.
Delete if not needed.

### references/
Documentation loaded into context as needed.
Delete if not needed.

### assets/
Files used in output (templates, images, etc.) — not loaded into context.
Delete if not needed.
`;
}

function generateExampleScript(name) {
  return `#!/usr/bin/env node
/**
 * Example helper script for ${name}
 *
 * Replace with actual implementation or delete if not needed.
 */

function main() {
  console.log('This is an example script for ${name}');
  // TODO: Add actual script logic here
}

main();
`;
}

function generateExampleReference(name) {
  const title = titleCase(name);
  return `# Reference Documentation for ${title}

This is a placeholder for detailed reference documentation.
Replace with actual reference content or delete if not needed.

Reference docs are ideal for:
- Comprehensive API documentation
- Detailed workflow guides
- Complex multi-step processes
- Information too lengthy for main SKILL.md
- Content that's only needed for specific use cases
`;
}

function initSkill(skillName, outputPath) {
  const skillDir = path.resolve(outputPath, skillName);

  // Check if directory already exists
  if (fs.existsSync(skillDir)) {
    console.error(`Error: Skill directory already exists: ${skillDir}`);
    return null;
  }

  // Create skill directory
  fs.mkdirSync(skillDir, { recursive: true });
  console.log(`Created skill directory: ${skillDir}`);

  // Create SKILL.md
  fs.writeFileSync(path.join(skillDir, 'SKILL.md'), generateSkillMd(skillName));
  console.log('Created SKILL.md');

  // Create scripts/ with example
  const scriptsDir = path.join(skillDir, 'scripts');
  fs.mkdirSync(scriptsDir);
  const exampleScript = path.join(scriptsDir, 'example.js');
  fs.writeFileSync(exampleScript, generateExampleScript(skillName));
  fs.chmodSync(exampleScript, 0o755);
  console.log('Created scripts/example.js');

  // Create references/ with example
  const refsDir = path.join(skillDir, 'references');
  fs.mkdirSync(refsDir);
  fs.writeFileSync(path.join(refsDir, 'api-reference.md'), generateExampleReference(skillName));
  console.log('Created references/api-reference.md');

  // Create assets/ with placeholder
  const assetsDir = path.join(skillDir, 'assets');
  fs.mkdirSync(assetsDir);
  fs.writeFileSync(path.join(assetsDir, '.gitkeep'), '');
  console.log('Created assets/');

  console.log(`\nSkill '${skillName}' initialized at ${skillDir}`);
  console.log('\nNext steps:');
  console.log('1. Edit SKILL.md — complete the TODO items and update the description');
  console.log('2. Customize or delete the example files in scripts/, references/, and assets/');
  console.log('3. Run validate.js to check the skill structure');

  return skillDir;
}

// CLI entry point
const args = process.argv.slice(2);

if (args.length === 0) {
  console.error('Usage: init-skill.js <skill-name> [--path <output-directory>]');
  console.error(`\nDefault path: ${DEFAULT_PATH}`);
  console.error('\nExamples:');
  console.error('  init-skill.js my-new-skill');
  console.error('  init-skill.js my-api-helper --path ~/.claude/skills');
  process.exit(1);
}

const skillName = args[0];
const pathIndex = args.indexOf('--path');
const outputPath = pathIndex !== -1 && args[pathIndex + 1]
  ? args[pathIndex + 1].replace(/^~/, os.homedir())
  : DEFAULT_PATH;

console.log(`Initializing skill: ${skillName}`);
console.log(`Location: ${outputPath}\n`);

const result = initSkill(skillName, outputPath);
process.exit(result ? 0 : 1);
