#!/usr/bin/env node
import { cp, mkdir, readFile, readdir, stat, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { dirname, extname, join, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const skillRoot = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const qualityGateName = 'Vibe Gate';
const registry = JSON.parse(await readFile(join(skillRoot, 'registry.json'), 'utf8'));
const openDesignResource = await loadJsonIfExists(join(skillRoot, 'resource', 'open-design-systems.json'), null);
const templateRecipes = await loadJsonIfExists(join(skillRoot, 'resource', 'open-design-template-recipes.json'), { templates: [] });
const uiAntiPatterns = await loadJsonIfExists(join(skillRoot, 'resource', 'ui-anti-patterns.json'), { patterns: [] });
const antiPatternById = new Map((uiAntiPatterns.patterns || []).map((pattern) => [pattern.id, pattern]));
const builtInDesigns = registry.designs.map((design) => ({
  ...design,
  source: 'built-in',
  namespacedId: design.id,
  displayId: design.id,
  searchText: [
    design.id,
    design.name,
    design.sourceId,
    design.description,
    ...(design.categories || []),
    ...(design.bestFor || []),
    ...(design.style || []),
    ...(design.keywords || []),
    ...(design.pageTypes || []),
  ].join(' '),
}));
const openDesigns = (openDesignResource?.systems || []).map((system) => ({
  id: system.namespacedId,
  namespacedId: system.namespacedId,
  displayId: system.namespacedId,
  source: 'open-design',
  sourceId: system.id,
  name: system.name,
  description: system.description,
  categories: [system.category, ...(system.keywords || [])].filter(Boolean),
  bestFor: inferBestFor(system),
  avoidFor: [],
  style: system.keywords || [],
  keywords: [system.id, system.name, system.title, system.category, system.description, ...(system.keywords || [])].filter(Boolean),
  pageTypes: inferPageTypes(system),
  tailwindReady: true,
  difficulty: 'medium',
  disclaimer: 'Vibe UI bundled upstream resource. Inspired by publicly visible UI patterns; not an official brand design system.',
  body: system.body,
  sourcePath: system.sourcePath,
  swatches: system.swatches || [],
  repo: openDesignResource.source.repo,
  commit: openDesignResource.source.commit,
  searchText: [
    system.id,
    system.namespacedId,
    system.name,
    system.title,
    system.category,
    system.description,
    ...(system.keywords || []),
    system.body,
  ].join(' '),
}));
const designs = [...builtInDesigns, ...openDesigns];
const aliases = new Map([
  ['linear.app', 'linear'],
  ['openai', 'openai'],
  ['claude', 'openai'],
]);

const usage = `Usage:
  node scripts/design.mjs list [--source built-in|open-design|all]
  node scripts/design.mjs search <keyword> [--source built-in|open-design|all]
  node scripts/design.mjs recommend <user_goal> [--source built-in|open-design|all]
  node scripts/design.mjs use <design_id>
  node scripts/design.mjs like <design_id> [page_type] [--strength light|medium|bold]
  node scripts/design.mjs remix <primary_design_id> <secondary_design_id> [goal]
  node scripts/design.mjs workflow <page_type> [--design design_id] [--template template_id] [--target file_or_directory]
  node scripts/design.mjs template <template_id>
  node scripts/design.mjs generate <page_type> [--template template_id]
  node scripts/design.mjs invariants <design_id>
  node scripts/design.mjs brief-check <page_type> [--design design_id] [--template template_id]
  node scripts/design.mjs check <file_or_directory>
  node scripts/design.mjs preview [--source built-in|open-design|all] [--out directory]
  node scripts/design.mjs browse [--source built-in|open-design|all] [--out directory]
  node scripts/design.mjs submit <design_id> <DESIGN.md> [--name display_name]
  node scripts/design.mjs extract-url <url_or_html_file> [--out DESIGN.md]
  node scripts/design.mjs import <figma_or_screenshot_notes> [--kind figma|screenshot] [--out DESIGN.md]
  node scripts/design.mjs report <file_or_directory> [--out DESIGN-REPORT.md]`;

const command = process.argv[2];
const args = process.argv.slice(3);

try {
  if (!command || command === 'help' || command === '--help' || command === '-h') {
    console.log(usage);
  } else if (command === 'list') {
    listDesigns(args);
  } else if (command === 'search') {
    searchDesigns(args);
  } else if (command === 'recommend') {
    recommendDesigns(args);
  } else if (command === 'use') {
    await useDesign(args[0]);
  } else if (command === 'like') {
    likeStyle(args);
  } else if (command === 'remix') {
    remixStyles(args[0], args[1], args.slice(2).join(' '));
  } else if (command === 'workflow') {
    await showWorkflow(args);
  } else if (command === 'template') {
    showTemplate(args[0]);
  } else if (command === 'generate') {
    await generatePrompt(args);
  } else if (command === 'invariants') {
    showInvariants(args[0]);
  } else if (command === 'brief-check') {
    await showBriefCheck(args);
  } else if (command === 'check') {
    await checkDesign(args[0]);
  } else if (command === 'preview') {
    await generatePreview(args);
  } else if (command === 'browse') {
    await generateBrowser(args);
  } else if (command === 'submit') {
    await submitDesign(args);
  } else if (command === 'extract-url') {
    await extractUrlDesign(args);
  } else if (command === 'import') {
    await importVisualReference(args);
  } else if (command === 'report') {
    await writeDesignReport(args);
  } else {
    fail(`Unknown command: ${command}\n\n${usage}`);
  }
} catch (error) {
  fail(error instanceof Error ? error.message : String(error));
}

async function loadJsonIfExists(path, fallback) {
  if (!existsSync(path)) return fallback;
  return JSON.parse(await readFile(path, 'utf8'));
}

function listDesigns(rawArgs = []) {
  const { flags } = parseArgs(rawArgs);
  const source = normalizeSource(flags.source);
  const list = filterBySource(designs, source);
  console.log(`Available DESIGN.md styles (${source}):\n`);
  for (const design of list) {
    const tags = unique([...(design.categories || []), ...(design.pageTypes || []), ...(design.style || [])]).slice(0, 8).join(', ');
    console.log(`- ${design.displayId}: ${tags}`);
  }
  console.log('\nUse `node scripts/design.mjs recommend "<goal>"` if you want help choosing.');
}

function searchDesigns(rawArgs) {
  const { positional, flags } = parseArgs(rawArgs);
  const query = positional.join(' ');
  if (!query.trim()) fail('Search requires a keyword.');
  const source = normalizeSource(flags.source);
  const matches = rankDesigns(query, source).filter((item) => item.score > 0).slice(0, 10);
  if (!matches.length) {
    console.log(`No matching DESIGN.md styles found for: ${query}`);
    return;
  }

  console.log(`Search results for "${query}" (${source}):\n`);
  for (const { design, reasons } of matches) {
    console.log(`- ${design.displayId}: ${(design.categories || []).join(', ')}`);
    console.log(`  Source: ${design.source}`);
    console.log(`  ${design.description}`);
    console.log(`  Match: ${reasons.slice(0, 3).join('; ')}`);
  }
}

function recommendDesigns(rawArgs) {
  const { positional, flags } = parseArgs(rawArgs);
  const goal = positional.join(' ');
  if (!goal.trim()) fail('Recommend requires a natural-language user goal.');
  const source = normalizeSource(flags.source);
  const enrichedGoal = enrichGoal(goal);
  const sourceDesigns = filterBySource(designs, source);
  const matches = rankDesigns(enrichedGoal, source)
    .filter((item) => item.score > 0)
    .slice(0, 3);
  const recommendations = matches.length ? matches : sourceDesigns.slice(0, 3).map((design) => ({
    design,
    reasons: ['strong general-purpose page-generation coverage'],
    score: 1,
  }));

  console.log(`Recommended styles (${source}):\n`);
  recommendations.forEach(({ design, reasons }, index) => {
    console.log(`${index + 1}. ${design.displayId}`);
    console.log(`   Source: ${design.source}`);
    console.log(`   Reason: ${reasonFor(design, goal, reasons)}\n`);
  });
  const [primary, secondary] = recommendations.map(({ design }) => design.displayId);
  console.log(`Default recommendation: ${primary}${secondary ? ` + ${secondary}-inspired layout discipline` : ''}.`);
  if (recommendations.some(({ design }) => design.region === 'china')) {
    console.log('Regional note: Chinese product-inspired styles are inspired by publicly visible domestic UI patterns. Not affiliated with or endorsed by the referenced product/company.');
  }
}

async function useDesign(id) {
  const design = findDesign(id);
  const cwd = process.cwd();
  const target = join(cwd, 'DESIGN.md');
  const stateDir = join(cwd, '.vibe-ui');
  const statePath = join(stateDir, 'current-design.json');
  await mkdir(stateDir, { recursive: true });

  if (design.source === 'open-design') {
    await writeFile(target, design.body);
  } else {
    const source = designSourcePath(design);
    if (!existsSync(source)) fail(`DESIGN.md source not found for ${design.id}: ${relative(skillRoot, source)}`);
    await cp(source, target);
  }

  await writeFile(join(cwd, 'DESIGN.generated.md'), buildGeneratedDesignMd(design));
  await writeFile(statePath, `${JSON.stringify({
    id: design.displayId,
    name: design.name,
    source: design.source,
    sourceId: design.sourceId,
    version: registry.version,
    commit: design.commit,
    repo: design.repo,
    sourcePath: design.sourcePath,
    appliedAt: new Date().toISOString(),
    disclaimer: design.disclaimer,
  }, null, 2)}\n`);

  console.log(`Applied design: ${design.displayId}\n`);
  console.log('Created:');
  console.log('- DESIGN.md');
  console.log('- DESIGN.generated.md');
  console.log('- .vibe-ui/current-design.json\n');
  console.log('Next:');
  console.log('"Build this page following DESIGN.md strictly. Do not invent unrelated colors, shadows, or gradients."');
}

function remixStyles(primaryId, secondaryId, goal = '') {
  const primary = findDesign(primaryId);
  const secondary = findDesign(secondaryId);
  if (primary.displayId === secondary.displayId) fail('Remix requires two different design styles.');

  console.log('Style remix prototype:\n');
  console.log(`Primary style: ${primary.displayId} - ${primary.description}`);
  console.log(`Secondary style: ${secondary.displayId} - ${secondary.description}`);
  if (goal.trim()) console.log(`Goal: ${goal.trim()}`);
  console.log('\nBlend plan:');
  console.log(`- Use ${primary.displayId} for layout rhythm, typography hierarchy, spacing density, and base component structure.`);
  console.log(`- Use ${secondary.displayId} for localized content tone, secondary component cues, and selected interaction patterns.`);
  console.log("- Keep one source of truth for colors: start from the primary DESIGN.md and borrow secondary accents only when explicitly documented.");
  console.log("- Do not average colors, mix unrelated gradients, or stack both systems' shadows/radii.");
  console.log('\nPrompt:');
  console.log(`Build using ${primary.displayId} as the primary DESIGN.md style, then selectively borrow ${secondary.displayId} cues for the stated goal. Preserve token discipline and explain any borrowed cue in comments or a short implementation note.`);
}

function likeStyle(rawArgs) {
  const { positional, flags } = parseArgs(rawArgs);
  const design = findDesign(positional[0]);
  const pageType = positional[1] || 'landing';
  if (!supportedPageTypes().includes(pageType)) {
    fail(`Unsupported page type: ${pageType}\nSupported page types: ${supportedPageTypes().join(', ')}`);
  }
  const strength = flags.strength || 'medium';
  if (!['light', 'medium', 'bold'].includes(strength)) {
    fail('Unsupported strength. Use one of: light, medium, bold.');
  }

  const label = styleLabel(design);
  const recipe = pageRecipe(pageType);
  const intensity = strengthGuidance(strength);

  console.log('Like-style prompt:\n');
  console.log(`Style: ${design.displayId}`);
  console.log(`Page type: ${pageType}`);
  console.log(`Strength: ${strength}`);
  console.log(`Source: ${design.sourceId}`);
  console.log(`${design.disclaimer}\n`);
  console.log(`Build a ${pageType} page with a ${label} visual direction. This is not a pixel-perfect clone and not pixel-perfect replication; use the style as inspiration for hierarchy, rhythm, density, and mood.\n`);
  console.log('Style direction:');
  console.log(`- ${intensity}`);
  console.log(`- Preserve the product category fit: ${(design.bestFor || []).slice(0, 4).join(', ')}.`);
  console.log(`- Use visual cues from ${(design.style || []).slice(0, 5).join(', ')} without copying proprietary assets.`);
  console.log('- Keep one coherent system for colors, radius, shadows, spacing, and typography.\n');
  console.log('Page recipe:');
  recipe.forEach((item) => console.log(`- ${item}`));
  console.log('\nGuardrails:');
  console.log('- Do not copy logos, trademarks, proprietary assets, or official brand claims.');
  console.log('- Do not claim affiliation with or endorsement by the referenced product/company.');
  console.log('- Avoid overfitting the reference; make the page feel native to the current product.');
  console.log('- Prefer polished composition over exhaustive brand replication.');
}

function showTemplate(id) {
  const template = findTemplate(id);
  console.log(`Vibe UI template recipe: ${template.id}\n`);
  console.log(`${template.name}`);
  console.log(`${template.description}\n`);
  console.log('Required sections:');
  template.requiredSections.forEach((section) => console.log(`- ${section}`));
  console.log('\nLayout notes:');
  template.layoutNotes.forEach((note) => console.log(`- ${note}`));
  console.log('\nP0 self-check:');
  template.p0SelfCheck.forEach((item) => console.log(`- ${item}`));
}

async function showWorkflow(rawArgs) {
  const { positional, flags } = parseArgs(rawArgs);
  const pageType = positional[0] || 'landing';
  if (!supportedPageTypes().includes(pageType)) {
    fail(`Unsupported page type: ${pageType}\nSupported page types: ${supportedPageTypes().join(', ')}`);
  }
  const current = flags.design ? null : await loadCurrentDesign();
  const designId = flags.design || current?.id || '<design_id>';
  const template = flags.template ? findTemplate(flags.template) : null;
  const target = flags.target || '<file_or_directory>';
  const sourceHint = flags.design || current ? `--design ${designId}` : '--design <design_id>';

  console.log(`Vibe UI workflow for ${pageType}\n`);
  console.log(`${qualityGateName}: default quality gate for visual work.`);
  console.log('Run these steps in order:\n');
  console.log(`Step 1. Select or confirm the design source`);
  console.log(`- ${current || flags.design ? `node scripts/design.mjs use ${designId}` : 'node scripts/design.mjs recommend "<user goal>" --source all'}`);
  console.log(`Step 2. Lock ${qualityGateName} invariants`);
  console.log(`- node scripts/design.mjs invariants ${designId}`);
  console.log(`Step 3. Write the execution contract`);
  console.log(`- node scripts/design.mjs brief-check ${pageType} ${sourceHint}${template ? ` --template ${template.id}` : ''}`);
  console.log(`Step 4. Generate the build prompt`);
  console.log(`- node scripts/design.mjs generate ${pageType}${template ? ` --template ${template.id}` : ''}`);
  console.log('Step 5. Review implementation output');
  console.log(`- node scripts/design.mjs report ${target}`);
  console.log('\nReady rule: ship only when the report decision is Ready, or when every blocking issue has a documented follow-up.');
}

function showInvariants(id) {
  const design = findDesign(id);
  const swatches = design.swatches?.length ? design.swatches.slice(0, 6) : [previewAccent(design)];
  const cues = unique([
    ...(design.categories || []),
    ...(design.bestFor || []),
    ...(design.style || []),
    ...(design.pageTypes || []),
  ]).slice(0, 10);

  console.log(`${qualityGateName} invariants for ${design.displayId}\n`);
  console.log(`Source: ${design.source}`);
  console.log(`Reference: ${design.sourceId}`);
  if (design.repo) console.log(`Repository: ${design.repo}`);
  if (design.sourcePath) console.log(`Source path: ${design.sourcePath}`);
  console.log(`${design.disclaimer}\n`);

  console.log('Must preserve:');
  console.log('- Treat the selected DESIGN.md as the source of truth for palette, type, spacing, radius, shadows, density, and component rhythm.');
  console.log(`- Keep the page aligned with these cues: ${cues.join(', ') || 'selected style evidence'}.`);
  console.log(`- Use only documented or extracted palette evidence first: ${swatches.join(', ')}.`);
  console.log('- Make top-level sections and major generated blocks easy to review with stable data-od-id values.');
  console.log('- Keep content specific to the real product and page goal.\n');

  console.log('Do not:');
  console.log('- Do not copy logos, trademarks, proprietary assets, screenshots, or official brand claims from the reference.');
  console.log('- Do not add default LLM indigo, arbitrary gradients, emoji icons, invented metrics, filler copy, heavy shadows, or radius drift unless DESIGN.md explicitly permits them.');
  console.log('- Do not average multiple design systems into one mixed palette.');
  if (isDarkDesign(design)) console.log('- Do not invert the reference into a generic light SaaS layout unless the user asks for that change.');
  console.log('- Do not use the inspiration as a pixel-perfect clone target.\n');

  console.log('P0 self-check:');
  console.log('- Every visible color, radius, shadow, and type choice can point back to DESIGN.md or the active project design system.');
  console.log('- The first viewport communicates the actual product, not generic placeholder marketing.');
  console.log('- Top-level sections have stable review identifiers where applicable.');
  console.log('- Run `node scripts/design.mjs check <file_or_directory>` or `node scripts/design.mjs report <file_or_directory>` after implementation.');
}

async function showBriefCheck(rawArgs) {
  const { positional, flags } = parseArgs(rawArgs);
  const pageType = positional[0] || 'landing';
  if (!supportedPageTypes().includes(pageType)) {
    fail(`Unsupported page type: ${pageType}\nSupported page types: ${supportedPageTypes().join(', ')}`);
  }
  const current = flags.design ? null : await loadCurrentDesign();
  const design = flags.design
    ? findDesign(flags.design)
    : current
      ? findDesign(current.id)
      : null;
  const template = flags.template ? findTemplate(flags.template) : null;
  const sections = template?.requiredSections?.length ? template.requiredSections : pageRecipe(pageType);
  const watchlist = antiPatternsForBrief(pageType, template).slice(0, 7);
  const verificationCommands = [
    'node scripts/design.mjs check <file_or_directory>',
    'node scripts/design.mjs report <file_or_directory>',
    'Inspect the rendered UI at desktop and mobile widths.',
  ];
  const contract = buildGateContract({
    pageType,
    design,
    current,
    template,
    sections,
    watchlist,
    verificationCommands,
  });
  const contractPath = await writeGateContract(contract);

  console.log(`${qualityGateName} execution contract\n`);
  console.log(`Page type: ${pageType}`);
  console.log(`Design: ${design?.displayId ?? current?.id ?? 'not selected'}`);
  console.log(`Design source: ${design?.source ?? current?.source ?? 'none'}`);
  if (template) console.log(`Template: ${template.id}`);
  console.log('');

  console.log('Materials status:');
  console.log(`- DESIGN.md: ${design ? 'selected or ready to apply' : 'missing; run use <design_id> before implementation'}`);
  console.log(`- Source provenance: ${design?.repo ? `${design.repo}${design.commit ? ` @ ${design.commit}` : ''}` : design?.sourceId ?? 'project-local or not selected'}`);
  console.log('- Logos/product screenshots: use user-provided or project-owned assets only.');
  console.log('- Claims and metrics: do not invent proof; cite real evidence or use neutral copy.\n');

  console.log('Required sections:');
  sections.forEach((section) => console.log(`- ${section}`));
  if (template?.layoutNotes?.length) {
    console.log('\nLayout notes:');
    template.layoutNotes.forEach((note) => console.log(`- ${note}`));
  }

  console.log('\nAnti-pattern watchlist:');
  watchlist.forEach((pattern) => console.log(`- ${pattern.id}: ${pattern.fix}`));

  console.log('\nVerification commands:');
  verificationCommands.forEach((command) => console.log(`- ${command}`));
  console.log('');

  console.log('P0 self-check:');
  console.log('- The design reads as one coherent system, not a collage of defaults.');
  console.log('- The output uses DESIGN.md tokens before invented colors, shadows, radii, or effects.');
  console.log('- The page has concrete product copy, accessible controls, and stable review hooks.');
  console.log(`\nWrote ${relative(process.cwd(), contractPath)}`);
}

async function generatePrompt(rawArgs) {
  const { positional, flags } = parseArgs(rawArgs);
  const pageType = positional[0] || 'landing';
  const promptPath = join(skillRoot, 'prompts', `${pageType}.md`);
  if (!existsSync(promptPath)) {
    fail(`Unsupported page type: ${pageType}\nSupported page types: ${supportedPageTypes().join(', ')}`);
  }
  const current = await loadCurrentDesign();
  const prompt = await readFile(promptPath, 'utf8');
  const selected = current ? current.id : 'none';
  const template = flags.template ? findTemplate(flags.template) : null;

  console.log(`Generate a ${pageType} page using the current DESIGN.md.\n`);
  console.log(`Selected style: ${selected}`);
  if (!current) {
    console.log('No .vibe-ui/current-design.json found. Run `node scripts/design.mjs use <design_id>` first, or ensure DESIGN.md exists.\n');
  } else {
    console.log(`Design source: ${current.name ?? current.id}`);
    console.log(`${current.disclaimer ?? 'Inspired by publicly visible UI patterns. This is not an official brand design system.'}\n`);
  }
  if (template) {
    const gateDesignId = current?.id || '<design_id>';
    console.log(`${qualityGateName} required before implementation:`);
    console.log(`- node scripts/design.mjs invariants ${gateDesignId}`);
    console.log(`- node scripts/design.mjs brief-check ${pageType} --design ${gateDesignId} --template ${template.id}`);
    console.log('');
    console.log(`Template recipe: ${template.id}`);
    console.log(`Recipe source: ${template.source}`);
    console.log('\nRequired sections:');
    template.requiredSections.forEach((section) => console.log(`- ${section}`));
    console.log('\nLayout notes:');
    template.layoutNotes.forEach((note) => console.log(`- ${note}`));
    console.log('\nP0 self-check:');
    template.p0SelfCheck.forEach((item) => console.log(`- ${item}`));
    console.log('');
  }
  console.log(prompt.trim());
}

async function checkDesign(targetArg) {
  const review = await analyzeDesign(targetArg);
  printDesignReview(review);
}

async function generatePreview(rawArgs) {
  const { flags } = parseArgs(rawArgs);
  const source = normalizeSource(flags.source);
  const outDir = resolve(process.cwd(), flags.out || 'vibe-ui-preview');
  await mkdir(outDir, { recursive: true });
  await writeFile(join(outDir, 'designs.json'), `${JSON.stringify(browserData(source), null, 2)}\n`);
  await writeFile(join(outDir, 'index.html'), buildPreviewHtml(source));
  console.log(`Generated visual preview site: ${relative(process.cwd(), join(outDir, 'index.html'))}`);
}

async function generateBrowser(rawArgs) {
  const { flags } = parseArgs(rawArgs);
  const source = normalizeSource(flags.source);
  const outDir = resolve(process.cwd(), flags.out || 'vibe-ui-browser');
  await mkdir(outDir, { recursive: true });
  await writeFile(join(outDir, 'designs.json'), `${JSON.stringify(browserData(source), null, 2)}\n`);
  await writeFile(join(outDir, 'index.html'), buildPreviewHtml(source));
  console.log(`Generated online design browser: ${relative(process.cwd(), outDir)}`);
}

async function submitDesign(rawArgs) {
  const { positional, flags } = parseArgs(rawArgs);
  const id = normalizeDesignId(positional[0]);
  const sourceArg = positional[1];
  if (!id || !sourceArg) fail('Submit requires: submit <design_id> <DESIGN.md> [--name display_name]');
  const source = resolve(process.cwd(), sourceArg);
  if (!existsSync(source)) fail(`DESIGN.md source does not exist: ${sourceArg}`);
  const text = await readFile(source, 'utf8');
  const targetDir = join(process.cwd(), '.vibe-ui', 'submissions', id);
  await mkdir(targetDir, { recursive: true });
  await writeFile(join(targetDir, 'DESIGN.md'), text);
  await writeFile(join(targetDir, 'meta.json'), `${JSON.stringify({
    id,
    name: flags.name || id,
    source: relative(process.cwd(), source),
    submittedAt: new Date().toISOString(),
    disclaimer: 'User-submitted DESIGN.md. Review rights, provenance, and brand-safety before publishing.',
  }, null, 2)}\n`);
  console.log(`Submitted design: ${id}`);
  console.log(`Created: ${relative(process.cwd(), targetDir)}/DESIGN.md`);
}

async function extractUrlDesign(rawArgs) {
  const { positional, flags } = parseArgs(rawArgs);
  const input = positional[0];
  if (!input) fail('extract-url requires a URL or local HTML file.');
  const html = await loadUrlOrFile(input);
  const outPath = resolve(process.cwd(), flags.out || 'EXTRACTED.DESIGN.md');
  await writeFile(outPath, buildExtractedDesignMd(input, html));
  console.log(`Extracted DESIGN.md from URL: ${relative(process.cwd(), outPath)}`);
}

async function importVisualReference(rawArgs) {
  const { positional, flags } = parseArgs(rawArgs);
  const sourceArg = positional[0];
  if (!sourceArg) fail('import requires a Figma export, screenshot notes file, or visual reference text file.');
  const source = resolve(process.cwd(), sourceArg);
  if (!existsSync(source)) fail(`Visual reference does not exist: ${sourceArg}`);
  const text = await readFile(source, 'utf8');
  const kind = flags.kind || inferImportKind(sourceArg);
  if (!['figma', 'screenshot'].includes(kind)) fail('Unsupported import kind. Use one of: figma, screenshot.');
  const outPath = resolve(process.cwd(), flags.out || 'IMPORTED.DESIGN.md');
  await writeFile(outPath, buildImportedDesignMd(kind, sourceArg, text));
  console.log(`Imported visual reference: ${relative(process.cwd(), outPath)}`);
}

async function writeDesignReport(rawArgs) {
  const { positional, flags } = parseArgs(rawArgs);
  const targetArg = positional[0];
  if (!targetArg) fail('report requires a file or directory.');
  const review = await analyzeDesign(targetArg);
  const outPath = resolve(process.cwd(), flags.out || 'DESIGN-REPORT.md');
  await writeFile(outPath, buildReportMarkdown(review));
  console.log(`Wrote design consistency report: ${relative(process.cwd(), outPath)}`);
}

function buildGateContract({ pageType, design, current, template, sections, watchlist, verificationCommands }) {
  return {
    schemaVersion: 'vibe-ui/vibe-gate-contract/v1',
    qualityGate: {
      name: qualityGateName,
      purpose: 'Default execution contract for Vibe UI visual work.',
    },
    pageType,
    design: design ? {
      id: design.displayId,
      source: design.source,
      sourceId: design.sourceId,
      repo: design.repo,
      commit: design.commit,
      sourcePath: design.sourcePath,
    } : {
      id: current?.id || null,
      source: current?.source || null,
    },
    template: template ? {
      id: template.id,
      pageType: template.pageType,
      source: template.source,
    } : null,
    materialsStatus: {
      designMd: design ? 'selected-or-ready' : 'missing',
      sourceProvenance: design?.repo ? `${design.repo}${design.commit ? ` @ ${design.commit}` : ''}` : design?.sourceId || 'project-local-or-not-selected',
      assets: 'use user-provided or project-owned assets only',
      claims: 'cite real evidence or use neutral copy',
    },
    requiredSections: sections,
    antiPatternWatchlist: watchlist.map((pattern) => ({
      id: pattern.id,
      category: pattern.category,
      fix: pattern.fix,
    })),
    verificationCommands,
    p0SelfCheck: [
      'The design reads as one coherent system, not a collage of defaults.',
      'The output uses DESIGN.md tokens before invented colors, shadows, radii, or effects.',
      'The page has concrete product copy, accessible controls, and stable review hooks.',
    ],
    generatedAt: new Date().toISOString(),
  };
}

async function writeGateContract(contract) {
  const stateDir = join(process.cwd(), '.vibe-ui');
  const contractPath = join(stateDir, 'vibe-gate-contract.json');
  await mkdir(stateDir, { recursive: true });
  await writeFile(contractPath, `${JSON.stringify(contract, null, 2)}\n`);
  return contractPath;
}

async function analyzeDesign(targetArg) {
  if (!targetArg) fail('Check requires a file or directory.');
  const cwd = process.cwd();
  const target = resolve(cwd, targetArg);
  if (!existsSync(target)) fail(`Target does not exist: ${targetArg}`);

  const current = await loadCurrentDesign();
  const designText = existsSync(join(cwd, 'DESIGN.md')) ? await readFile(join(cwd, 'DESIGN.md'), 'utf8') : '';
  const files = await collectFiles(target);
  const textByFile = await Promise.all(files.map(async (file) => [file, await readFile(file, 'utf8')]));
  const combined = textByFile.map(([, text]) => text).join('\n');
  const designTokens = extractDesignTokenHints(designText);
  const tokenColors = new Set(designTokens.colors.map((token) => token.value));
  const findings = {
    Color: [],
    Typography: [],
    Layout: [],
    Components: [],
    'Copy/content': [],
    'Brand safety': [],
    Accessibility: [],
  };
  const good = [];
  const patchSuggestions = [];
  const qaFindings = [];

  if (tokenColors.size && [...tokenColors].some((color) => combined.toLowerCase().includes(color.toLowerCase()))) {
    good.push('Uses at least one color value defined in DESIGN.md.');
  }
  if (/\b(text|font)-(xs|sm|base|lg|xl|2xl|3xl|4xl|5xl|6xl)\b/.test(combined) || /font-(medium|semibold|bold)/.test(combined)) {
    good.push('Contains explicit typography hierarchy classes.');
  }
  if (/\b(p|m|gap|space|px|py)-[0-9]/.test(combined)) {
    good.push('Uses a repeatable spacing scale.');
  }

  if (/\bfrom-[\w/[\]#.-]+\s+\b(to|via)-[\w/[\]#.-]+|\bbg-gradient-to-/.test(combined)) {
    addFinding(findings, 'Color', 'Uses a random gradient or unsupported gradient; only keep gradients explicitly present in DESIGN.md.');
    addQaFinding(qaFindings, 'generic-ai-gradient');
    const gradientMatch = combined.match(/\bfrom-[\w/[\]#.-]+\s+\b(?:via-[\w/[\]#.-]+\s+)?to-[\w/[\]#.-]+/);
    if (gradientMatch) {
      const primary = preferredColorToken(designTokens, ['primary', 'accent', 'link', 'brand']);
      patchSuggestions.push(`Replace \`${gradientMatch[0]}\` with a single DESIGN.md action color such as \`${primary.value}\` (${primary.name}).`);
    }
  }
  if (/#(6366f1|4f46e5|818cf8|7c3aed)\b/i.test(combined)) {
    addFinding(findings, 'Color', 'Uses an AI-default indigo/default LLM accent color; replace it with a selected DESIGN.md token.');
    addQaFinding(qaFindings, 'default-llm-indigo');
  }
  if (/\bshadow-(xl|2xl)|box-shadow:\s*[^;]*(40px|60px|80px)/i.test(combined)) {
    addFinding(findings, 'Components', 'Uses heavier shadows than most curated DESIGN.md systems allow; reduce to token-defined or subtle shadows.');
    addQaFinding(qaFindings, 'heavy-shadow');
    const shadowMatch = combined.match(/\bshadow-(xl|2xl)\b/i);
    if (shadowMatch) {
      patchSuggestions.push(`Replace \`${shadowMatch[0]}\` with \`${preferredShadow(designTokens)}\` unless DESIGN.md explicitly calls for heavy depth.`);
    }
  }
  if (/\brounded-\[[^\]]+\]|border-radius:\s*(3[2-9]|[4-9][0-9])px/i.test(combined)) {
    addFinding(findings, 'Components', 'Uses arbitrary large radius values; align radius with DESIGN.md component rules.');
    addQaFinding(qaFindings, 'radius-drift');
    const radiusMatch = combined.match(/\brounded-\[[^\]]+\]|border-radius:\s*(?:3[2-9]|[4-9][0-9])px/i);
    if (radiusMatch) {
      patchSuggestions.push(`Replace \`${radiusMatch[0]}\` with \`${preferredRadius(designTokens)}\` from the DESIGN.md radius scale.`);
    }
  }
  const hardcoded = [...combined.matchAll(/#[0-9a-fA-F]{3,8}/g)]
    .map((match) => match[0].toLowerCase())
    .filter((color) => !tokenColors.has(color));
  if (hardcoded.length) {
    addFinding(findings, 'Color', `Contains hardcoded arbitrary color values not found in DESIGN.md: ${unique(hardcoded).slice(0, 5).join(', ')}.`);
    addQaFinding(qaFindings, 'hardcoded-color', `Matched ${unique(hardcoded).slice(0, 5).join(', ')} outside DESIGN.md token candidates.`);
    const replacement = preferredColorToken(designTokens, ['primary', 'ink', 'text', 'canvas', 'surface']);
    for (const color of unique(hardcoded).slice(0, 5)) {
      patchSuggestions.push(`Replace \`${color}\` with DESIGN.md token \`${replacement.value}\` (${replacement.name}).`);
    }
  }
  if (/glassmorphism|backdrop-blur|blur-\[|neon|animate-pulse/i.test(combined)) {
    addFinding(findings, 'Components', 'Introduces visual effects that often drift from DESIGN.md unless the selected style explicitly calls for them.');
    addQaFinding(qaFindings, 'generic-ai-gradient', 'Matched generic effect language such as glass, blur, neon, or pulse.');
  }
  if (/[\u{1f000}-\u{1faff}\u{2600}-\u{27bf}]/u.test(combined)) {
    addFinding(findings, 'Brand safety', 'Uses emoji as UI ornament/iconography; replace with the project icon system or remove if DESIGN.md does not allow it.');
    addQaFinding(qaFindings, 'emoji-icon');
  }
  if (/\b(?:\d{2,}x|99(?:\.9+)?%|1m\+|100k\+|millions?|billions?)\b/i.test(combined)) {
    addFinding(findings, 'Copy/content', 'Uses an invented metric or unsupported numeric claim; replace with real evidence or neutral product copy.');
    addQaFinding(qaFindings, 'invented-metric');
  }
  if (/lorem ipsum|placeholder|your product|acme|coming soon/i.test(combined)) {
    addFinding(findings, 'Copy/content', 'Contains filler copy or placeholder content; write specific product-facing copy.');
    addQaFinding(qaFindings, 'filler-copy');
  }
  if (/text-transform:\s*uppercase|uppercase/.test(combined) && !/letter-spacing|tracking-/.test(combined)) {
    addFinding(findings, 'Typography', 'Uppercase text appears without explicit letter-spacing/tracking; add spacing or use sentence case.');
    addQaFinding(qaFindings, 'uppercase-without-letter-spacing');
  }
  if (/<section\b/i.test(combined) && !/data-od-id=/.test(combined)) {
    addFinding(findings, 'Layout', 'Sections are not labeled with data-od-id; add stable section identifiers for review and iteration.');
    addQaFinding(qaFindings, 'missing-section-id');
  }
  if (/<button\b/i.test(combined) && !/(aria-label|>\s*[^<]+\s*<\/button>)/i.test(combined)) {
    addFinding(findings, 'Accessibility', 'Button elements need visible text or aria-label for accessibility.');
    addQaFinding(qaFindings, 'unlabeled-button');
  }
  if (!/function|const|className|<header|<main|<section|export default/.test(combined)) {
    addFinding(findings, 'Layout', 'Target does not look like reusable page/component code; review component structure manually.');
    addQaFinding(qaFindings, 'weak-component-structure');
  }

  const issues = Object.values(findings).flat();
  const score = Math.max(1, Math.min(10, 10 - issues.length * 1.2 + Math.min(good.length, 2)));
  const gate = buildGateSummary(Math.round(score), qaFindings, issues, patchSuggestions);
  return {
    current,
    files,
    score: Math.round(score),
    gate,
    good,
    issues,
    findings,
    qaFindings,
    patchSuggestions,
    designTokens,
  };
}

function addFinding(findings, section, text) {
  findings[section].push(text);
}

function buildGateSummary(score, qaFindings, issues, patchSuggestions) {
  const blockingIds = new Set([
    'default-llm-indigo',
    'hardcoded-color',
    'emoji-icon',
    'invented-metric',
    'filler-copy',
    'missing-section-id',
    'unlabeled-button',
    'weak-component-structure',
  ]);
  const blocking = qaFindings.filter((finding) => blockingIds.has(finding.id));
  const decision = blocking.length || score < 8 ? 'Needs revision' : 'Ready';
  const topFixes = unique([
    ...blocking.map((finding) => finding.fix),
    ...patchSuggestions,
    ...qaFindings.map((finding) => finding.fix),
  ]).slice(0, 3);
  return {
    name: qualityGateName,
    score,
    decision,
    blocking,
    topFixes,
    issueCount: issues.length,
  };
}

function addQaFinding(qaFindings, id, evidenceOverride) {
  const pattern = antiPatternById.get(id);
  if (!pattern || qaFindings.some((finding) => finding.id === id && finding.evidence === (evidenceOverride || pattern.evidence))) return;
  qaFindings.push({
    id: pattern.id,
    category: pattern.category,
    label: pattern.label,
    bad: pattern.bad,
    fix: pattern.fix,
    evidence: evidenceOverride || pattern.evidence,
  });
}

function printDesignReview(review) {
  console.log('Design consistency review:\n');
  console.log(`Selected style: ${review.current?.id ?? 'unknown'}`);
  console.log(`Files checked: ${review.files.length}`);
  console.log(`Score: ${review.score}/10\n`);
  console.log(`${qualityGateName}: ${review.gate.decision}`);
  console.log(`Quality gate score: ${review.gate.score}/10`);
  if (review.gate.blocking.length) {
    console.log('Blocking issues:');
    review.gate.blocking.forEach((finding) => console.log(`- ${finding.id}: ${finding.fix}`));
  } else {
    console.log('Blocking issues: none detected by the static checker.');
  }
  console.log('');
  console.log('Good:');
  if (review.good.length) review.good.forEach((item) => console.log(`- ${item}`));
  else console.log('- No strong DESIGN.md alignment signals were detected by the static checker.');
  console.log('\nIssues:');
  if (review.issues.length) review.issues.forEach((item) => console.log(`- ${item}`));
  else console.log('- No obvious static consistency issues found.');
  console.log('\nSuggested fixes:');
  if (review.issues.length) {
    console.log('- Replace arbitrary colors, gradients, shadows, and radii with tokens or rules from DESIGN.md.');
    console.log('- Re-read the selected DESIGN.md before changing component hierarchy or page rhythm.');
    console.log('\nPatch suggestions:');
    if (review.patchSuggestions.length) review.patchSuggestions.forEach((item) => console.log(`- ${item}`));
    else console.log('- No token-aware patch suggestions were available from this DESIGN.md.');
    if (review.designTokens.colors.length) {
      console.log('\nDESIGN.md token candidates:');
      review.designTokens.colors.slice(0, 6).forEach((token) => console.log(`- ${token.name}: ${token.value}`));
    }
  } else {
    console.log('- Do a rendered visual pass against DESIGN.md before shipping.');
  }
}

function rankDesigns(query, source = 'built-in') {
  const normalized = normalize(query);
  const terms = tokenize(normalized);
  return filterBySource(designs, source)
    .map((design) => {
      const fields = [
        ['id/name', 10, [design.displayId, design.id, design.name, design.sourceId]],
        ['categories', 8, design.categories || []],
        ['bestFor', 8, design.bestFor || []],
        ['style', 6, design.style || []],
        ['keywords', 6, design.keywords || []],
        ['pageTypes', 5, design.pageTypes || []],
        ['description', 3, [design.description]],
        ['body', design.source === 'open-design' ? 1 : 0, [design.body || '']],
      ];
      let score = 0;
      const reasons = [];
      for (const [label, weight, values] of fields) {
        if (!weight) continue;
        const haystack = normalize(values.join(' '));
        const hits = terms.filter((term) => haystack.includes(term));
        if (hits.length) {
          score += weight * hits.length;
          reasons.push(`${label} matched ${unique(hits).slice(0, 3).join(', ')}`);
        }
      }
      return { design, score, reasons };
    })
    .sort((a, b) => b.score - a.score || a.design.displayId.localeCompare(b.design.displayId));
}

function enrichGoal(goal) {
  const expansions = [
    [/官网|主页|首页|marketing|homepage/i, 'landing'],
    [/后台|管理台|控制台|dashboard|admin/i, 'dashboard'],
    [/定价|pricing/i, 'pricing'],
    [/文档|docs|documentation|api/i, 'docs documentation'],
    [/登录|login|signin/i, 'login'],
    [/插件|扩展|chrome extension|extension/i, 'chrome-extension-landing extension'],
    [/极简|简洁|minimal/i, 'minimal clean'],
    [/高级|premium|luxury/i, 'premium polished'],
    [/科技感|技术|developer|开发者|工程师/i, 'developer technical'],
    [/金融|支付|fintech|payment/i, 'fintech payments'],
    [/暗色|dark/i, 'dark'],
    [/温暖|friendly|warm/i, 'warm friendly'],
    [/年轻|playful/i, 'playful creator'],
    [/中文|国内|中国|飞书|豆包|小红书|协作|团队/i, 'china domestic Chinese product-inspired collaboration workspace'],
    [/\bai\b|AI|人工智能|智能/i, 'ai ai-tool developer'],
  ];
  return `${goal} ${expansions.filter(([pattern]) => pattern.test(goal)).map(([, words]) => words).join(' ')}`;
}

function reasonFor(design, goal, reasons) {
  if (design.region === 'china' && /中文|国内|中国|飞书|豆包|小红书|协作|团队/i.test(goal)) {
    return `Chinese product-inspired fit for domestic users, with ${(design.style || []).slice(0, 3).join(', ')} visual cues. Not affiliated with or endorsed by the referenced product/company.`;
  }
  if (/AI|ai|人工智能|编程|developer|开发者|工程师/i.test(goal) && (design.bestFor || []).includes('ai-tool')) {
    return `strong fit for AI/developer-tool goals, with ${(design.style || []).slice(0, 3).join(', ')} visual discipline.`;
  }
  if (/dashboard|后台|管理台/i.test(goal) && (design.bestFor || []).includes('dashboard')) {
    return `dashboard-friendly information density and ${(design.categories || []).slice(0, 3).join(', ')} patterns.`;
  }
  if (/pricing|定价|金融|fintech/i.test(goal) && ((design.bestFor || []).includes('pricing') || (design.categories || []).includes('fintech'))) {
    return 'well suited to pricing, trust, and conversion surfaces.';
  }
  return `${design.description} (${reasons[0] ?? 'general fit'}).`;
}

function buildGeneratedDesignMd(design) {
  const lines = [
    '# DESIGN.generated.md',
    '',
    `Generated by Vibe UI ${registry.version}`,
    '',
    `Selected style: ${design.displayId}`,
    `Source style: ${design.sourceId}`,
    `Source collection: ${design.source === 'open-design' ? 'Vibe UI bundled upstream source' : 'Vibe UI curated registry'}`,
  ];
  if (design.source === 'open-design') lines.push('Upstream project: Open Design');
  if (design.repo) lines.push(`Repository: ${design.repo}`);
  if (design.sourcePath) lines.push(`Source path: ${design.sourcePath}`);
  if (design.commit) lines.push(`Commit: ${design.commit}`);
  lines.push('', design.disclaimer, '', '## How to Use', '', 'Use DESIGN.md as the source of truth for color, typography, spacing, radius, shadows, layout rhythm, component density, and interaction style.', '', '## Guardrails', '', '- Inspired by publicly visible UI patterns.', '- Not affiliated with or endorsed by the referenced product/company.', '- Do not copy logos, trademarks, proprietary assets, or official brand claims.', '- Do not introduce unrelated gradients, glassmorphism, neon colors, oversized shadows, or arbitrary hardcoded colors unless DESIGN.md explicitly supports them.', '- Run `node scripts/design.mjs check <file_or_directory>` after generating UI.');
  if (design.source === 'open-design') {
    lines.push('- See `resource/open-design-attribution.md` in the Vibe UI skill for bundled-resource attribution.');
  }
  return `${lines.join('\n')}\n`;
}

function findDesign(id) {
  if (!id) fail('Design id is required.');
  const normalized = aliases.get(id) ?? id;
  const openId = normalized.startsWith('open-design:') ? normalized : `open-design:${normalized}`;
  const design = designs.find((item) => (
    item.displayId === normalized ||
    item.id === normalized ||
    item.sourceId === normalized ||
    item.namespacedId === normalized ||
    item.namespacedId === openId
  ));
  if (!design) fail(`Unknown design: ${id}\nRun \`node scripts/design.mjs list --source all\` to see available styles.`);
  return design;
}

function findTemplate(id) {
  if (!id) fail('Template id is required.');
  const template = (templateRecipes.templates || []).find((item) => item.id === id || item.aliases?.includes(id));
  if (!template) fail(`Unknown template: ${id}\nRun \`node scripts/design.mjs browse --source all\` to see bundled recipes.`);
  return template;
}

function designSourcePath(design) {
  return join(skillRoot, registry.resourceRoot, design.sourceId, 'DESIGN.md');
}

async function loadCurrentDesign() {
  const statePath = join(process.cwd(), '.vibe-ui', 'current-design.json');
  if (!existsSync(statePath)) return null;
  return JSON.parse(await readFile(statePath, 'utf8'));
}

function supportedPageTypes() {
  return ['landing', 'dashboard', 'pricing', 'login', 'docs', 'settings', 'profile', 'chrome-extension-landing'];
}

function parseArgs(rawArgs) {
  const positional = [];
  const flags = {};
  for (let index = 0; index < rawArgs.length; index += 1) {
    const arg = rawArgs[index];
    if (arg.startsWith('--')) {
      const key = arg.slice(2);
      const next = rawArgs[index + 1];
      if (!next || next.startsWith('--')) {
        flags[key] = true;
      } else {
        flags[key] = next;
        index += 1;
      }
    } else {
      positional.push(arg);
    }
  }
  return { positional, flags };
}

function normalizeSource(value) {
  const source = value || 'built-in';
  if (!['built-in', 'open-design', 'all'].includes(source)) {
    fail('Unsupported source. Use one of: built-in, open-design, all.');
  }
  return source;
}

function filterBySource(items, source) {
  if (source === 'all') return items;
  return items.filter((item) => item.source === source);
}

function styleLabel(design) {
  const base = design.name.split(' ')[0].replace(/-inspired$/i, '');
  return `${base}-like`;
}

function strengthGuidance(strength) {
  if (strength === 'light') {
    return 'Use a light touch: borrow the spacing, clarity, and general mood while keeping the product visually distinct.';
  }
  if (strength === 'bold') {
    return 'Use a bold interpretation: make the layout rhythm, contrast, and component treatment clearly recognizable, while staying brand-safe.';
  }
  return 'Use a balanced interpretation: make the page recognizably inspired by the style without turning it into a replica.';
}

function pageRecipe(pageType) {
  const recipes = {
    landing: [
      'Hero with a sharp value proposition, one primary action, and a supporting product proof area.',
      'Feature sections with clear hierarchy, generous rhythm, and restrained decorative effects.',
      'Conversion section that repeats the core promise without adding unrelated visual tropes.',
    ],
    dashboard: [
      'Dense but readable overview with key metrics, primary workflow panels, and clear navigation.',
      'Use repeated component patterns so scanning feels calm and operational.',
      'Keep charts, cards, and tables aligned to the selected style density.',
    ],
    pricing: [
      'Pricing tiers with direct comparison, trust cues, and one obvious recommended plan.',
      'Make plan hierarchy clear through spacing, contrast, and concise feature grouping.',
      'Include FAQ or objection handling below the main conversion area.',
    ],
    login: [
      'Simple authentication panel with minimal fields and strong focus management.',
      'Use the surrounding space to communicate product tone without distracting from sign-in.',
      'Keep error, loading, and secondary actions visually quiet.',
    ],
    docs: [
      'Readable documentation shell with navigation, content hierarchy, and code/content examples.',
      'Favor clarity and fast scanning over marketing decoration.',
      'Use callouts sparingly and keep them aligned with the selected design language.',
    ],
    settings: [
      'Organize controls into predictable groups with clear labels, states, and save affordances.',
      'Keep density practical and avoid decorative layout choices.',
      'Make destructive or sensitive actions visually distinct but not loud.',
    ],
    profile: [
      'Profile header, identity details, activity/content areas, and meaningful secondary actions.',
      'Balance personal expression with the selected style system.',
      'Use repeated cards or sections only where they help comparison or scanning.',
    ],
    'chrome-extension-landing': [
      'Show the extension purpose immediately with browser or product-context framing.',
      'Explain install/use flow with compact steps and strong proof of usefulness.',
      'Keep calls to action focused on installing, trying, or viewing the extension.',
    ],
  };
  return recipes[pageType] ?? recipes.landing;
}

function antiPatternsForBrief(pageType, template) {
  const baseIds = [
    'default-llm-indigo',
    'hardcoded-color',
    'generic-ai-gradient',
    'emoji-icon',
    'invented-metric',
    'filler-copy',
    'missing-section-id',
  ];
  const contextualIds = [];
  if (['dashboard', 'settings', 'profile'].includes(pageType)) contextualIds.push('heavy-shadow', 'radius-drift');
  if (['landing', 'pricing', 'chrome-extension-landing'].includes(pageType)) contextualIds.push('invented-metric', 'filler-copy');
  if (template) contextualIds.push('missing-section-id');
  const patterns = unique([...baseIds, ...contextualIds])
    .map((id) => antiPatternById.get(id))
    .filter(Boolean);
  return patterns.length ? patterns : uiAntiPatterns.patterns || [];
}

function isDarkDesign(design) {
  const text = [
    design.description,
    ...(design.categories || []),
    ...(design.style || []),
    design.body || '',
  ].join(' ').toLowerCase();
  const hasDarkWords = /\bdark|black|night|midnight|charcoal|slate\b/.test(text);
  const hasDarkSwatch = (design.swatches || []).some((color) => /^#(?:0[0-9a-f]|1[0-9a-f]|2[0-9a-f])/i.test(color));
  return hasDarkWords || hasDarkSwatch;
}

function browserData(source = 'built-in') {
  return {
    version: registry.version,
    generatedAt: new Date().toISOString(),
    source,
    designs: filterBySource(designs, source).map((design) => ({
      id: design.displayId,
      name: design.name,
      source: design.source,
      sourceId: design.sourceId,
      sourcePath: design.sourcePath,
      region: design.region || 'global',
      description: design.description,
      categories: design.categories || [],
      bestFor: design.bestFor || [],
      pageTypes: design.pageTypes || [],
      style: design.style || [],
      swatches: design.swatches || [previewAccent(design)],
      commands: {
        use: `node scripts/design.mjs use ${design.displayId}`,
        like: `node scripts/design.mjs like ${design.displayId} landing --strength medium`,
        pricingLike: `node scripts/design.mjs like ${design.displayId} pricing --strength light`,
      },
      disclaimer: design.disclaimer,
    })),
    templates: templateRecipes.templates || [],
  };
}

function buildPreviewHtml(source = 'built-in') {
  const data = browserData(source);
  const cards = data.designs.map((design) => {
    const accent = design.swatches?.[0] || '#2563eb';
    return `<article class="card" data-source="${escapeHtml(design.source)}" data-tags="${escapeHtml([...design.categories, ...design.pageTypes, ...design.style].join(' '))}">
      <div class="swatch" style="background:${escapeHtml(accent)}"></div>
      <p class="source">${escapeHtml(design.source === 'open-design' ? 'Open Design' : 'Built-in')}</p>
      <h2>${escapeHtml(design.id)}</h2>
      <p>${escapeHtml(design.description)}</p>
      <div class="tags">${[...design.categories, ...design.pageTypes].slice(0, 6).map((tag) => `<span>${escapeHtml(tag)}</span>`).join('')}</div>
      <pre><button type="button" data-copy-command="node scripts/design.mjs use ${escapeHtml(design.id)}">copy command</button>node scripts/design.mjs use ${escapeHtml(design.id)}
node scripts/design.mjs like ${escapeHtml(design.id)} landing --strength medium</pre>
    </article>`;
  }).join('\n');
  const templateCards = data.templates.map((template) => `<article class="card template" data-source="template" data-tags="${escapeHtml([template.pageType, ...(template.tags || [])].join(' '))}">
      <div class="swatch" style="background:#111827"></div>
      <p class="source">Template recipe</p>
      <h2>${escapeHtml(template.id)}</h2>
      <p>${escapeHtml(template.description)}</p>
      <pre><button type="button" data-copy-command="node scripts/design.mjs generate ${escapeHtml(template.pageType)} --template ${escapeHtml(template.id)}">copy command</button>node scripts/design.mjs generate ${escapeHtml(template.pageType)} --template ${escapeHtml(template.id)}</pre>
    </article>`).join('\n');
  return `<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Vibe UI Design Browser</title>
  <style>
    body { margin: 0; font-family: Inter, ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; color: #181d26; background: #f6f7f9; }
    header { padding: 32px 28px 16px; max-width: 1180px; margin: 0 auto; }
    h1 { margin: 0 0 8px; font-size: 34px; letter-spacing: 0; }
    p { line-height: 1.55; }
    .toolbar { display: flex; flex-wrap: wrap; gap: 10px; max-width: 1180px; margin: 0 auto; padding: 10px 28px; }
    input, select { height: 38px; border: 1px solid #cfd6df; border-radius: 6px; padding: 0 10px; background: #fff; }
    .grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(260px, 1fr)); gap: 16px; max-width: 1180px; margin: 0 auto; padding: 20px 28px 48px; }
    .card { background: #fff; border: 1px solid #dfe3ea; border-radius: 8px; padding: 18px; box-shadow: 0 1px 2px rgba(15, 23, 42, .06); }
    .swatch { height: 6px; border-radius: 999px; margin-bottom: 14px; }
    .source { margin: 0 0 6px; font-size: 12px; color: #667085; }
    h2 { margin: 0 0 10px; font-size: 20px; letter-spacing: 0; }
    .tags { display: flex; flex-wrap: wrap; gap: 6px; margin: 14px 0; }
    .tags span { font-size: 12px; border: 1px solid #dfe3ea; border-radius: 999px; padding: 3px 8px; background: #f9fafb; }
    pre { position: relative; overflow-x: auto; background: #111827; color: #f9fafb; border-radius: 6px; padding: 34px 10px 10px; font-size: 12px; line-height: 1.45; }
    button { position: absolute; top: 8px; right: 8px; border: 1px solid #374151; border-radius: 5px; color: #f9fafb; background: #1f2937; font-size: 12px; padding: 4px 8px; }
  </style>
</head>
<body>
  <header>
    <h1>Vibe UI Design Browser</h1>
    <p>Filter built-in styles, bundled source systems, and template recipes. Pick a direction, copy command, then apply the DESIGN.md in your project.</p>
  </header>
  <section class="toolbar">
    <input data-filter-text placeholder="Search styles, categories, page types">
    <select data-filter-source>
      <option value="">All sources</option>
      <option value="built-in">Built-in</option>
      <option value="open-design">Open Design</option>
      <option value="template">Templates</option>
    </select>
  </section>
  <main class="grid">
    ${cards}
    ${templateCards}
  </main>
  <script>
    const text = document.querySelector('[data-filter-text]');
    const source = document.querySelector('[data-filter-source]');
    const cards = [...document.querySelectorAll('.card')];
    function applyFilters() {
      const q = text.value.toLowerCase();
      const s = source.value;
      for (const card of cards) {
        const matchesSource = !s || card.dataset.source === s;
        const matchesText = !q || card.innerText.toLowerCase().includes(q) || card.dataset.tags.toLowerCase().includes(q);
        card.hidden = !(matchesSource && matchesText);
      }
    }
    text.addEventListener('input', applyFilters);
    source.addEventListener('change', applyFilters);
    document.addEventListener('click', async (event) => {
      const button = event.target.closest('[data-copy-command]');
      if (!button) return;
      await navigator.clipboard.writeText(button.dataset.copyCommand);
      button.textContent = 'copied';
      setTimeout(() => { button.textContent = 'copy command'; }, 900);
    });
  </script>
</body>
</html>
`;
}

function previewAccent(design) {
  const palette = {
    stripe: '#635bff',
    linear: '#5e6ad2',
    apple: '#111827',
    feishu: '#3370ff',
    doubao: '#ff7a45',
    xiaohongshu: '#ff2442',
    'wechat-reading': '#07c160',
    figma: '#a259ff',
    slack: '#611f69',
  };
  return palette[design.sourceId] || palette[design.id] || '#2563eb';
}

async function loadUrlOrFile(input) {
  if (existsSync(resolve(process.cwd(), input))) {
    return readFile(resolve(process.cwd(), input), 'utf8');
  }
  if (input.startsWith('data:text/html,')) {
    return decodeURIComponent(input.slice('data:text/html,'.length));
  }
  if (/^https?:\/\//i.test(input)) {
    const response = await fetch(input);
    if (!response.ok) fail(`Failed to fetch URL: ${response.status} ${response.statusText}`);
    return response.text();
  }
  return input;
}

function buildExtractedDesignMd(source, html) {
  const title = textMatch(html, /<title[^>]*>([^<]+)<\/title>/i) || 'Extracted site';
  const description = textMatch(html, /<meta[^>]+name=["']description["'][^>]+content=["']([^"']+)["']/i) || 'Extracted from URL evidence.';
  const colors = unique([...html.matchAll(/#[0-9a-fA-F]{3,8}/g)].map((match) => normalizeHex(match[0]))).slice(0, 8);
  return `# ${title} DESIGN.md

Generated by Vibe UI ${registry.version} URL-to-DESIGN.md extractor.

Source: ${source}

## Summary

${description}

## Tokens

${colors.length ? colors.map((color, index) => `color-${index + 1}: ${color}`).join('\n') : 'primary: #111827\nsurface: #ffffff\nmuted: #6b7280'}

## Usage Notes

- Treat this as a draft DESIGN.md extracted from public page evidence.
- Review colors, typography, spacing, and brand-safety before using it.
- Do not copy logos, trademarks, proprietary assets, or official brand claims.
`;
}

function buildImportedDesignMd(kind, source, text) {
  const colors = unique([...text.matchAll(/#[0-9a-fA-F]{3,8}/g)].map((match) => normalizeHex(match[0]))).slice(0, 8);
  const summary = text.replace(/\s+/g, ' ').trim().slice(0, 220) || 'Visual reference import.';
  return `# Imported ${kind} DESIGN.md

Generated by Vibe UI ${registry.version} ${kind} import.

Source: ${source}

## Visual Summary

${summary}

## Tokens

${colors.length ? colors.map((color, index) => `color-${index + 1}: ${color}`).join('\n') : 'primary: #111827\nsurface: #ffffff\nmuted: #6b7280'}

## Guidance

- Use this imported reference as a starting point, not as proof of an official design system.
- Convert visible patterns into reusable layout, spacing, color, radius, and typography rules.
- Do not copy logos, trademarks, proprietary assets, or official brand claims.
`;
}

function buildReportMarkdown(review) {
  const lines = [
    '# Design Consistency Report',
    '',
    `Generated by Vibe UI ${registry.version}`,
    '',
    `Selected style: ${review.current?.id ?? 'unknown'}`,
    `Files checked: ${review.files.length}`,
    `Score: ${review.score}/10`,
    '',
    `## ${qualityGateName}`,
    '',
    `Quality gate score: ${review.gate.score}/10`,
    `Decision: ${review.gate.decision}`,
    '',
    '### Blocking issues',
    ...(review.gate.blocking.length
      ? review.gate.blocking.map((finding) => `- ${finding.id}: ${finding.fix}`)
      : ['- None detected by the static checker.']),
    '',
    '### Top fixes before handoff',
    ...(review.gate.topFixes.length
      ? review.gate.topFixes.map((fix) => `- ${fix}`)
      : ['- Do a rendered visual pass against DESIGN.md before shipping.']),
    '',
    '## Good',
    ...(review.good.length ? review.good.map((item) => `- ${item}`) : ['- No strong DESIGN.md alignment signals were detected by the static checker.']),
  ];
  for (const heading of ['Color', 'Typography', 'Layout', 'Components', 'Copy/content', 'Brand safety', 'Accessibility']) {
    lines.push('', `## ${heading}`);
    const items = review.findings[heading] || [];
    lines.push(...(items.length ? items.map((item) => `- ${item}`) : ['- No static findings in this category.']));
  }
  lines.push('', '## Patch suggestions');
  lines.push(...(review.patchSuggestions.length ? review.patchSuggestions.map((item) => `- ${item}`) : ['- No token-aware patch suggestions were available from this DESIGN.md.']));
  lines.push('', '## Vibe Gate Guidance');
  if (review.qaFindings?.length) {
    for (const finding of review.qaFindings) {
      lines.push('', `### ${finding.id}`);
      lines.push('Bad:');
      lines.push(`- ${finding.bad}`);
      lines.push('Fix:');
      lines.push(`- ${finding.fix}`);
      lines.push('Evidence:');
      lines.push(`- ${finding.evidence}`);
    }
  } else {
    lines.push('- No Vibe Gate anti-patterns were detected by the static checker.');
  }
  if (review.designTokens.colors.length) {
    lines.push('', '## DESIGN.md token candidates');
    review.designTokens.colors.slice(0, 8).forEach((token) => lines.push(`- ${token.name}: ${token.value}`));
  }
  return `${lines.join('\n')}\n`;
}

function normalizeDesignId(value) {
  return (value || '').toLowerCase().replace(/[^a-z0-9-]+/g, '-').replace(/^-+|-+$/g, '');
}

function inferImportKind(source) {
  return /figma/i.test(source) ? 'figma' : 'screenshot';
}

function textMatch(text, pattern) {
  const match = text.match(pattern);
  return match ? decodeHtml(match[1].trim()) : '';
}

function decodeHtml(value) {
  return value
    .replace(/&amp;/g, '&')
    .replace(/&lt;/g, '<')
    .replace(/&gt;/g, '>')
    .replace(/&quot;/g, '"')
    .replace(/&#39;/g, "'");
}

function escapeHtml(value) {
  return String(value)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

async function collectFiles(target) {
  const info = await stat(target);
  if (info.isFile()) return [target];
  const output = [];
  async function walk(dir) {
    const entries = await readdir(dir, { withFileTypes: true });
    for (const entry of entries) {
      if (entry.name.startsWith('.') || entry.name === 'node_modules' || entry.name === 'dist' || entry.name === 'build') continue;
      const full = join(dir, entry.name);
      if (entry.isDirectory()) await walk(full);
      else if (isCodeFile(full)) output.push(full);
    }
  }
  await walk(target);
  return output;
}

function isCodeFile(file) {
  return ['.js', '.jsx', '.ts', '.tsx', '.vue', '.svelte', '.html', '.css', '.scss', '.mdx'].includes(extname(file));
}

function extractDesignTokenHints(text) {
  const colors = [];
  for (const line of text.split('\n')) {
    const match = line.match(/^\s*([\w-]+):\s*['"]?(#[0-9a-fA-F]{3,8})['"]?/);
    if (match) colors.push({ name: match[1], value: normalizeHex(match[2]) });
  }
  const markdownColors = [...text.matchAll(/\*\*([^*]+)\*\*\s*\(`(#[0-9a-fA-F]{3,8})`\)/g)]
    .map((match) => ({ name: normalizeDesignId(match[1]) || 'color', value: normalizeHex(match[2]) }));
  colors.push(...markdownColors);
  return {
    colors: uniqueBy(colors, (token) => `${token.name}:${token.value}`),
    radii: [...text.matchAll(/^\s*([\w-]+):\s*['"]?([0-9.]+px|9999px|999px|50%)['"]?/gm)]
      .map((match) => ({ name: match[1], value: match[2] }))
      .filter((token) => /radius|rounded|pill|full|sm|md|lg|xl/i.test(token.name)),
    shadows: [...text.matchAll(/^\s*([\w-]+):\s*['"]?([^'"\n]*(?:shadow|rgba|px)[^'"\n]*)['"]?/gim)]
      .map((match) => ({ name: match[1], value: match[2].trim() })),
  };
}

function preferredColorToken(tokens, preferredNames) {
  const byName = tokens.colors.find((token) => preferredNames.some((name) => token.name.toLowerCase().includes(name)));
  return byName ?? tokens.colors[0] ?? { name: 'primary', value: '#000000' };
}

function preferredRadius(tokens) {
  const radius = tokens.radii.find((token) => /sm|md|button|card|radius/i.test(token.name));
  if (!radius) return 'rounded-lg';
  const numeric = Number.parseFloat(radius.value);
  if (Number.isFinite(numeric)) {
    if (numeric <= 4) return 'rounded';
    if (numeric <= 8) return 'rounded-md';
    if (numeric <= 12) return 'rounded-lg';
    return `rounded-[${radius.value}]`;
  }
  return `rounded-[${radius.value}]`;
}

function preferredShadow(tokens) {
  const shadow = tokens.shadows.find((token) => /sm|subtle|card|elev/i.test(token.name));
  return shadow ? 'shadow-sm' : 'shadow-sm';
}

function normalizeHex(value) {
  return value.length === 4
    ? `#${value[1]}${value[1]}${value[2]}${value[2]}${value[3]}${value[3]}`.toLowerCase()
    : value.toLowerCase();
}

function normalize(value) {
  return value.toLowerCase().replace(/[._:-]+/g, ' ');
}

function tokenize(value) {
  return unique(normalize(value).split(/[^\p{L}\p{N}]+/u).filter((term) => term.length >= 2));
}

function unique(values) {
  return [...new Set(values)];
}

function uniqueBy(values, keyFn) {
  const seen = new Set();
  return values.filter((value) => {
    const key = keyFn(value);
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
}

function inferPageTypes(system) {
  const text = `${system.category} ${system.description} ${(system.keywords || []).join(' ')}`.toLowerCase();
  const pageTypes = [];
  if (/dashboard|admin|productivity|saas|data/.test(text)) pageTypes.push('dashboard');
  if (/pricing|fintech|crypto|commerce|retail|saas/.test(text)) pageTypes.push('pricing');
  if (/docs|developer|api|documentation/.test(text)) pageTypes.push('docs');
  if (/profile|consumer|media|creative|portfolio/.test(text)) pageTypes.push('profile');
  pageTypes.unshift('landing');
  return unique(pageTypes);
}

function inferBestFor(system) {
  const text = `${system.category} ${system.description} ${(system.keywords || []).join(' ')}`.toLowerCase();
  const bestFor = ['landing'];
  if (/dashboard|productivity|saas/.test(text)) bestFor.push('dashboard');
  if (/pricing|fintech|crypto|commerce/.test(text)) bestFor.push('pricing');
  if (/docs|developer/.test(text)) bestFor.push('docs');
  if (/ai|llm/.test(text)) bestFor.push('ai-tool');
  if (/developer/.test(text)) bestFor.push('developer-tool');
  return unique(bestFor);
}

function fail(message) {
  console.error(message);
  process.exit(1);
}
