/**
 * Tests for PreDeployValidator
 * Run with: node test.js
 */

const PreDeployValidator = require('./index');

let passed = 0;
let failed = 0;

function assert(condition, message) {
  if (condition) {
    console.log(`  ✅ ${message}`);
    passed++;
  } else {
    console.error(`  ❌ FAIL: ${message}`);
    failed++;
  }
}

async function run() {
  console.log('Running PreDeployValidator tests...\n');

  // ── Constructor defaults ──────────────────────────────────────────────────
  console.log('Constructor defaults');
  const v = new PreDeployValidator();
  assert(v.config.checkCodeQuality === true,  'checkCodeQuality defaults to true');
  assert(v.config.checkSecurity === true,     'checkSecurity defaults to true');
  assert(v.config.checkTests === true,        'checkTests defaults to true');
  assert(v.config.checkDependencies === true, 'checkDependencies defaults to true');
  assert(v.config.checkDocumentation === true,'checkDocumentation defaults to true');
  assert(v.config.failOnWarnings === false,   'failOnWarnings defaults to false');

  // ── Constructor overrides ─────────────────────────────────────────────────
  console.log('\nConstructor overrides');
  const v2 = new PreDeployValidator({ checkSecurity: false, failOnWarnings: true });
  assert(v2.config.checkSecurity === false, 'checkSecurity can be disabled');
  assert(v2.config.failOnWarnings === true, 'failOnWarnings can be enabled');

  // ── Initial results state ─────────────────────────────────────────────────
  console.log('\nInitial results state');
  assert(Array.isArray(v.results.passed),   'results.passed is array');
  assert(Array.isArray(v.results.warnings), 'results.warnings is array');
  assert(Array.isArray(v.results.failures), 'results.failures is array');
  assert(Array.isArray(v.results.errors),   'results.errors is array');

  // ── getFilesToCheck ───────────────────────────────────────────────────────
  console.log('\ngetFilesToCheck');
  const files = v.getFilesToCheck(['.js']);
  assert(Array.isArray(files),          'returns an array');
  assert(files.length > 0,              'finds at least one .js file');
  assert(files.every(f => f.endsWith('.js')), 'all returned files match extension');
  assert(!files.some(f => f.includes('node_modules')), 'excludes node_modules');

  // ── checkDocumentation — missing docs ────────────────────────────────────
  console.log('\ncheckDocumentation (missing docs)');
  const vDoc = new PreDeployValidator({
    checkCodeQuality: false, checkSecurity: false,
    checkTests: false, checkDependencies: false
  });
  // Run only the documentation check in a temp dir context by mocking existsSync
  const origExists = require('fs').existsSync;
  require('fs').existsSync = () => false;
  await vDoc.checkDocumentation();
  require('fs').existsSync = origExists;
  assert(vDoc.results.failures.length > 0, 'reports failure when docs are missing');

  // ── checkSecurity — clean content ────────────────────────────────────────
  console.log('\ncheckSecurity (no secrets)');
  const vSec = new PreDeployValidator({
    checkCodeQuality: false, checkTests: false,
    checkDependencies: false, checkDocumentation: false
  });
  // Override getFilesToCheck to return only this clean test file
  vSec.getFilesToCheck = () => [__filename];
  await vSec.checkSecurity();
  assert(
    vSec.results.passed.some(m => m.includes('No sensitive patterns')),
    'passes security check when no secrets found'
  );
  assert(vSec.results.failures.length === 0, 'no failures for clean file');

  // ── generateReport — success path ────────────────────────────────────────
  console.log('\ngenerateReport (success)');
  const vRep = new PreDeployValidator();
  vRep.results.passed = ['check a', 'check b'];
  const report = vRep.generateReport();
  assert(report.success === true,            'success=true when no failures or errors');
  assert(typeof report.results === 'object', 'report.results is object');

  // ── generateReport — failure path ────────────────────────────────────────
  console.log('\ngenerateReport (failure)');
  const vFail = new PreDeployValidator();
  vFail.results.failures = ['something broke'];
  const failReport = vFail.generateReport();
  assert(failReport.success === false, 'success=false when failures present');

  // ── generateReport — error path ──────────────────────────────────────────
  console.log('\ngenerateReport (error)');
  const vErr = new PreDeployValidator();
  vErr.results.errors = ['unexpected crash'];
  const errReport = vErr.generateReport();
  assert(errReport.success === false, 'success=false when errors present');

  // ── Summary ───────────────────────────────────────────────────────────────
  console.log(`\n${'─'.repeat(40)}`);
  console.log(`Results: ${passed} passed, ${failed} failed`);

  if (failed > 0) {
    process.exit(1);
  }
}

run().catch(err => {
  console.error('Test runner error:', err);
  process.exit(1);
});
