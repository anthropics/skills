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
  assert(v2.config.failOnWarnings === true, 'failOnWarnings can be set');

  // Test 3: Results structure
  console.log('\nTest: Results structure');
  const v3 = new PreDeployValidator();
  assert(Array.isArray(v3.results.passed), 'results.passed is an array');
  assert(Array.isArray(v3.results.warnings), 'results.warnings is an array');
  assert(Array.isArray(v3.results.failures), 'results.failures is an array');
  assert(Array.isArray(v3.results.errors), 'results.errors is an array');

  // Test 4: getFilesToCheck returns an array
  console.log('\nTest: getFilesToCheck');
  const v4 = new PreDeployValidator();
  const files = v4.getFilesToCheck(['.js']);
  assert(Array.isArray(files), 'getFilesToCheck returns an array');
  assert(files.length > 0, 'getFilesToCheck finds .js files');

  // Test 5: validate returns report with success property
  console.log('\nTest: validate returns report');
  const v5 = new PreDeployValidator({ checkDependencies: false, checkTests: false });
  const report = await v5.validate();
  assert(typeof report.success === 'boolean', 'report.success is boolean');
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
