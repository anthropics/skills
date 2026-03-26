/**
 * Tests for PreDeployValidator
 */

const PreDeployValidator = require('./index.js');

let passed = 0;
let failed = 0;

function assert(condition, message) {
  if (condition) {
    console.log(`  ✓ ${message}`);
    passed++;
  } else {
    console.error(`  ✗ ${message}`);
    failed++;
  }
}

async function runTests() {
  console.log('Running PreDeployValidator tests...\n');

  // Test 1: Constructor defaults
  console.log('Test: Constructor defaults');
  const validator = new PreDeployValidator();
  assert(validator.config.checkCodeQuality === true, 'checkCodeQuality defaults to true');
  assert(validator.config.checkSecurity === true, 'checkSecurity defaults to true');
  assert(validator.config.checkTests === true, 'checkTests defaults to true');
  assert(validator.config.checkDependencies === true, 'checkDependencies defaults to true');
  assert(validator.config.checkDocumentation === true, 'checkDocumentation defaults to true');
  assert(validator.config.failOnWarnings === false, 'failOnWarnings defaults to false');

  // Test 2: Constructor with config overrides
  console.log('\nTest: Constructor config overrides');
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
  const v5 = new PreDeployValidator({ checkDependencies: false });
  const report = await v5.validate();
  assert(typeof report.success === 'boolean', 'report.success is boolean');
  assert(typeof report.results === 'object', 'report.results is object');

  console.log(`\n${passed} passed, ${failed} failed`);

  if (failed > 0) {
    process.exit(1);
  }
}

runTests().catch(err => {
  console.error('Test runner error:', err);
  process.exit(1);
});
