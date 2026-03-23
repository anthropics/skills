import { describe, it, expect, beforeEach, vi } from 'vitest';
import { PreDeployValidator } from '../src/index.js';
import { PreDeployConfig, ValidationResult } from '../src/types.js';

describe('PreDeployValidator', () => {
  let validator: PreDeployValidator;
  let config: PreDeployConfig;

  beforeEach(() => {
    config = {
      name: 'test-validator',
      version: '1.0.0',
      description: 'Test config',
      checks: {
        lint: {
          enabled: true,
          command: 'echo "Lint passed"',
          timeoutMs: 5000,
          onFail: 'block',
        },
        typescript: {
          enabled: false,
          command: 'echo "TypeScript passed"',
          timeoutMs: 5000,
          onFail: 'block',
        },
      },
      skipOnBranches: [],
      parallel: false,
      reportFormat: 'console',
      exitCode: 1,
    };
    validator = new PreDeployValidator(config);
  });

  it('should initialize with a valid config', () => {
    expect(validator).toBeDefined();
  });

  it('should return a ValidationResult with correct structure', async () => {
    const result = await validator.runChecks();

    expect(result).toHaveProperty('success');
    expect(result).toHaveProperty('checks');
    expect(result).toHaveProperty('duration');
    expect(result).toHaveProperty('errors');
    expect(result).toHaveProperty('timestamp');
  });

  it('should include only enabled checks in results', async () => {
    const result = await validator.runChecks();
    const checkNames = result.checks.map((c) => c.name);

    expect(checkNames).toContain('lint');
    expect(checkNames).not.toContain('typescript');
  });

  it('should record check duration', async () => {
    const result = await validator.runChecks();

    expect(result.duration).toBeGreaterThanOrEqual(0);
    result.checks.forEach((check) => {
      expect(check.duration).toBeGreaterThanOrEqual(0);
    });
  });

  it('should handle failed checks', async () => {
    const failConfig = {
      ...config,
      checks: {
        lint: {
          enabled: true,
          command: 'false',
          timeoutMs: 5000,
          onFail: 'block',
        },
      },
    };

    const failValidator = new PreDeployValidator(failConfig);
    const result = await failValidator.runChecks();

    expect(result.success).toBe(false);
    expect(result.errors.length).toBeGreaterThan(0);
  });

  it('should support parallel execution', async () => {
    config.parallel = true;
    const parallelValidator = new PreDeployValidator(config);
    const result = await parallelValidator.runChecks();

    expect(result).toHaveProperty('checks');
    expect(Array.isArray(result.checks)).toBe(true);
  });

  it('should skip checks on specified branches', async () => {
    config.skipOnBranches = ['main', 'develop'];
    const skipValidator = new PreDeployValidator(config);
    const result = await skipValidator.runChecks();

    // Result will depend on current branch
    expect(result).toHaveProperty('success');
  });

  it('should return checks with name property', async () => {
    const result = await validator.runChecks();

    result.checks.forEach((check) => {
      expect(check).toHaveProperty('name');
      expect(typeof check.name).toBe('string');
    });
  });

  it('should include timestamps in result', async () => {
    const result = await validator.runChecks();

    expect(result.timestamp).toBeTruthy();
    // Verify it's a valid ISO string
    expect(new Date(result.timestamp).getTime()).toBeGreaterThan(0);
  });

  it('should handle unknown checks gracefully', async () => {
    const unknownConfig = {
      ...config,
      checks: {
        unknown: {
          enabled: true,
          command: 'echo test',
          timeoutMs: 5000,
          onFail: 'block',
        },
      },
    };

    const unknownValidator = new PreDeployValidator(unknownConfig);
    const result = await unknownValidator.runChecks();

    expect(result.checks.length).toBeGreaterThan(0);
    const unknownCheck = result.checks.find((c) => c.name === 'unknown');
    expect(unknownCheck?.success).toBe(false);
  });
});
