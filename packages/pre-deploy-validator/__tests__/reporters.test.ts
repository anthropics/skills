import { describe, it, expect } from 'vitest';
import { formatConsoleReport, formatJsonReport } from '../src/index.js';
import { ValidationResult } from '../src/types.js';

describe('Reporters', () => {
  const mockResult: ValidationResult = {
    success: true,
    checks: [
      {
        name: 'lint',
        success: true,
        duration: 1000,
        output: 'Lint passed',
        severity: 'error',
      },
      {
        name: 'typescript',
        success: true,
        duration: 2000,
        output: 'TypeScript passed',
        severity: 'error',
      },
    ],
    duration: 3000,
    errors: [],
    timestamp: '2024-01-01T00:00:00.000Z',
  };

  const failedResult: ValidationResult = {
    success: false,
    checks: [
      {
        name: 'lint',
        success: false,
        duration: 1000,
        error: 'Linting failed',
        severity: 'error',
      },
    ],
    duration: 1000,
    errors: ['lint: Linting failed'],
    timestamp: '2024-01-01T00:00:00.000Z',
  };

  describe('formatConsoleReport', () => {
    it('should format a successful result', () => {
      const report = formatConsoleReport(mockResult);

      expect(report).toContain('Pre-Deployment Validation Report');
      expect(report).toContain('PASSED');
      expect(report).toContain('✓');
    });

    it('should include check details', () => {
      const report = formatConsoleReport(mockResult);

      expect(report).toContain('lint');
      expect(report).toContain('typescript');
    });

    it('should show duration', () => {
      const report = formatConsoleReport(mockResult);

      expect(report).toContain('Duration');
      expect(report).toMatch(/\d+\.\d+s/);
    });

    it('should format failed results', () => {
      const report = formatConsoleReport(failedResult);

      expect(report).toContain('FAILED');
      expect(report).toContain('✗');
      expect(report).toContain('Error:');
    });

    it('should include errors summary', () => {
      const report = formatConsoleReport(failedResult);

      expect(report).toContain('Issues');
      expect(report).toContain('Linting failed');
    });

    it('should include timestamp', () => {
      const report = formatConsoleReport(mockResult);

      expect(report).toContain('2024-01-01');
    });
  });

  describe('formatJsonReport', () => {
    it('should format result as valid JSON', () => {
      const report = formatJsonReport(mockResult);
      const parsed = JSON.parse(report);

      expect(parsed).toEqual(mockResult);
    });

    it('should preserve all result properties', () => {
      const report = formatJsonReport(mockResult);
      const parsed = JSON.parse(report);

      expect(parsed.success).toBe(true);
      expect(Array.isArray(parsed.checks)).toBe(true);
      expect(parsed.duration).toBeDefined();
      expect(parsed.errors).toBeDefined();
      expect(parsed.timestamp).toBeDefined();
    });

    it('should format failed results', () => {
      const report = formatJsonReport(failedResult);
      const parsed = JSON.parse(report);

      expect(parsed.success).toBe(false);
      expect(parsed.errors.length).toBeGreaterThan(0);
    });

    it('should be properly indented', () => {
      const report = formatJsonReport(mockResult);

      expect(report).toContain('\n');
      expect(report).toMatch(/\s{2}"success"/);
    });
  });
});
