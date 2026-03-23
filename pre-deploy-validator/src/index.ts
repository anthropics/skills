import { execaCommand } from 'execa';
import { CheckResult, PreDeployConfig, ValidationResult, CheckConfig } from './types.js';
import { runLintCheck } from './checks/lint.js';
import { runTypeScriptCheck } from './checks/typescript.js';
import { runTestsCheck } from './checks/tests.js';
import { runSecurityAuditCheck } from './checks/security-audit.js';
import { runBuildCheck } from './checks/builds.js';

export class PreDeployValidator {
  private config: PreDeployConfig;

  constructor(config: PreDeployConfig) {
    this.config = config;
  }

  async runChecks(): Promise<ValidationResult> {
    const startTime = Date.now();
    const results: CheckResult[] = [];
    const errors: string[] = [];

    // Check if we should skip on this branch
    if (this.config.skipOnBranches) {
      const currentBranch = await this.getCurrentBranch();
      if (this.config.skipOnBranches.includes(currentBranch)) {
        return {
          success: true,
          checks: [],
          duration: 0,
          errors: [`Skipped on branch: ${currentBranch}`],
          timestamp: new Date().toISOString(),
        };
      }
    }

    // Run checks
    const checkNames = Object.keys(this.config.checks);
    const checks = checkNames.map((name) => ({
      name,
      config: this.config.checks[name],
    }));

    if (this.config.parallel) {
      const promises = checks
        .filter((c) => c.config.enabled)
        .map((c) => this.runCheck(c.name, c.config));
      const checkResults = await Promise.all(promises);
      results.push(...checkResults);
    } else {
      for (const check of checks) {
        if (check.config.enabled) {
          const result = await this.runCheck(check.name, check.config);
          results.push(result);
        }
      }
    }

    // Collect errors
    for (const result of results) {
      if (!result.success && result.severity === 'error') {
        errors.push(`${result.name}: ${result.error || 'unknown error'}`);
      }
    }

    const duration = Date.now() - startTime;
    const success = errors.length === 0;

    return {
      success,
      checks: results,
      duration,
      errors,
      timestamp: new Date().toISOString(),
    };
  }

  private async runCheck(
    name: string,
    config: CheckConfig
  ): Promise<CheckResult> {
    switch (name) {
      case 'lint':
        return runLintCheck(
          config.command || 'npm run lint',
          config.timeoutMs || 30000
        );
      case 'typescript':
        return runTypeScriptCheck(
          config.command || 'tsc --noEmit',
          config.timeoutMs || 60000
        );
      case 'tests':
        return runTestsCheck(
          config.command || 'npm test',
          config.timeoutMs || 120000,
          config.coverageThreshold
        );
      case 'security-audit':
        return runSecurityAuditCheck(
          config.command || 'npm audit --audit-level=moderate',
          config.timeoutMs || 45000
        );
      case 'build':
        return runBuildCheck(
          config.command || 'npm run build',
          config.projects || ['.'],
          config.timeoutMs || 180000
        );
      default:
        return {
          name,
          success: false,
          duration: 0,
          error: `Unknown check: ${name}`,
          severity: 'error',
        };
    }
  }

  private async getCurrentBranch(): Promise<string> {
    try {
      const result = await execaCommand('git rev-parse --abbrev-ref HEAD', {
        stdio: 'pipe',
      });
      return result.stdout.trim();
    } catch {
      return 'unknown';
    }
  }

  getReport(format: 'console' | 'json' = this.config.reportFormat || 'console'): string {
    return format === 'json' ? 'Use formatJsonReport()' : 'Use formatConsoleReport()';
  }
}

export { PreDeployConfig, ValidationResult, CheckResult } from './types.js';
export { formatConsoleReport } from './reporters/console.js';
export { formatJsonReport } from './reporters/json.js';
