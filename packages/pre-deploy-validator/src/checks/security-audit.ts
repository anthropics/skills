import { execaCommand } from 'execa';
import { CheckResult } from '../types.js';

export async function runSecurityAuditCheck(
  command: string = 'npm audit --audit-level=moderate',
  timeoutMs: number = 45000
): Promise<CheckResult> {
  const startTime = Date.now();

  try {
    const result = await execaCommand(command, {
      timeout: timeoutMs,
      stdio: 'pipe',
      reject: false,
    });

    // npm audit returns non-zero exit code even on warnings
    const output = result.stdout || '';

    if (result.exitCode === 0 || output.includes('0 vulnerabilities')) {
      return {
        name: 'security-audit',
        success: true,
        duration: Date.now() - startTime,
        output: 'Security audit passed - no vulnerabilities found',
        severity: 'error',
      };
    }

    // Check if vulnerabilities are below threshold
    if (output.includes('moderate') || output.includes('high') || output.includes('critical')) {
      return {
        name: 'security-audit',
        success: false,
        duration: Date.now() - startTime,
        error: 'Vulnerabilities found at or above threshold',
        severity: 'error',
      };
    }

    return {
      name: 'security-audit',
      success: true,
      duration: Date.now() - startTime,
      output: 'Security audit completed',
      severity: 'error',
    };
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : String(error);

    return {
      name: 'security-audit',
      success: false,
      duration: Date.now() - startTime,
      error: errorMessage,
      severity: 'error',
    };
  }
}
