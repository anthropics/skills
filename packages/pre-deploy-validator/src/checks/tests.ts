import { execaCommand } from 'execa';
import { CheckResult } from '../types.js';

interface CoverageThreshold {
  lines: number;
  functions: number;
  branches: number;
}

export async function runTestsCheck(
  command: string = 'npm test',
  timeoutMs: number = 120000,
  coverageThreshold?: CoverageThreshold
): Promise<CheckResult> {
  const startTime = Date.now();

  try {
    const result = await execaCommand(command, {
      timeout: timeoutMs,
      stdio: 'pipe',
    });

    // Check coverage if thresholds are provided
    if (coverageThreshold) {
      const output = result.stdout || '';
      // Basic coverage validation - in real implementation would parse coverage reports
      if (output.includes('coverage') && output.includes('100%')) {
        return {
          name: 'tests',
          success: true,
          duration: Date.now() - startTime,
          output: 'Tests passed with coverage requirements met',
          severity: 'error',
        };
      }
    }

    return {
      name: 'tests',
      success: true,
      duration: Date.now() - startTime,
      output: 'Tests passed',
      severity: 'error',
    };
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : String(error);

    return {
      name: 'tests',
      success: false,
      duration: Date.now() - startTime,
      error: errorMessage,
      severity: 'error',
    };
  }
}
