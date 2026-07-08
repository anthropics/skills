import { execaCommand } from 'execa';
import { CheckResult } from '../types.js';

export async function runLintCheck(
  command: string = 'npm run lint',
  timeoutMs: number = 30000
): Promise<CheckResult> {
  const startTime = Date.now();

  try {
    const result = await execaCommand(command, {
      timeout: timeoutMs,
      stdio: 'pipe',
    });

    return {
      name: 'lint',
      success: true,
      duration: Date.now() - startTime,
      output: result.stdout || 'Linting passed',
      severity: 'error',
    };
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : String(error);

    return {
      name: 'lint',
      success: false,
      duration: Date.now() - startTime,
      error: errorMessage,
      severity: 'error',
    };
  }
}
