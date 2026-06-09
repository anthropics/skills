import { execaCommand } from 'execa';
import { CheckResult } from '../types.js';

export async function runTypeScriptCheck(
  command: string = 'tsc --noEmit',
  timeoutMs: number = 60000
): Promise<CheckResult> {
  const startTime = Date.now();

  try {
    await execaCommand(command, {
      timeout: timeoutMs,
      stdio: 'pipe',
    });

    return {
      name: 'typescript',
      success: true,
      duration: Date.now() - startTime,
      output: 'TypeScript compilation successful',
      severity: 'error',
    };
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : String(error);

    return {
      name: 'typescript',
      success: false,
      duration: Date.now() - startTime,
      error: errorMessage,
      severity: 'error',
    };
  }
}
