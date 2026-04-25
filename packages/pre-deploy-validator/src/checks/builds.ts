import { execaCommand } from 'execa';
import { CheckResult } from '../types.js';

export async function runBuildCheck(
  command: string = 'npm run build',
  projects: string[] = ['.'],
  timeoutMs: number = 180000
): Promise<CheckResult> {
  const startTime = Date.now();
  const results: { project: string; success: boolean; error?: string }[] = [];

  for (const project of projects) {
    try {
      const fullCommand = command.includes('-w')
        ? command
        : `${command} -w ${project === '.' ? 'root' : project}`;

      await execaCommand(fullCommand, {
        timeout: timeoutMs,
        stdio: 'pipe',
        cwd: project === '.' ? undefined : project,
      });

      results.push({
        project,
        success: true,
      });
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : String(error);
      results.push({
        project,
        success: false,
        error: errorMessage,
      });
    }
  }

  const allSuccess = results.every((r) => r.success);
  const failedProjects = results.filter((r) => !r.success);

  return {
    name: 'build',
    success: allSuccess,
    duration: Date.now() - startTime,
    output: allSuccess
      ? `All ${projects.length} project(s) built successfully`
      : `Failed projects: ${failedProjects.map((r) => r.project).join(', ')}`,
    error: allSuccess ? undefined : failedProjects.map((r) => `${r.project}: ${r.error}`).join('\n'),
    severity: 'error',
  };
}
