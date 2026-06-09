import chalk from 'chalk';
import { ValidationResult } from '../types.js';

export function formatConsoleReport(result: ValidationResult): string {
  const lines: string[] = [];

  lines.push(chalk.bold('\n📋 Pre-Deployment Validation Report\n'));

  // Summary
  const statusIcon = result.success ? chalk.green('✓') : chalk.red('✗');
  const statusText = result.success
    ? chalk.green('PASSED')
    : chalk.red('FAILED');

  lines.push(`${statusIcon} Status: ${statusText}`);
  lines.push(`⏱️  Duration: ${(result.duration / 1000).toFixed(2)}s`);
  lines.push(`📅 Timestamp: ${result.timestamp}`);

  // Individual checks
  lines.push(chalk.bold('\n Checks:\n'));

  for (const check of result.checks) {
    const checkIcon = check.success ? chalk.green('✓') : chalk.red('✗');
    const checkName = chalk.cyan(check.name.padEnd(20));
    const duration = chalk.gray(`(${(check.duration / 1000).toFixed(2)}s)`);

    lines.push(`  ${checkIcon} ${checkName} ${duration}`);

    if (!check.success && check.error) {
      lines.push(chalk.red(`      Error: ${check.error.split('\n')[0]}`));
    }

    if (check.output && !check.success) {
      const outputLines = check.output.split('\n').slice(0, 2);
      outputLines.forEach((line) => {
        if (line.trim()) {
          lines.push(chalk.gray(`      ${line}`));
        }
      });
    }
  }

  // Errors summary
  if (result.errors.length > 0) {
    lines.push(chalk.bold('\n⚠️  Issues:\n'));
    result.errors.forEach((error) => {
      lines.push(chalk.red(`  • ${error}`));
    });
  }

  // Footer
  if (!result.success) {
    lines.push(chalk.bold(chalk.red('\n❌ Deployment blocked due to check failures\n')));
  } else {
    lines.push(chalk.bold(chalk.green('\n✅ All checks passed - ready to deploy!\n')));
  }

  return lines.join('\n');
}
