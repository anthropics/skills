#!/usr/bin/env node

import { readFileSync } from 'fs';
import { resolve } from 'path';
import { Command } from 'commander';
import { PreDeployValidator } from './index.js';
import { formatConsoleReport } from './reporters/console.js';
import { formatJsonReport } from './reporters/json.js';
import { PreDeployConfig, CLIOptions } from './types.js';

const program = new Command();

program
  .name('pre-deploy-validator')
  .description('Standardized pre-deployment quality gates for Node.js/Next.js projects')
  .version('1.0.0')
  .option('-c, --config <path>', 'Path to config file (.pdv.json)', '.pdv.json')
  .option('-f, --format <format>', 'Output format (console|json)', 'console')
  .option('-s, --skip <checks>', 'Comma-separated checks to skip')
  .parse(process.argv);

async function main() {
  try {
    const options = program.opts<CLIOptions>();
    const configPath = resolve(options.config || '.pdv.json');

    let config: PreDeployConfig;
    try {
      const configContent = readFileSync(configPath, 'utf-8');
      config = JSON.parse(configContent);
    } catch {
      console.error(`Error: Could not read config file at ${configPath}`);
      process.exit(1);
    }

    // Skip checks if specified
    if (options.skip) {
      const skipChecks = options.skip.split(',').map((s) => s.trim());
      skipChecks.forEach((check) => {
        if (config.checks[check]) {
          config.checks[check].enabled = false;
        }
      });
    }

    const validator = new PreDeployValidator(config);
    const result = await validator.runChecks();

    // Format and output report
    const format = (options.format || 'console') as 'console' | 'json';
    const report = format === 'json' ? formatJsonReport(result) : formatConsoleReport(result);
    console.log(report);

    // Exit with appropriate code
    if (!result.success) {
      process.exit(config.exitCode || 1);
    }
  } catch (error) {
    console.error('Unexpected error:', error);
    process.exit(1);
  }
}

main();
