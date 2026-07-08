export interface CheckConfig {
  enabled: boolean;
  command?: string;
  timeoutMs: number;
  onFail: 'block' | 'warn';
  coverageThreshold?: {
    lines: number;
    functions: number;
    branches: number;
  };
  projects?: string[];
}

export interface PreDeployConfig {
  name: string;
  version: string;
  description: string;
  checks: Record<string, CheckConfig>;
  skipOnBranches?: string[];
  parallel?: boolean;
  reportFormat?: 'console' | 'json';
  exitCode?: number;
}

export interface CheckResult {
  name: string;
  success: boolean;
  duration: number;
  output?: string;
  error?: string;
  severity: 'error' | 'warning';
}

export interface ValidationResult {
  success: boolean;
  checks: CheckResult[];
  duration: number;
  errors: string[];
  timestamp: string;
}

export interface CLIOptions {
  config?: string;
  format?: 'console' | 'json';
  skip?: string;
}
