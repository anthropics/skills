import { ValidationResult } from '../types.js';

export function formatJsonReport(result: ValidationResult): string {
  return JSON.stringify(result, null, 2);
}
