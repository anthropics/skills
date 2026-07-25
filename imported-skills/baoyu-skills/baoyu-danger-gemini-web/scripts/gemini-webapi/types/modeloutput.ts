import type { Image } from './image.js';
import type { Candidate } from './candidate.js';

export class ModelOutput {
  public metadata: string[];
  public candidates: Candidate[];
  public chosen: number;

  constructor(params: { metadata: string[]; candidates: Candidate[]; chosen?: number }) {
    this.metadata = params.metadata;
    this.candidates = params.candidates;
    this.chosen = params.chosen ?? 0;
  }

  toString(): string {
    return this.text;
  }

  get text(): string {
    return this.candidates[this.chosen]?.text ?? '';
  }

  get thoughts(): string | null {
    return this.candidates[this.chosen]?.thoughts ?? null;
  }

  get images(): Image[] {
    return this.candidates[this.chosen]?.images ?? [];
  }

  get rcid(): string {
    return this.candidates[this.chosen]?.rcid ?? '';
  }
}

