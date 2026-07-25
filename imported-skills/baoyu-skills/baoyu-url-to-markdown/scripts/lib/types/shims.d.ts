declare module "turndown" {
  export interface TurndownOptions {
    codeBlockStyle?: "indented" | "fenced";
    headingStyle?: "setext" | "atx";
    bulletListMarker?: "-" | "*" | "+";
  }

  export default class TurndownService {
    constructor(options?: TurndownOptions);
    use(plugin: unknown): void;
    turndown(input: string): string;
  }
}

declare module "turndown-plugin-gfm" {
  export const gfm: unknown;
}
