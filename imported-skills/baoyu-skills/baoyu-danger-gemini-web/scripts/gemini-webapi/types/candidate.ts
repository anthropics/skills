import { GeneratedImage, type Image, WebImage } from './image.js';

function decode_html(s: string | null | undefined): string | null | undefined {
  if (s == null) return s;
  return s
    .replace(/&amp;/g, '&')
    .replace(/&lt;/g, '<')
    .replace(/&gt;/g, '>')
    .replace(/&quot;/g, '"')
    .replace(/&apos;/g, "'")
    .replace(/&#39;/g, "'")
    .replace(/&nbsp;/g, ' ')
    .replace(/&#x([0-9a-fA-F]+);/g, (_, hex) => String.fromCodePoint(parseInt(hex, 16)))
    .replace(/&#(\d+);/g, (_, dec) => String.fromCodePoint(parseInt(dec, 10)));
}

export class Candidate {
  public rcid: string;
  public text: string;
  public thoughts: string | null;
  public web_images: WebImage[];
  public generated_images: GeneratedImage[];

  constructor(params: {
    rcid: string;
    text: string;
    thoughts?: string | null;
    web_images?: WebImage[];
    generated_images?: GeneratedImage[];
  }) {
    this.rcid = params.rcid;
    this.text = decode_html(params.text) ?? '';
    this.thoughts = decode_html(params.thoughts) ?? null;
    this.web_images = params.web_images ?? [];
    this.generated_images = params.generated_images ?? [];
  }

  toString(): string {
    return this.text;
  }

  get images(): Image[] {
    return [...this.web_images, ...this.generated_images];
  }
}
