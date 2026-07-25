export type ContentBlock =
  | {
      type: "paragraph";
      text: string;
    }
  | {
      type: "heading";
      depth: number;
      text: string;
    }
  | {
      type: "list";
      ordered: boolean;
      items: string[];
    }
  | {
      type: "quote";
      text: string;
    }
  | {
      type: "code";
      code: string;
      language?: string;
    }
  | {
      type: "image";
      url: string;
      alt?: string;
    }
  | {
      type: "html";
      html: string;
    }
  | {
      type: "markdown";
      markdown: string;
    };

export interface ExtractedDocument {
  url: string;
  requestedUrl?: string;
  canonicalUrl?: string;
  title?: string;
  author?: string;
  siteName?: string;
  publishedAt?: string;
  summary?: string;
  content: ContentBlock[];
  metadata?: Record<string, unknown>;
  adapter?: string;
}
