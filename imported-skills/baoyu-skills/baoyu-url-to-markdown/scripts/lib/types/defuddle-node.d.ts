declare module "defuddle/node" {
  export interface DefuddleResponse {
    content?: string;
    title?: string;
    description?: string;
    author?: string;
    published?: string;
    image?: string;
    language?: string;
  }

  export interface DefuddleOptions {
    markdown?: boolean;
  }

  export function Defuddle(
    input:
      | Document
      | string
      | {
          window: {
            document: Document;
            location: {
              href: string;
            };
          };
        },
    url?: string,
    options?: DefuddleOptions,
  ): Promise<DefuddleResponse>;
}
