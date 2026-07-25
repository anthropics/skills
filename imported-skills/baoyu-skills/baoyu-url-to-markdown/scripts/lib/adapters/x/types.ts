export type JsonObject = Record<string, unknown>;

export interface XUser {
  name?: string;
  screenName?: string;
}

export interface XMedia {
  type: string;
  url: string;
  alt?: string;
}

export interface XQuotedTweet {
  id: string;
  author?: string;
  authorName?: string;
  text: string;
  url: string;
  media: XMedia[];
}

export interface XTweet {
  id: string;
  author?: string;
  authorName?: string;
  text: string;
  likes: number;
  retweets: number;
  replies: number;
  createdAt?: string;
  inReplyTo?: string;
  url: string;
  media: XMedia[];
  quotedTweet?: XQuotedTweet;
}
