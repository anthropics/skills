export type CookieLike = {
  name?: string;
  value?: string;
  domain?: string;
  path?: string;
  url?: string;
};

export type ArticleQueryInfo = {
  queryId: string;
  featureSwitches: string[];
  fieldToggles: string[];
  html: string;
};

export type ArticleEntityRange = {
  key?: number;
  offset?: number;
  length?: number;
};

export type ArticleBlock = {
  type?: string;
  text?: string;
  entityRanges?: ArticleEntityRange[];
};

export type ArticleEntityMapMediaItem = {
  mediaId?: string;
  media_id?: string;
  localMediaId?: string;
};

export type ArticleEntityMapEntry = {
  key?: string;
  value?: {
    type?: string;
    mutability?: string;
    data?: {
      caption?: string;
      markdown?: string;
      mediaItems?: ArticleEntityMapMediaItem[];
      url?: string;
      tweetId?: string;
    };
  };
};

export type ArticleContentState = {
  blocks?: ArticleBlock[];
  entityMap?: Record<string, ArticleEntityMapEntry>;
};

export type ArticleMediaInfo = {
  __typename?: string;
  original_img_url?: string;
  preview_image?: {
    original_img_url?: string;
  };
  variants?: Array<{
    content_type?: string;
    url?: string;
    bit_rate?: number;
  }>;
};

export type ArticleMediaEntity = {
  media_id?: string;
  media_info?: ArticleMediaInfo;
};

export type ArticleEntity = {
  title?: string;
  plain_text?: string;
  preview_text?: string;
  content_state?: ArticleContentState;
  cover_media?: {
    media_info?: ArticleMediaInfo;
  };
  media_entities?: ArticleMediaEntity[];
};
