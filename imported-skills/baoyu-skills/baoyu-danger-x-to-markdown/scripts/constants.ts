import { resolveXToMarkdownChromeProfileDir } from "./paths.js";

export const DEFAULT_BEARER_TOKEN =
  "Bearer AAAAAAAAAAAAAAAAAAAAANRILgAAAAAAnNwIzUejRCOuH5E6I8xnZz4puTs%3D1Zv7ttfk8LF81IUq16cHjhLTvJu4FA33AGWWjCpTnA";
export const DEFAULT_USER_AGENT =
  "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36";
export const X_LOGIN_URL = "https://x.com/home";
export const X_USER_DATA_DIR = resolveXToMarkdownChromeProfileDir();

export const X_COOKIE_NAMES = ["auth_token", "ct0", "gt", "twid"] as const;
export const X_REQUIRED_COOKIES = ["auth_token", "ct0"] as const;

export const FALLBACK_QUERY_ID = "id8pHQbQi7eZ6P9mA1th1Q";
export const FALLBACK_FEATURE_SWITCHES = [
  "profile_label_improvements_pcf_label_in_post_enabled",
  "responsive_web_profile_redirect_enabled",
  "rweb_tipjar_consumption_enabled",
  "verified_phone_label_enabled",
  "responsive_web_graphql_skip_user_profile_image_extensions_enabled",
  "responsive_web_graphql_timeline_navigation_enabled",
];
export const FALLBACK_FIELD_TOGGLES = ["withPayments", "withAuxiliaryUserLabels"];

export const FALLBACK_TWEET_QUERY_ID = "HJ9lpOL-ZlOk5CkCw0JW6Q";
export const FALLBACK_TWEET_FEATURE_SWITCHES = [
  "creator_subscriptions_tweet_preview_api_enabled",
  "premium_content_api_read_enabled",
  "communities_web_enable_tweet_community_results_fetch",
  "c9s_tweet_anatomy_moderator_badge_enabled",
  "responsive_web_grok_analyze_button_fetch_trends_enabled",
  "responsive_web_grok_analyze_post_followups_enabled",
  "responsive_web_jetfuel_frame",
  "responsive_web_grok_share_attachment_enabled",
  "responsive_web_grok_annotations_enabled",
  "articles_preview_enabled",
  "responsive_web_edit_tweet_api_enabled",
  "graphql_is_translatable_rweb_tweet_is_translatable_enabled",
  "view_counts_everywhere_api_enabled",
  "longform_notetweets_consumption_enabled",
  "responsive_web_twitter_article_tweet_consumption_enabled",
  "tweet_awards_web_tipping_enabled",
  "responsive_web_grok_show_grok_translated_post",
  "responsive_web_grok_analysis_button_from_backend",
  "post_ctas_fetch_enabled",
  "creator_subscriptions_quote_tweet_preview_enabled",
  "freedom_of_speech_not_reach_fetch_enabled",
  "standardized_nudges_misinfo",
  "tweet_with_visibility_results_prefer_gql_limited_actions_policy_enabled",
  "longform_notetweets_rich_text_read_enabled",
  "longform_notetweets_inline_media_enabled",
  "profile_label_improvements_pcf_label_in_post_enabled",
  "responsive_web_profile_redirect_enabled",
  "rweb_tipjar_consumption_enabled",
  "verified_phone_label_enabled",
  "responsive_web_grok_image_annotation_enabled",
  "responsive_web_grok_imagine_annotation_enabled",
  "responsive_web_grok_community_note_auto_translation_is_enabled",
  "responsive_web_graphql_skip_user_profile_image_extensions_enabled",
  "responsive_web_graphql_timeline_navigation_enabled",
  "responsive_web_enhance_cards_enabled",
];
export const FALLBACK_TWEET_FIELD_TOGGLES = [
  "withArticleRichContentState",
  "withArticlePlainText",
  "withGrokAnalyze",
  "withDisallowedReplyControls",
  "withPayments",
  "withAuxiliaryUserLabels",
];

export const FALLBACK_TWEET_DETAIL_QUERY_ID = "_8aYOgEDz35BrBcBal1-_w";
export const FALLBACK_TWEET_DETAIL_FEATURE_SWITCHES = [
  "rweb_video_screen_enabled",
  "profile_label_improvements_pcf_label_in_post_enabled",
  "rweb_tipjar_consumption_enabled",
  "verified_phone_label_enabled",
  "creator_subscriptions_tweet_preview_api_enabled",
  "responsive_web_graphql_timeline_navigation_enabled",
  "responsive_web_graphql_skip_user_profile_image_extensions_enabled",
  "premium_content_api_read_enabled",
  "communities_web_enable_tweet_community_results_fetch",
  "c9s_tweet_anatomy_moderator_badge_enabled",
  "responsive_web_grok_analyze_button_fetch_trends_enabled",
  "responsive_web_grok_analyze_post_followups_enabled",
  "responsive_web_jetfuel_frame",
  "responsive_web_grok_share_attachment_enabled",
  "articles_preview_enabled",
  "responsive_web_edit_tweet_api_enabled",
  "graphql_is_translatable_rweb_tweet_is_translatable_enabled",
  "view_counts_everywhere_api_enabled",
  "longform_notetweets_consumption_enabled",
  "responsive_web_twitter_article_tweet_consumption_enabled",
  "tweet_awards_web_tipping_enabled",
  "responsive_web_grok_show_grok_translated_post",
  "responsive_web_grok_analysis_button_from_backend",
  "creator_subscriptions_quote_tweet_preview_enabled",
  "freedom_of_speech_not_reach_fetch_enabled",
  "standardized_nudges_misinfo",
  "tweet_with_visibility_results_prefer_gql_limited_actions_policy_enabled",
  "longform_notetweets_rich_text_read_enabled",
  "longform_notetweets_inline_media_enabled",
  "responsive_web_grok_image_annotation_enabled",
  "responsive_web_enhance_cards_enabled",
];
export const FALLBACK_TWEET_DETAIL_FEATURE_DEFAULTS: Record<string, boolean> = {
  rweb_video_screen_enabled: false,
  profile_label_improvements_pcf_label_in_post_enabled: true,
  rweb_tipjar_consumption_enabled: true,
  verified_phone_label_enabled: false,
  creator_subscriptions_tweet_preview_api_enabled: true,
  responsive_web_graphql_timeline_navigation_enabled: true,
  responsive_web_graphql_skip_user_profile_image_extensions_enabled: false,
  premium_content_api_read_enabled: false,
  communities_web_enable_tweet_community_results_fetch: true,
  c9s_tweet_anatomy_moderator_badge_enabled: true,
  responsive_web_grok_analyze_button_fetch_trends_enabled: false,
  responsive_web_grok_analyze_post_followups_enabled: true,
  responsive_web_jetfuel_frame: false,
  responsive_web_grok_share_attachment_enabled: true,
  articles_preview_enabled: true,
  responsive_web_edit_tweet_api_enabled: true,
  graphql_is_translatable_rweb_tweet_is_translatable_enabled: true,
  view_counts_everywhere_api_enabled: true,
  longform_notetweets_consumption_enabled: true,
  responsive_web_twitter_article_tweet_consumption_enabled: true,
  tweet_awards_web_tipping_enabled: false,
  responsive_web_grok_show_grok_translated_post: false,
  responsive_web_grok_analysis_button_from_backend: true,
  creator_subscriptions_quote_tweet_preview_enabled: false,
  freedom_of_speech_not_reach_fetch_enabled: true,
  standardized_nudges_misinfo: true,
  tweet_with_visibility_results_prefer_gql_limited_actions_policy_enabled: true,
  longform_notetweets_rich_text_read_enabled: true,
  longform_notetweets_inline_media_enabled: true,
  responsive_web_grok_image_annotation_enabled: true,
  responsive_web_enhance_cards_enabled: false,
};
export const FALLBACK_TWEET_DETAIL_FIELD_TOGGLES = [
  "withArticleRichContentState",
  "withArticlePlainText",
  "withGrokAnalyze",
  "withDisallowedReplyControls",
];
