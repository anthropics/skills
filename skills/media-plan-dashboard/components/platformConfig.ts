// =============================================================================
// PLATFORM CONFIGURATION - Logos, Colors, and Fallbacks
// =============================================================================

import { PlatformConfig } from './types';

export const platformConfig: Record<string, PlatformConfig> = {
  'meta': {
    name: 'Meta Ads',
    logo: 'https://cdn.simpleicons.org/meta/1877F2',
    color: '#1877F2',
    altText: 'Meta logo'
  },
  'facebook': {
    name: 'Facebook',
    logo: 'https://cdn.simpleicons.org/facebook/1877F2',
    color: '#1877F2',
    altText: 'Facebook logo'
  },
  'instagram': {
    name: 'Instagram',
    logo: 'https://cdn.simpleicons.org/instagram/E4405F',
    color: '#E4405F',
    altText: 'Instagram logo'
  },
  'google': {
    name: 'Google Ads',
    logo: 'https://cdn.simpleicons.org/googleads/4285F4',
    color: '#4285F4',
    altText: 'Google Ads logo'
  },
  'linkedin': {
    name: 'LinkedIn',
    logo: 'https://cdn.simpleicons.org/linkedin/0A66C2',
    color: '#0A66C2',
    altText: 'LinkedIn logo'
  },
  'spotify': {
    name: 'Spotify Audio',
    logo: 'https://cdn.simpleicons.org/spotify/1DB954',
    color: '#1DB954',
    altText: 'Spotify logo'
  },
  'youtube': {
    name: 'YouTube',
    logo: 'https://cdn.simpleicons.org/youtube/FF0000',
    color: '#FF0000',
    altText: 'YouTube logo'
  },
  'tiktok': {
    name: 'TikTok',
    logo: 'https://cdn.simpleicons.org/tiktok/000000',
    color: '#000000',
    altText: 'TikTok logo'
  },
  'twitter': {
    name: 'Twitter/X',
    logo: 'https://cdn.simpleicons.org/x/000000',
    color: '#000000',
    altText: 'X logo'
  },
  'pinterest': {
    name: 'Pinterest',
    logo: 'https://cdn.simpleicons.org/pinterest/E60023',
    color: '#E60023',
    altText: 'Pinterest logo'
  },
  'snapchat': {
    name: 'Snapchat',
    logo: 'https://cdn.simpleicons.org/snapchat/FFFC00',
    color: '#FFFC00',
    altText: 'Snapchat logo'
  },
  'reddit': {
    name: 'Reddit',
    logo: 'https://cdn.simpleicons.org/reddit/FF4500',
    color: '#FF4500',
    altText: 'Reddit logo'
  },
  'amazon': {
    name: 'Amazon Ads',
    logo: 'https://cdn.simpleicons.org/amazon/FF9900',
    color: '#FF9900',
    altText: 'Amazon logo'
  },
  'microsoft': {
    name: 'Microsoft Ads',
    logo: 'https://cdn.simpleicons.org/microsoft/00A4EF',
    color: '#00A4EF',
    altText: 'Microsoft logo'
  },
  'quantcast': {
    name: 'Quantcast',
    logo: 'https://cdn.simpleicons.org/quantcast/000000',
    color: '#6B5B4F',
    altText: 'Quantcast logo'
  },
  // Platforms without standard logos - use emoji fallbacks
  'programmatic': {
    name: 'Programmatic',
    emoji: '🎯',
    color: '#6B5B4F'
  },
  'bellmedia': {
    name: 'Bell Media',
    emoji: '📺',
    color: '#2C2416'
  },
  'ooh': {
    name: 'Out of Home',
    emoji: '🚏',
    color: '#8B7355'
  },
  'dooh': {
    name: 'Digital OOH',
    emoji: '📺',
    color: '#2C2416'
  },
  'radio': {
    name: 'Radio',
    emoji: '📻',
    color: '#D4A574'
  },
  'podcast': {
    name: 'Podcast',
    emoji: '🎙️',
    color: '#8B7355'
  },
  'display': {
    name: 'Display Network',
    emoji: '🖼️',
    color: '#6B5B4F'
  },
  'email': {
    name: 'Email Marketing',
    emoji: '✉️',
    color: '#8B7355'
  },
  'ctv': {
    name: 'Connected TV',
    emoji: '📺',
    color: '#4A3C2A'
  },
  'native': {
    name: 'Native Ads',
    emoji: '📰',
    color: '#6B5B4F'
  },
  'affiliate': {
    name: 'Affiliate',
    emoji: '🤝',
    color: '#8B7355'
  },
  'influencer': {
    name: 'Influencer',
    emoji: '⭐',
    color: '#D4A574'
  },
  'print': {
    name: 'Print',
    emoji: '📰',
    color: '#4A3C2A'
  },
  'direct-mail': {
    name: 'Direct Mail',
    emoji: '📬',
    color: '#6B5B4F'
  }
};

// Helper to get platform config with fallback
export function getPlatformConfig(platformId: string): PlatformConfig {
  const id = platformId?.toLowerCase();
  return platformConfig[id] || {
    name: platformId || 'Unknown',
    emoji: '❓',
    color: '#888888'
  };
}
