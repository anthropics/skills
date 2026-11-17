/**
 * Media Plan Dashboard Component Library
 *
 * A complete solution for building media plan dashboards
 * that sync with Google Sheets.
 */

// Main dashboard component
export { default as MediaPlanDashboard } from './MediaPlanDashboard';

// Google Sheets integration
export { useGoogleSheets, generatePublishedUrls } from './useGoogleSheets';

// Data transformation utilities
export { transformSheetData } from './dataTransform';
export type { RawSheetData } from './dataTransform';

// Platform configuration
export { platformConfig, getPlatformConfig } from './platformConfig';

// Type definitions
export type {
  CampaignData,
  Campaign,
  Platform,
  Budget,
  Audience,
  Phase,
  Project,
  Projections,
  ProjectionPhase,
  PlatformBreakdown,
  FunnelBreakdown,
  CampaignTotal,
  Results,
  PlatformConfig,
  FunnelStage
} from './types';

// Demo data for development
export { demoData } from './demoData';
