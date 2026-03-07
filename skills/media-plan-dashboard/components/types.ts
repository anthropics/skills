// =============================================================================
// TYPE DEFINITIONS - Media Plan Dashboard
// =============================================================================

export interface Phase {
  name: string;
  start: string;
  end: string;
}

export interface Project {
  name: string;
  client: string;
  period: string;
  objective: string;
  startDate: string;
  endDate: string;
  phases: Phase[];
}

export interface Budget {
  total: number;
  digitalCampaigns: number;
  digitalMedia: number;
  ooh: number;
  broadcast: number;
  managementFees: number;
  projectManagementFees: number;
  serviceFees: number;
}

export interface Audience {
  demographics: string;
  income: string;
  psychographics: string;
  locations: string;
  estimatedReach: string;
}

export interface Campaign {
  id: string;
  name: string;
  type: string;
  funnelStage: 'Awareness' | 'Consideration' | 'Conversion';
  objective: string;
  startDate: string;
  endDate: string;
  dailySpend: number;
  totalSpend: number;
  format: string;
  status: 'Planned' | 'Active' | 'Paused' | 'Completed';
  targeting?: string;
}

export interface Platform {
  id: string;
  name: string;
  color: string;
  totalBudget: number;
  campaigns: Campaign[];
}

export interface PlatformBreakdown {
  platformId: string;
  platformName: string;
  projectedImpressions: number;
  projectedClicks: number | null;
  projectedRegistrations: number | null;
  projectedCPL: number | null;
  budget: number;
}

export interface FunnelBreakdown {
  budget: number;
  budgetPercent: number;
  impressions?: number;
  clicks?: number;
  ctr?: number;
  registrations?: number;
  cvr?: number;
  cpl?: number;
}

export interface PhasePerformance {
  totalRegistrations: number;
  totalImpressions: number;
  totalClicks: number;
  ctr: number;
  cvr: number;
  cpl: number;
  cpc: number;
  budget: number;
}

export interface ProjectionPhase {
  phaseId: string;
  phaseName: string;
  startDate: string;
  endDate: string;
  durationDays: number;
  performance: PhasePerformance;
  platformBreakdown: PlatformBreakdown[];
  funnelBreakdown: {
    awareness: FunnelBreakdown;
    consideration: FunnelBreakdown;
    conversion: FunnelBreakdown;
  };
}

export interface CampaignTotal {
  totalRegistrations: number;
  totalImpressions: number;
  totalClicks: number;
  avgCtr: number;
  avgCvr: number;
  avgCpl: number;
  avgCpc: number;
  totalBudget: number;
  campaignDuration: string;
  durationDays: number;
}

export interface Projections {
  enabled: boolean;
  generated: string;
  lastUpdated: string;
  byPhase: ProjectionPhase[];
  campaignTotal: CampaignTotal;
  benchmarks: Record<string, Record<string, { cpm?: number; cpc?: number; ctr: number; cvr: number }>>;
  assumptions: string[];
  dataSources: string[];
}

export interface Results {
  available: boolean;
  // Extend with actual results data when available
}

export interface CampaignData {
  project: Project;
  budget: Budget;
  audience: Audience;
  platforms: Platform[];
  projections?: Projections;
  results?: Results;
}

export interface PlatformConfig {
  name: string;
  logo?: string;
  emoji?: string;
  color: string;
  altText?: string;
}

export interface FunnelStage {
  id: 'awareness' | 'consideration' | 'conversion';
  name: string;
  subtitle: string;
  color: string;
  icon: React.ComponentType<{ size?: number }>;
  objective: string;
  metrics: string[];
  description: string;
  rationale: string;
}
