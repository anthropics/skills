import {
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
  FunnelBreakdown
} from './types';
import { platformConfig, getPlatformConfig } from './platformConfig';

// =============================================================================
// DATA TRANSFORMATION LAYER
// Maps raw Google Sheets data to the dashboard's CampaignData structure
// =============================================================================

export interface RawSheetData {
  campaigns: Record<string, string>[];
  platforms: Record<string, string>[];
  budget: Record<string, string>[];
  project: Record<string, string>[];
  audience?: Record<string, string>[];
  projections?: Record<string, string>[];
}

/**
 * Main transformation function - converts raw sheet data to CampaignData
 */
export function transformSheetData(raw: RawSheetData): CampaignData {
  const project = transformProject(raw.project);
  const budget = transformBudget(raw.budget);
  const audience = transformAudience(raw.audience || []);
  const platforms = transformPlatforms(raw.platforms, raw.campaigns);
  const projections = raw.projections?.length
    ? transformProjections(raw.projections, platforms)
    : undefined;

  return {
    project,
    budget,
    audience,
    platforms,
    projections,
    results: { available: false }
  };
}

/**
 * Transform project data from key-value rows
 * Expected columns: field, value
 */
function transformProject(rows: Record<string, string>[]): Project {
  const getValue = (field: string): string => {
    const row = rows.find(r =>
      r.field?.toLowerCase() === field.toLowerCase()
    );
    return row?.value || '';
  };

  // Parse phases from a JSON string or semicolon-separated format
  const phasesRaw = getValue('phases');
  let phases: Phase[] = [];

  if (phasesRaw) {
    try {
      // Try JSON format first
      phases = JSON.parse(phasesRaw);
    } catch {
      // Fall back to semicolon-separated format: "Phase 1|2025-01-01|2025-02-15;Phase 2|2025-02-15|2025-03-31"
      phases = phasesRaw.split(';').map(p => {
        const [name, start, end] = p.split('|').map(s => s.trim());
        return { name, start, end };
      }).filter(p => p.name && p.start && p.end);
    }
  }

  return {
    name: getValue('name') || 'Untitled Campaign',
    client: getValue('client') || '',
    period: getValue('period') || '',
    objective: getValue('objective') || '',
    startDate: getValue('start_date') || getValue('startdate') || '',
    endDate: getValue('end_date') || getValue('enddate') || '',
    phases
  };
}

/**
 * Transform budget data from category-amount rows
 * Expected columns: category, amount
 */
function transformBudget(rows: Record<string, string>[]): Budget {
  const getAmount = (category: string): number => {
    const row = rows.find(r =>
      r.category?.toLowerCase().includes(category.toLowerCase())
    );
    return parseFloat(row?.amount || '0') || 0;
  };

  const digitalCampaigns = getAmount('digital campaigns') || getAmount('digital_campaigns');
  const digitalMedia = getAmount('digital media') || getAmount('digital_media');
  const ooh = getAmount('ooh') || getAmount('out of home');
  const broadcast = getAmount('broadcast') || getAmount('radio');
  const managementFees = getAmount('management') || getAmount('management_fees');
  const projectManagementFees = getAmount('project management') || getAmount('pm_fees');
  const serviceFees = getAmount('service') || getAmount('service_fees');

  // Calculate total or use explicit total row
  const explicitTotal = getAmount('total');
  const calculatedTotal = digitalCampaigns + digitalMedia + ooh + broadcast +
    managementFees + projectManagementFees + serviceFees;

  return {
    total: explicitTotal || calculatedTotal,
    digitalCampaigns,
    digitalMedia,
    ooh,
    broadcast,
    managementFees,
    projectManagementFees,
    serviceFees
  };
}

/**
 * Transform audience data from key-value rows
 * Expected columns: field, value
 */
function transformAudience(rows: Record<string, string>[]): Audience {
  const getValue = (field: string): string => {
    const row = rows.find(r =>
      r.field?.toLowerCase() === field.toLowerCase()
    );
    return row?.value || '';
  };

  return {
    demographics: getValue('demographics'),
    income: getValue('income'),
    psychographics: getValue('psychographics'),
    locations: getValue('locations') || getValue('geography'),
    estimatedReach: getValue('estimated_reach') || getValue('reach')
  };
}

/**
 * Transform platforms and their campaigns
 * Platforms expected columns: id, name, total_budget
 * Campaigns expected columns: platform_id, campaign_name, type, funnel_stage, etc.
 */
function transformPlatforms(
  platformRows: Record<string, string>[],
  campaignRows: Record<string, string>[]
): Platform[] {
  return platformRows
    .filter(p => p.id)
    .map(p => {
      const platformId = p.id.toLowerCase();
      const config = getPlatformConfig(platformId);

      // Get all campaigns for this platform
      const platformCampaigns = campaignRows
        .filter(c => c.platform_id?.toLowerCase() === platformId)
        .map(c => transformCampaign(c, platformId));

      // Calculate total budget from campaigns if not provided
      const explicitBudget = parseFloat(p.total_budget) || 0;
      const calculatedBudget = platformCampaigns.reduce((sum, c) => sum + c.totalSpend, 0);

      return {
        id: platformId,
        name: p.name || config.name,
        color: config.color,
        totalBudget: explicitBudget || calculatedBudget,
        campaigns: platformCampaigns
      };
    });
}

/**
 * Transform a single campaign row
 */
function transformCampaign(row: Record<string, string>, platformId: string): Campaign {
  const name = row.campaign_name || row.name || 'Unnamed Campaign';

  // Generate ID from platform and name if not provided
  const id = row.campaign_id || row.id ||
    `${platformId}-${name}`.toLowerCase().replace(/[^a-z0-9]+/g, '-');

  // Normalize funnel stage
  const rawStage = (row.funnel_stage || row.stage || 'awareness').toLowerCase();
  let funnelStage: Campaign['funnelStage'] = 'Awareness';
  if (rawStage.includes('consider')) funnelStage = 'Consideration';
  else if (rawStage.includes('conver')) funnelStage = 'Conversion';

  // Normalize status
  const rawStatus = (row.status || 'planned').toLowerCase();
  let status: Campaign['status'] = 'Planned';
  if (rawStatus.includes('active') || rawStatus.includes('live')) status = 'Active';
  else if (rawStatus.includes('pause')) status = 'Paused';
  else if (rawStatus.includes('complete') || rawStatus.includes('ended')) status = 'Completed';

  return {
    id,
    name,
    type: row.type || row.campaign_type || 'Display',
    funnelStage,
    objective: row.objective || '',
    startDate: row.start_date || row.startdate || '',
    endDate: row.end_date || row.enddate || '',
    dailySpend: parseFloat(row.daily_spend || row.dailyspend || '0') || 0,
    totalSpend: parseFloat(row.total_spend || row.totalspend || row.budget || '0') || 0,
    format: row.format || row.ad_format || '',
    status,
    targeting: row.targeting || ''
  };
}

/**
 * Transform projections data
 * This handles both simple and complex projection structures
 */
function transformProjections(
  rows: Record<string, string>[],
  platforms: Platform[]
): Projections | undefined {
  if (!rows.length) return undefined;

  // Check if this is phase-based projections or simple projections
  const hasPhases = rows.some(r => r.phase_id || r.phase_name);

  if (hasPhases) {
    return transformPhaseProjections(rows, platforms);
  }

  return transformSimpleProjections(rows, platforms);
}

/**
 * Transform phase-based projections
 */
function transformPhaseProjections(
  rows: Record<string, string>[],
  platforms: Platform[]
): Projections {
  // Group rows by phase
  const phaseMap = new Map<string, Record<string, string>[]>();

  rows.forEach(row => {
    const phaseId = row.phase_id || 'phase1';
    if (!phaseMap.has(phaseId)) {
      phaseMap.set(phaseId, []);
    }
    phaseMap.get(phaseId)!.push(row);
  });

  const byPhase: ProjectionPhase[] = [];

  phaseMap.forEach((phaseRows, phaseId) => {
    // Get phase metadata from first row
    const firstRow = phaseRows[0];

    // Build platform breakdown
    const platformBreakdown: PlatformBreakdown[] = [];
    platforms.forEach(platform => {
      const platformRow = phaseRows.find(r =>
        r.platform_id?.toLowerCase() === platform.id
      );

      if (platformRow) {
        platformBreakdown.push({
          platformId: platform.id,
          platformName: platform.name,
          projectedImpressions: parseInt(platformRow.impressions || '0') || 0,
          projectedClicks: platformRow.clicks ? parseInt(platformRow.clicks) : null,
          projectedRegistrations: platformRow.registrations ? parseInt(platformRow.registrations) : null,
          projectedCPL: platformRow.cpl ? parseFloat(platformRow.cpl) : null,
          budget: parseFloat(platformRow.budget || '0') || 0
        });
      }
    });

    // Build funnel breakdown
    const funnelBreakdown = buildFunnelBreakdown(phaseRows);

    // Calculate performance totals
    const totalRegistrations = platformBreakdown.reduce(
      (sum, p) => sum + (p.projectedRegistrations || 0), 0
    );
    const totalImpressions = platformBreakdown.reduce(
      (sum, p) => sum + p.projectedImpressions, 0
    );
    const totalClicks = platformBreakdown.reduce(
      (sum, p) => sum + (p.projectedClicks || 0), 0
    );
    const totalBudget = platformBreakdown.reduce(
      (sum, p) => sum + p.budget, 0
    );

    byPhase.push({
      phaseId,
      phaseName: firstRow.phase_name || `Phase ${byPhase.length + 1}`,
      startDate: firstRow.start_date || '',
      endDate: firstRow.end_date || '',
      durationDays: parseInt(firstRow.duration_days || '30') || 30,
      performance: {
        totalRegistrations,
        totalImpressions,
        totalClicks,
        ctr: totalImpressions > 0 ? (totalClicks / totalImpressions) * 100 : 0,
        cvr: totalClicks > 0 ? (totalRegistrations / totalClicks) * 100 : 0,
        cpl: totalRegistrations > 0 ? totalBudget / totalRegistrations : 0,
        cpc: totalClicks > 0 ? totalBudget / totalClicks : 0,
        budget: totalBudget
      },
      platformBreakdown,
      funnelBreakdown
    });
  });

  // Calculate campaign totals
  const campaignTotal = calculateCampaignTotal(byPhase);

  return {
    enabled: true,
    generated: new Date().toISOString().split('T')[0],
    lastUpdated: new Date().toISOString().split('T')[0],
    byPhase,
    campaignTotal,
    benchmarks: {},
    assumptions: [],
    dataSources: []
  };
}

/**
 * Transform simple (non-phase) projections
 */
function transformSimpleProjections(
  rows: Record<string, string>[],
  platforms: Platform[]
): Projections {
  // Create a single phase from all data
  const platformBreakdown: PlatformBreakdown[] = [];

  platforms.forEach(platform => {
    const platformRow = rows.find(r =>
      r.platform_id?.toLowerCase() === platform.id
    );

    if (platformRow) {
      platformBreakdown.push({
        platformId: platform.id,
        platformName: platform.name,
        projectedImpressions: parseInt(platformRow.impressions || '0') || 0,
        projectedClicks: platformRow.clicks ? parseInt(platformRow.clicks) : null,
        projectedRegistrations: platformRow.registrations ? parseInt(platformRow.registrations) : null,
        projectedCPL: platformRow.cpl ? parseFloat(platformRow.cpl) : null,
        budget: parseFloat(platformRow.budget || '0') || platform.totalBudget
      });
    }
  });

  const funnelBreakdown = buildFunnelBreakdown(rows);

  const totalRegistrations = platformBreakdown.reduce(
    (sum, p) => sum + (p.projectedRegistrations || 0), 0
  );
  const totalImpressions = platformBreakdown.reduce(
    (sum, p) => sum + p.projectedImpressions, 0
  );
  const totalClicks = platformBreakdown.reduce(
    (sum, p) => sum + (p.projectedClicks || 0), 0
  );
  const totalBudget = platformBreakdown.reduce(
    (sum, p) => sum + p.budget, 0
  );

  const phase: ProjectionPhase = {
    phaseId: 'main',
    phaseName: 'Full Campaign',
    startDate: '',
    endDate: '',
    durationDays: 90,
    performance: {
      totalRegistrations,
      totalImpressions,
      totalClicks,
      ctr: totalImpressions > 0 ? (totalClicks / totalImpressions) * 100 : 0,
      cvr: totalClicks > 0 ? (totalRegistrations / totalClicks) * 100 : 0,
      cpl: totalRegistrations > 0 ? totalBudget / totalRegistrations : 0,
      cpc: totalClicks > 0 ? totalBudget / totalClicks : 0,
      budget: totalBudget
    },
    platformBreakdown,
    funnelBreakdown
  };

  return {
    enabled: true,
    generated: new Date().toISOString().split('T')[0],
    lastUpdated: new Date().toISOString().split('T')[0],
    byPhase: [phase],
    campaignTotal: {
      totalRegistrations,
      totalImpressions,
      totalClicks,
      avgCtr: phase.performance.ctr,
      avgCvr: phase.performance.cvr,
      avgCpl: phase.performance.cpl,
      avgCpc: phase.performance.cpc,
      totalBudget,
      campaignDuration: 'Full Campaign',
      durationDays: 90
    },
    benchmarks: {},
    assumptions: [],
    dataSources: []
  };
}

/**
 * Build funnel breakdown from projection rows
 */
function buildFunnelBreakdown(rows: Record<string, string>[]): {
  awareness: FunnelBreakdown;
  consideration: FunnelBreakdown;
  conversion: FunnelBreakdown;
} {
  const getFunnelData = (stage: string): FunnelBreakdown => {
    const stageRow = rows.find(r =>
      r.funnel_stage?.toLowerCase().includes(stage)
    );

    if (!stageRow) {
      return { budget: 0, budgetPercent: 0 };
    }

    return {
      budget: parseFloat(stageRow.budget || '0') || 0,
      budgetPercent: parseInt(stageRow.budget_percent || '0') || 0,
      impressions: stageRow.impressions ? parseInt(stageRow.impressions) : undefined,
      clicks: stageRow.clicks ? parseInt(stageRow.clicks) : undefined,
      ctr: stageRow.ctr ? parseFloat(stageRow.ctr) : undefined,
      registrations: stageRow.registrations ? parseInt(stageRow.registrations) : undefined,
      cvr: stageRow.cvr ? parseFloat(stageRow.cvr) : undefined,
      cpl: stageRow.cpl ? parseFloat(stageRow.cpl) : undefined
    };
  };

  return {
    awareness: getFunnelData('awareness'),
    consideration: getFunnelData('consideration'),
    conversion: getFunnelData('conversion')
  };
}

/**
 * Calculate campaign totals from phases
 */
function calculateCampaignTotal(phases: ProjectionPhase[]) {
  const totalRegistrations = phases.reduce(
    (sum, p) => sum + p.performance.totalRegistrations, 0
  );
  const totalImpressions = phases.reduce(
    (sum, p) => sum + p.performance.totalImpressions, 0
  );
  const totalClicks = phases.reduce(
    (sum, p) => sum + p.performance.totalClicks, 0
  );
  const totalBudget = phases.reduce(
    (sum, p) => sum + p.performance.budget, 0
  );
  const totalDays = phases.reduce(
    (sum, p) => sum + p.durationDays, 0
  );

  return {
    totalRegistrations,
    totalImpressions,
    totalClicks,
    avgCtr: totalImpressions > 0 ? (totalClicks / totalImpressions) * 100 : 0,
    avgCvr: totalClicks > 0 ? (totalRegistrations / totalClicks) * 100 : 0,
    avgCpl: totalRegistrations > 0 ? totalBudget / totalRegistrations : 0,
    avgCpc: totalClicks > 0 ? totalBudget / totalClicks : 0,
    totalBudget,
    campaignDuration: phases.length > 0
      ? `${phases[0].phaseName} - ${phases[phases.length - 1].phaseName}`
      : 'Full Campaign',
    durationDays: totalDays
  };
}
