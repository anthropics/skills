import { CampaignData } from './types';

/**
 * Demo campaign data for testing and development.
 * Replace with your actual Google Sheets integration in production.
 */
export const demoData: CampaignData = {
  project: {
    name: "The New Village",
    client: "Aquilini Development",
    period: "January - March 2025",
    objective: "Teaser → Now Previewing",
    startDate: "2025-01-01",
    endDate: "2025-03-31",
    phases: [
      { name: "Phase 1: Teaser & Register", start: "2025-01-01", end: "2025-02-15" },
      { name: "Phase 2: Now Previewing", start: "2025-02-15", end: "2025-03-31" }
    ]
  },

  budget: {
    total: 79488.53,
    digitalCampaigns: 30650,
    digitalMedia: 18660,
    ooh: 3000,
    broadcast: 3600,
    managementFees: 7128.53,
    projectManagementFees: 6000,
    serviceFees: 10450
  },

  audience: {
    demographics: "Adults 25-45, Greater Vancouver",
    income: "Household income $80K+",
    psychographics: "First-time buyers, young families seeking affordable homeownership",
    locations: "East Side, West End, Mount Pleasant, Burnaby",
    estimatedReach: "2.5M+ impressions"
  },

  platforms: [
    {
      id: "meta",
      name: "Meta Ads",
      color: "#1877F2",
      totalBudget: 13455,
      campaigns: [
        {
          id: "meta-reach-1",
          name: "English Reach Campaign",
          type: "Reach",
          funnelStage: "Awareness",
          objective: "Awareness",
          startDate: "2025-01-01",
          endDate: "2025-02-15",
          dailySpend: 115,
          totalSpend: 5290,
          format: "Awareness Campaign to maximize brand visibility and engagement; optimized for Reach and Impressions",
          status: "Planned",
          targeting: "100% AHI"
        },
        {
          id: "meta-lead-1",
          name: "English Lead Campaign",
          type: "Lead Gen",
          funnelStage: "Conversion",
          objective: "Lead Generation",
          startDate: "2025-02-01",
          endDate: "2025-02-15",
          dailySpend: 115,
          totalSpend: 1725,
          format: "Lead-Gen Campaign to maximize registrations; optimize for Clicks and Form-Fill",
          status: "Planned",
          targeting: "100% TNV"
        },
        {
          id: "meta-reach-2",
          name: "English Reach Campaign (Phase 2)",
          type: "Reach",
          funnelStage: "Awareness",
          objective: "Awareness",
          startDate: "2025-02-15",
          endDate: "2025-03-14",
          dailySpend: 230,
          totalSpend: 6440,
          format: "Awareness Campaign to maximize brand visibility; Phase 2 increased budget",
          status: "Planned",
          targeting: "100% AHI"
        }
      ]
    },
    {
      id: "google",
      name: "Google Ads",
      color: "#4285F4",
      totalBudget: 17195,
      campaigns: [
        {
          id: "google-search-1",
          name: "English Google Search Campaign",
          type: "Search",
          funnelStage: "Conversion",
          objective: "Traffic",
          startDate: "2025-01-01",
          endDate: "2025-02-15",
          dailySpend: 135,
          totalSpend: 6210,
          format: "Targeted Search Campaign for increased online visibility through relevant keyword bidding",
          status: "Planned",
          targeting: "70% AHI / 30% TNV"
        },
        {
          id: "google-demandgen-1",
          name: "English Google Demand Gen",
          type: "Demand Gen",
          funnelStage: "Consideration",
          objective: "Lead Generation",
          startDate: "2025-02-01",
          endDate: "2025-02-15",
          dailySpend: 135,
          totalSpend: 2025,
          format: "Awareness through Google Demand Gen, YouTube and Gmail platforms",
          status: "Planned",
          targeting: "100% TNV"
        },
        {
          id: "google-search-2",
          name: "English Google Search (Phase 2)",
          type: "Search",
          funnelStage: "Conversion",
          objective: "Traffic",
          startDate: "2025-02-15",
          endDate: "2025-03-14",
          dailySpend: 320,
          totalSpend: 8960,
          format: "Targeted Search Campaign for increased visibility; Phase 2 scaled budget",
          status: "Planned",
          targeting: "30% AHI / 70% TNV"
        }
      ]
    },
    {
      id: "programmatic",
      name: "Programmatic (Quantcast)",
      color: "#6B5B4F",
      totalBudget: 6000,
      campaigns: [
        {
          id: "prog-display-1",
          name: "Quantcast Display Campaign",
          type: "Programmatic Display",
          funnelStage: "Awareness",
          objective: "Awareness",
          startDate: "2025-01-01",
          endDate: "2025-03-14",
          dailySpend: 81,
          totalSpend: 6000,
          format: "Programmatic Display with real-time bidding and automated optimization",
          status: "Planned",
          targeting: "80% AHI / 20% TNV → 30% AHI / 70% TNV"
        }
      ]
    },
    {
      id: "bellmedia",
      name: "Bell Media Display",
      color: "#2C2416",
      totalBudget: 8160,
      campaigns: [
        {
          id: "bell-display-1",
          name: "Home Buyers Display Ads",
          type: "Display",
          funnelStage: "Awareness",
          objective: "Awareness",
          startDate: "2025-01-01",
          endDate: "2025-03-14",
          dailySpend: 110,
          totalSpend: 8160,
          format: "Display Ads with Home Buyers + Family + Occupation + Income Targeting",
          status: "Planned",
          targeting: "250,000 impressions per segment"
        }
      ]
    },
    {
      id: "spotify",
      name: "Spotify Audio",
      color: "#1DB954",
      totalBudget: 4500,
      campaigns: [
        {
          id: "spotify-audio-1",
          name: "Audio Ad Campaign",
          type: "Audio",
          funnelStage: "Awareness",
          objective: "Awareness",
          startDate: "2025-01-01",
          endDate: "2025-03-14",
          dailySpend: 61,
          totalSpend: 4500,
          format: "30-second non-skippable spots; Business & Finance, Home & Garden targeting",
          status: "Planned",
          targeting: "Greater Vancouver | Ages 25-45"
        }
      ]
    },
    {
      id: "ooh",
      name: "OOH (Broadsign)",
      color: "#8B7355",
      totalBudget: 3000,
      campaigns: [
        {
          id: "ooh-transit-1",
          name: "Transit & Digital Screens",
          type: "Digital OOH",
          funnelStage: "Awareness",
          objective: "Awareness",
          startDate: "2025-02-15",
          endDate: "2025-03-14",
          dailySpend: 107,
          totalSpend: 3000,
          format: "Transit shelters & digital screens on Cambie corridor, 99 B-Line, East Side",
          status: "Planned",
          targeting: "Geographic focus near transit"
        }
      ]
    },
    {
      id: "radio",
      name: "Radio (Z95.3 FM)",
      color: "#D4A574",
      totalBudget: 3600,
      campaigns: [
        {
          id: "radio-1",
          name: "Radio Ad Campaign",
          type: "Broadcast",
          funnelStage: "Awareness",
          objective: "Awareness",
          startDate: "2025-02-16",
          endDate: "2025-03-08",
          dailySpend: 171,
          totalSpend: 3600,
          format: "40x 30-second ads per week including DashSync by Stingray",
          status: "Planned",
          targeting: "Mass reach - Vancouver market"
        }
      ]
    }
  ],

  results: {
    available: false
  },

  projections: {
    enabled: true,
    generated: "2025-01-01",
    lastUpdated: "2025-01-01",
    byPhase: [
      {
        phaseId: "phase1",
        phaseName: "Phase 1: Teaser & Register",
        startDate: "2025-01-01",
        endDate: "2025-02-15",
        durationDays: 46,
        performance: {
          totalRegistrations: 245,
          totalImpressions: 580000,
          totalClicks: 5040,
          ctr: 0.87,
          cvr: 4.9,
          cpl: 78.00,
          cpc: 3.79,
          budget: 19110
        },
        platformBreakdown: [
          {
            platformId: "meta",
            platformName: "Meta Ads",
            projectedImpressions: 350000,
            projectedClicks: 2975,
            projectedRegistrations: 142,
            projectedCPL: 74.50,
            budget: 10575
          },
          {
            platformId: "google",
            platformName: "Google Ads",
            projectedImpressions: 180000,
            projectedClicks: 1620,
            projectedRegistrations: 103,
            projectedCPL: 82.60,
            budget: 8505
          },
          {
            platformId: "spotify",
            platformName: "Spotify Audio",
            projectedImpressions: 50000,
            projectedClicks: 225,
            projectedRegistrations: null,
            projectedCPL: null,
            budget: 1500
          }
        ],
        funnelBreakdown: {
          awareness: { budget: 9850, budgetPercent: 52, impressions: 520000, clicks: 4420, ctr: 0.85 },
          consideration: { budget: 3200, budgetPercent: 17, clicks: 384, registrations: 10, cvr: 2.6 },
          conversion: { budget: 6060, budgetPercent: 31, clicks: 2910, registrations: 235, cvr: 8.1, cpl: 25.79 }
        }
      },
      {
        phaseId: "phase2",
        phaseName: "Phase 2: Now Previewing",
        startDate: "2025-02-15",
        endDate: "2025-03-31",
        durationDays: 44,
        performance: {
          totalRegistrations: 843,
          totalImpressions: 1920000,
          totalClicks: 16710,
          ctr: 0.87,
          cvr: 5.0,
          cpl: 71.20,
          cpc: 3.61,
          budget: 60378
        },
        platformBreakdown: [
          {
            platformId: "meta",
            platformName: "Meta Ads",
            projectedImpressions: 1150000,
            projectedClicks: 10350,
            projectedRegistrations: 537,
            projectedCPL: 70.20,
            budget: 37680
          },
          {
            platformId: "google",
            platformName: "Google Ads",
            projectedImpressions: 620000,
            projectedClicks: 5580,
            projectedRegistrations: 365,
            projectedCPL: 72.40,
            budget: 26460
          },
          {
            platformId: "spotify",
            platformName: "Spotify Audio",
            projectedImpressions: 250000,
            projectedClicks: 1125,
            projectedRegistrations: null,
            projectedCPL: null,
            budget: 3000
          },
          {
            platformId: "ooh",
            platformName: "OOH",
            projectedImpressions: 125000,
            projectedClicks: null,
            projectedRegistrations: null,
            projectedCPL: null,
            budget: 3000
          },
          {
            platformId: "radio",
            platformName: "Radio",
            projectedImpressions: 175000,
            projectedClicks: null,
            projectedRegistrations: null,
            projectedCPL: null,
            budget: 3600
          }
        ],
        funnelBreakdown: {
          awareness: { budget: 32765, budgetPercent: 54, impressions: 1680000, clicks: 14280, ctr: 0.85 },
          consideration: { budget: 8030, budgetPercent: 13, clicks: 5016, registrations: 125, cvr: 2.5 },
          conversion: { budget: 19583, budgetPercent: 33, clicks: 8745, registrations: 718, cvr: 8.2, cpl: 27.28 }
        }
      }
    ],
    campaignTotal: {
      totalRegistrations: 1088,
      totalImpressions: 2500000,
      totalClicks: 21750,
      avgCtr: 0.87,
      avgCvr: 5.0,
      avgCpl: 73.00,
      avgCpc: 3.65,
      totalBudget: 79488,
      campaignDuration: "January 1 - March 31, 2025",
      durationDays: 90
    },
    benchmarks: {
      meta: {
        awareness: { cpm: 8.50, ctr: 0.85, cvr: 0 },
        consideration: { cpm: 9.20, ctr: 1.20, cvr: 2.5 },
        conversion: { cpm: 12.00, ctr: 1.80, cvr: 5.2 }
      },
      google: {
        awareness: { cpc: 0.95, ctr: 0.75, cvr: 0 },
        consideration: { cpc: 1.85, ctr: 1.50, cvr: 3.2 },
        conversion: { cpc: 2.20, ctr: 2.10, cvr: 6.5 }
      }
    },
    assumptions: [
      "Phase 1 focuses on brand awareness and initial registrations",
      "Phase 2 scales up conversion efforts with increased budget",
      "Based on Vancouver presale condo campaigns, 2024 benchmarks",
      "Meta CPM: $8.50 (Awareness), $9.20 (Consideration), $12.00 (Conversion)",
      "Google Search CPC: $2.20 for high-intent keywords",
      "Average form completion rate (CVR): 4.5-5.5%",
      "Campaign optimizations applied after Week 2",
      "Seasonal adjustment: +8% for January launch window"
    ],
    dataSources: [
      "Periphery Digital historical campaign data (2023-2024)",
      "Vancouver real estate market benchmarks",
      "Meta Ads industry benchmarks (Real Estate vertical)",
      "Google Ads Keyword Planner estimates"
    ]
  }
};
