import React, { useState, useMemo } from 'react';
import {
  LineChart, Line, BarChart, Bar, XAxis, YAxis, Tooltip,
  ResponsiveContainer, AreaChart, Area, PieChart, Pie, Cell
} from 'recharts';
import {
  TrendingUp, TrendingDown, ChevronDown, ChevronRight, Info,
  Target, Users, DollarSign, Eye, Calendar, Layers, ArrowRight,
  X, BarChart3, Clock, CheckCircle, Circle, PlayCircle, PauseCircle,
  ChevronUp, Filter, Lock, MousePointer, Percent, AlertTriangle
} from 'lucide-react';
import { CampaignData, Campaign, Platform, FunnelStage } from './types';
import { platformConfig } from './platformConfig';

// =============================================================================
// FUNNEL STAGE DEFINITIONS
// =============================================================================
const funnelStages: FunnelStage[] = [
  {
    id: "awareness",
    name: "Awareness",
    subtitle: "Top of Funnel",
    color: "#D4A574",
    icon: Eye,
    objective: "Brand discovery, reach, and visibility",
    metrics: ["CPM", "Impressions", "Reach", "Video Completion Rate"],
    description: "Introduce your development to qualified audiences through broad reach campaigns. This stage builds initial recognition and captures attention from potential buyers who match your target demographics.",
    rationale: "We prioritize efficient reach (CPM) while maintaining quality through precise targeting. High-impact visual content creates memorable first impressions that set the foundation for consideration."
  },
  {
    id: "consideration",
    name: "Consideration",
    subtitle: "Middle of Funnel",
    color: "#8B7355",
    icon: Users,
    objective: "Nurturing, engagement, and intent building",
    metrics: ["CTR", "Engagement Rate", "Time on Site", "Page Views"],
    description: "Re-engage interested audiences with deeper content that addresses questions and builds desire. Retargeting campaigns keep your development top-of-mind during the research phase.",
    rationale: "Warm audiences who've shown initial interest receive tailored messaging that advances them toward action. Multi-touch nurturing builds the trust needed for high-consideration real estate decisions."
  },
  {
    id: "conversion",
    name: "Conversion",
    subtitle: "Bottom of Funnel",
    color: "#4A7C59",
    icon: Target,
    objective: "Lead capture, registration, and sales handoff",
    metrics: ["CPA", "Registration Rate", "CVR", "Cost per Registration"],
    description: "Capture high-intent prospects through optimized lead generation campaigns. Search intent and direct response tactics connect with buyers ready to take the next step.",
    rationale: "Bottom-funnel campaigns focus on efficiency and quality. We optimize for cost-per-registration while ensuring leads meet qualification criteria for your sales team."
  }
];

// =============================================================================
// UTILITY FUNCTIONS
// =============================================================================
const formatCurrency = (value: number): string => {
  if (value >= 1000) return `$${(value / 1000).toFixed(1)}K`;
  return `$${value.toLocaleString()}`;
};

const formatFullCurrency = (value: number): string => {
  return `$${value.toLocaleString(undefined, { minimumFractionDigits: 2, maximumFractionDigits: 2 })}`;
};

const formatDate = (dateStr: string, format: 'short' | 'long' = 'short'): string => {
  const date = new Date(dateStr);
  if (format === 'short') return date.toLocaleDateString('en-US', { month: 'short', day: 'numeric' });
  return date.toLocaleDateString('en-US', { month: 'long', day: 'numeric', year: 'numeric' });
};

const getDaysBetween = (start: string | Date, end: string | Date): number => {
  return Math.ceil((new Date(end).getTime() - new Date(start).getTime()) / (1000 * 60 * 60 * 24));
};

const formatLargeNumber = (num: number): string => {
  if (num >= 1000000) return `${(num / 1000000).toFixed(1)}M`;
  if (num >= 1000) return `${(num / 1000).toFixed(0)}K`;
  return num?.toLocaleString() || '—';
};

interface MonthInfo {
  month: string;
  shortMonth: string;
  year: number;
  monthNumber: number;
  startDate: Date;
  endDate: Date;
}

const getMonthsInRange = (startDate: string, endDate: string): MonthInfo[] => {
  const months: MonthInfo[] = [];
  const start = new Date(startDate);
  const end = new Date(endDate);
  const current = new Date(start.getFullYear(), start.getMonth(), 1);

  while (current <= end) {
    months.push({
      month: current.toLocaleDateString('en-US', { month: 'long', year: 'numeric' }),
      shortMonth: current.toLocaleDateString('en-US', { month: 'short' }),
      year: current.getFullYear(),
      monthNumber: current.getMonth(),
      startDate: new Date(current),
      endDate: new Date(current.getFullYear(), current.getMonth() + 1, 0)
    });
    current.setMonth(current.getMonth() + 1);
  }
  return months;
};

interface WeekInfo {
  weekNumber: number;
  startDate: Date;
  endDate: Date;
  label: string;
}

const getWeeksInMonth = (year: number, month: number): WeekInfo[] => {
  const weeks: WeekInfo[] = [];
  const firstDay = new Date(year, month, 1);
  const lastDay = new Date(year, month + 1, 0);
  let currentWeekStart = new Date(firstDay);
  let weekNum = 1;

  while (currentWeekStart <= lastDay) {
    const weekEnd = new Date(currentWeekStart);
    weekEnd.setDate(weekEnd.getDate() + 6);
    if (weekEnd > lastDay) weekEnd.setTime(lastDay.getTime());

    weeks.push({
      weekNumber: weekNum,
      startDate: new Date(currentWeekStart),
      endDate: new Date(weekEnd),
      label: `Wk ${weekNum}`
    });

    currentWeekStart.setDate(currentWeekStart.getDate() + 7);
    weekNum++;
  }
  return weeks;
};

const isCampaignActiveInPeriod = (campaign: Campaign, periodStart: Date, periodEnd: Date): boolean => {
  const campStart = new Date(campaign.startDate);
  const campEnd = new Date(campaign.endDate);
  return campStart <= periodEnd && campEnd >= periodStart;
};

// =============================================================================
// PLATFORM LOGO COMPONENT
// =============================================================================
interface PlatformLogoProps {
  platformId: string;
  size?: number;
  className?: string;
}

const PlatformLogo: React.FC<PlatformLogoProps> = ({ platformId, size = 20, className = '' }) => {
  const [logoError, setLogoError] = useState(false);
  const config = platformConfig[platformId?.toLowerCase()];

  if (!config) {
    return <span className={className} style={{ fontSize: size }}>❓</span>;
  }

  if (config.logo && !logoError) {
    return (
      <img
        src={config.logo}
        alt={config.altText || config.name}
        width={size}
        height={size}
        className={`platform-logo ${className}`}
        style={{ display: 'block', objectFit: 'contain' }}
        onError={() => setLogoError(true)}
      />
    );
  }

  if (config.emoji) {
    return <span className={className} style={{ fontSize: size * 0.9, lineHeight: 1 }}>{config.emoji}</span>;
  }

  return (
    <div
      className={`platform-logo-fallback ${className}`}
      style={{
        width: size,
        height: size,
        borderRadius: '50%',
        background: config.color,
        color: 'white',
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        fontSize: size * 0.45,
        fontWeight: 600
      }}
    >
      {config.name.charAt(0)}
    </div>
  );
};

// =============================================================================
// BUDGET DONUT CHART
// =============================================================================
interface BudgetDonutProps {
  data: CampaignData['budget'];
}

const BudgetDonut: React.FC<BudgetDonutProps> = ({ data }) => {
  const COLORS = ['#D4A574', '#8B7355', '#6B5B4F', '#4A7C59', '#2C2416', '#A89078'];
  const chartData = [
    { name: 'Digital Campaigns', value: data.digitalCampaigns },
    { name: 'Digital Media', value: data.digitalMedia },
    { name: 'OOH', value: data.ooh },
    { name: 'Broadcast', value: data.broadcast },
    { name: 'Management Fees', value: data.managementFees },
    { name: 'Service & PM Fees', value: data.serviceFees + data.projectManagementFees }
  ].filter(d => d.value > 0);

  return (
    <div className="budget-donut">
      <ResponsiveContainer width="100%" height={180}>
        <PieChart>
          <Pie data={chartData} cx="50%" cy="50%" innerRadius={55} outerRadius={75} paddingAngle={2} dataKey="value">
            {chartData.map((entry, i) => <Cell key={i} fill={COLORS[i % COLORS.length]} />)}
          </Pie>
          <Tooltip
            formatter={(v: number) => formatFullCurrency(v)}
            contentStyle={{ background: 'white', border: '1px solid #E8E4DE', borderRadius: '8px', fontSize: '12px' }}
          />
        </PieChart>
      </ResponsiveContainer>
      <div className="donut-center">
        <span className="donut-total">{formatCurrency(data.total)}</span>
        <span className="donut-label">Total</span>
      </div>
      <div className="donut-legend">
        {chartData.map((item, i) => (
          <div key={i} className="legend-row">
            <span className="legend-dot" style={{ background: COLORS[i % COLORS.length] }} />
            <span className="legend-name">{item.name}</span>
            <span className="legend-val">{formatCurrency(item.value)}</span>
          </div>
        ))}
      </div>
    </div>
  );
};

// =============================================================================
// CAMPAIGN TIMELINE
// =============================================================================
interface CampaignTimelineProps {
  phases: CampaignData['project']['phases'];
}

const CampaignTimeline: React.FC<CampaignTimelineProps> = ({ phases }) => (
  <div className="timeline-wrap">
    <div className="timeline-track">
      {phases.map((phase, i) => (
        <div key={i} className="timeline-phase">
          <div className="phase-dot" />
          <div className="phase-name">{phase.name}</div>
          <div className="phase-dates">{formatDate(phase.start)} - {formatDate(phase.end)}</div>
        </div>
      ))}
    </div>
  </div>
);

// =============================================================================
// FUNNEL VISUALIZATION
// =============================================================================
interface FunnelVisualizationProps {
  platforms: Platform[];
  expandedStage: string | null;
  onToggle: (id: string) => void;
  showDetail: boolean;
}

const FunnelVisualization: React.FC<FunnelVisualizationProps> = ({
  platforms, expandedStage, onToggle, showDetail
}) => {
  const stageBudgets = useMemo(() => {
    const budgets: Record<string, number> = { awareness: 0, consideration: 0, conversion: 0 };
    platforms.forEach(p => p.campaigns.forEach(c => {
      const stage = c.funnelStage.toLowerCase();
      if (budgets[stage] !== undefined) budgets[stage] += c.totalSpend;
    }));
    return budgets;
  }, [platforms]);

  const totalDigital = Object.values(stageBudgets).reduce((a, b) => a + b, 0);

  const getCampaignsForStage = (stageId: string) => {
    const campaigns: (Campaign & { platformId: string; platform: string; platformColor: string })[] = [];
    platforms.forEach(p => p.campaigns.forEach(c => {
      if (c.funnelStage.toLowerCase() === stageId) {
        campaigns.push({ ...c, platformId: p.id, platform: p.name, platformColor: p.color });
      }
    }));
    return campaigns;
  };

  return (
    <div className="funnel-viz">
      {funnelStages.map((stage, idx) => {
        const Icon = stage.icon;
        const isExpanded = expandedStage === stage.id;
        const stageCampaigns = getCampaignsForStage(stage.id);
        const widthPct = 100 - (idx * 18);
        const stagePct = totalDigital > 0 ? ((stageBudgets[stage.id] / totalDigital) * 100).toFixed(0) : '0';

        return (
          <div key={stage.id} className="funnel-stage-wrap">
            <div className={`funnel-stage ${isExpanded ? 'expanded' : ''}`} onClick={() => onToggle(stage.id)}>
              <div className="funnel-bar" style={{ width: `${widthPct}%`, background: stage.color }}>
                <div className="funnel-inner">
                  <div className="funnel-left">
                    <Icon size={20} />
                    <div className="funnel-text">
                      <span className="funnel-name">{stage.name}</span>
                      <span className="funnel-sub">{stage.subtitle}</span>
                    </div>
                  </div>
                  <div className="funnel-right">
                    <span className="funnel-budget">{formatCurrency(stageBudgets[stage.id])}</span>
                    <span className="funnel-pct">{stagePct}%</span>
                  </div>
                  <div className="funnel-chevron">{isExpanded ? <ChevronDown size={20} /> : <ChevronRight size={20} />}</div>
                </div>
              </div>
            </div>

            {isExpanded && (
              <div className="funnel-detail">
                <div className="detail-row">
                  <div className="detail-box">
                    <h4>Objective</h4>
                    <p>{stage.objective}</p>
                  </div>
                  <div className="detail-box">
                    <h4>Success Metrics</h4>
                    <div className="metric-tags">{stage.metrics.map((m, i) => <span key={i} className="metric-tag">{m}</span>)}</div>
                  </div>
                </div>
                <div className="detail-box full">
                  <h4>Strategy</h4>
                  <p>{stage.description}</p>
                </div>
                <div className="detail-box full rationale-box">
                  <h4>Why This Approach</h4>
                  <p>{stage.rationale}</p>
                </div>
                {showDetail && stageCampaigns.length > 0 && (
                  <div className="detail-box full">
                    <h4>Active Campaigns ({stageCampaigns.length})</h4>
                    <div className="campaign-chips">
                      {stageCampaigns.map((c, i) => (
                        <div key={i} className="campaign-chip">
                          <div className="chip-platform-logo">
                            <PlatformLogo platformId={c.platformId} size={16} />
                          </div>
                          <span className="chip-name">{c.name}</span>
                          <span className="chip-budget">{formatCurrency(c.totalSpend)}</span>
                        </div>
                      ))}
                    </div>
                  </div>
                )}
              </div>
            )}
            {idx < funnelStages.length - 1 && <div className="funnel-arrow"><ArrowRight size={14} /></div>}
          </div>
        );
      })}
    </div>
  );
};

// =============================================================================
// GANTT CHART
// =============================================================================
interface TrueGanttChartProps {
  platforms: Platform[];
  projectStart: string;
  projectEnd: string;
  selectedView: string;
  onViewChange: (view: string) => void;
}

const TrueGanttChart: React.FC<TrueGanttChartProps> = ({
  platforms, projectStart, projectEnd, selectedView, onViewChange
}) => {
  const [collapsedPlatforms, setCollapsedPlatforms] = useState<Record<string, boolean>>(() => {
    const initial: Record<string, boolean> = {};
    platforms.forEach(p => { initial[p.id] = true; });
    return initial;
  });
  const [hoveredCampaign, setHoveredCampaign] = useState<Campaign | null>(null);
  const [hoveredPlatform, setHoveredPlatform] = useState<string | null>(null);
  const [selectedCampaign, setSelectedCampaign] = useState<Campaign | null>(null);

  const months = useMemo(() => getMonthsInRange(projectStart, projectEnd), [projectStart, projectEnd]);

  const viewOptions = [
    { value: 'full', label: 'Full Campaign' },
    { value: 'q1', label: 'Q1 2025' },
    { value: 'q2', label: 'Q2 2025' },
    ...months.map(m => ({ value: m.month, label: m.month }))
  ];

  interface VisibleRange {
    start: Date;
    end: Date;
    months?: MonthInfo[];
    weeks?: WeekInfo[];
    isMonthly: boolean;
    month?: MonthInfo;
  }

  const getVisibleRange = (): VisibleRange => {
    if (selectedView === 'full') return { start: new Date(projectStart), end: new Date(projectEnd), months, isMonthly: false };
    if (selectedView === 'q1') return { start: new Date('2025-01-01'), end: new Date('2025-03-31'), months: months.filter(m => m.monthNumber < 3), isMonthly: false };
    if (selectedView === 'q2') return { start: new Date('2025-04-01'), end: new Date('2025-06-30'), months: months.filter(m => m.monthNumber >= 3 && m.monthNumber < 6), isMonthly: false };

    const selectedMonth = months.find(m => m.month === selectedView);
    if (selectedMonth) {
      const weeks = getWeeksInMonth(selectedMonth.year, selectedMonth.monthNumber);
      return { start: selectedMonth.startDate, end: selectedMonth.endDate, weeks, isMonthly: true, month: selectedMonth };
    }
    return { start: new Date(projectStart), end: new Date(projectEnd), months, isMonthly: false };
  };

  const visibleRange = getVisibleRange();
  const totalDays = getDaysBetween(visibleRange.start, visibleRange.end);

  const togglePlatform = (platformId: string) => {
    setCollapsedPlatforms(prev => ({ ...prev, [platformId]: !prev[platformId] }));
  };

  const getBarPosition = (campaign: Campaign) => {
    const campStart = new Date(campaign.startDate);
    const campEnd = new Date(campaign.endDate);
    const rangeStart = visibleRange.start;
    const rangeEnd = visibleRange.end;

    const visStart = campStart < rangeStart ? rangeStart : campStart;
    const visEnd = campEnd > rangeEnd ? rangeEnd : campEnd;

    if (visStart > rangeEnd || visEnd < rangeStart) return null;

    const startOffset = getDaysBetween(rangeStart, visStart);
    const duration = getDaysBetween(visStart, visEnd) + 1;

    const leftPct = (startOffset / totalDays) * 100;
    const widthPct = (duration / totalDays) * 100;

    return { left: `${leftPct}%`, width: `${Math.max(widthPct, 2)}%` };
  };

  const getPlatformCombinedBar = (campaigns: Campaign[]) => {
    if (!campaigns || campaigns.length === 0) return null;

    const activeCampaigns = campaigns.filter(c =>
      isCampaignActiveInPeriod(c, visibleRange.start, visibleRange.end)
    );

    if (activeCampaigns.length === 0) return null;

    let earliestStart = new Date(activeCampaigns[0].startDate);
    let latestEnd = new Date(activeCampaigns[0].endDate);

    activeCampaigns.forEach(c => {
      const start = new Date(c.startDate);
      const end = new Date(c.endDate);
      if (start < earliestStart) earliestStart = start;
      if (end > latestEnd) latestEnd = end;
    });

    const rangeStart = visibleRange.start;
    const rangeEnd = visibleRange.end;

    const visStart = earliestStart < rangeStart ? rangeStart : earliestStart;
    const visEnd = latestEnd > rangeEnd ? rangeEnd : latestEnd;

    if (visStart > rangeEnd || visEnd < rangeStart) return null;

    const startOffset = getDaysBetween(rangeStart, visStart);
    const duration = getDaysBetween(visStart, visEnd) + 1;

    const leftPct = (startOffset / totalDays) * 100;
    const widthPct = (duration / totalDays) * 100;

    return {
      left: `${leftPct}%`,
      width: `${Math.max(widthPct, 2)}%`,
      startDate: earliestStart,
      endDate: latestEnd,
      campaignCount: activeCampaigns.length
    };
  };

  const getStagePattern = (stage: string) => {
    switch (stage.toLowerCase()) {
      case 'awareness': return 'pattern-awareness';
      case 'consideration': return 'pattern-consideration';
      default: return 'pattern-conversion';
    }
  };

  return (
    <div className="gantt-container">
      <div className="gantt-controls">
        <div className="view-selector">
          <Filter size={14} />
          <select value={selectedView} onChange={(e) => onViewChange(e.target.value)}>
            {viewOptions.map(opt => <option key={opt.value} value={opt.value}>{opt.label}</option>)}
          </select>
        </div>
        <div className="gantt-legend">
          <div className="legend-item"><span className="legend-bar awareness-bar" /> Awareness</div>
          <div className="legend-item"><span className="legend-bar consideration-bar" /> Consideration</div>
          <div className="legend-item"><span className="legend-bar conversion-bar" /> Conversion</div>
        </div>
      </div>

      <div className="gantt-chart">
        <div className="gantt-header">
          <div className="gantt-label-col">Campaign</div>
          <div className="gantt-timeline-col">
            {visibleRange.isMonthly ? (
              visibleRange.weeks?.map((w, i) => <div key={i} className="gantt-time-header">{w.label}</div>)
            ) : (
              visibleRange.months?.map((m, i) => <div key={i} className="gantt-time-header">{m.shortMonth}</div>)
            )}
          </div>
          <div className="gantt-budget-col">Budget</div>
        </div>

        <div className="gantt-body">
          {platforms.map(platform => {
            const isCollapsed = collapsedPlatforms[platform.id];
            const activeCampaigns = platform.campaigns.filter(c =>
              isCampaignActiveInPeriod(c, visibleRange.start, visibleRange.end)
            );

            if (activeCampaigns.length === 0 && selectedView !== 'full') return null;

            return (
              <div key={platform.id} className="platform-group">
                <div className="platform-row" onClick={() => togglePlatform(platform.id)}>
                  <div className="gantt-label-col platform-header">
                    <span className="platform-toggle">{isCollapsed ? <ChevronRight size={14} /> : <ChevronDown size={14} />}</span>
                    <div className="platform-logo-wrap">
                      <PlatformLogo platformId={platform.id} size={18} />
                    </div>
                    <span className="platform-name">{platform.name}</span>
                    <span className="platform-count">({activeCampaigns.length})</span>
                  </div>
                  <div className="gantt-timeline-col">
                    <div className="timeline-grid platform-grid">
                      {visibleRange.isMonthly
                        ? visibleRange.weeks?.map((_, i) => <div key={i} className="grid-line" />)
                        : visibleRange.months?.map((_, i) => <div key={i} className="grid-line" />)
                      }
                    </div>
                    {isCollapsed ? (
                      (() => {
                        const combinedBar = getPlatformCombinedBar(platform.campaigns);
                        if (!combinedBar) return <div className="platform-bar-bg" />;
                        return (
                          <>
                            <div
                              className="platform-combined-bar"
                              style={{
                                left: combinedBar.left,
                                width: combinedBar.width,
                                backgroundColor: platform.color
                              }}
                              onMouseEnter={(e) => {
                                e.stopPropagation();
                                setHoveredPlatform(platform.id);
                              }}
                              onMouseLeave={() => setHoveredPlatform(null)}
                            >
                              <span className="combined-bar-label">{formatCurrency(platform.totalBudget)}</span>
                            </div>
                            {hoveredPlatform === platform.id && (
                              <div className="platform-tooltip" style={{ left: combinedBar.left }}>
                                <div className="tooltip-header">{platform.name}</div>
                                <div className="tooltip-row"><span>Total Budget:</span> {formatCurrency(platform.totalBudget)}</div>
                                <div className="tooltip-row"><span>Date Range:</span> {formatDate(combinedBar.startDate.toISOString())} - {formatDate(combinedBar.endDate.toISOString())}</div>
                                <div className="tooltip-row"><span>Campaigns:</span> {combinedBar.campaignCount}</div>
                                <div className="tooltip-hint">Click to expand campaigns</div>
                              </div>
                            )}
                          </>
                        );
                      })()
                    ) : (
                      <div className="platform-bar-bg" />
                    )}
                  </div>
                  <div className="gantt-budget-col platform-total">{formatCurrency(platform.totalBudget)}</div>
                </div>

                {!isCollapsed && activeCampaigns.map(campaign => {
                  const barPos = getBarPosition(campaign);
                  if (!barPos) return null;

                  return (
                    <div
                      key={campaign.id}
                      className={`campaign-row ${selectedCampaign?.id === campaign.id ? 'selected' : ''}`}
                      onClick={() => setSelectedCampaign(selectedCampaign?.id === campaign.id ? null : campaign)}
                    >
                      <div className="gantt-label-col campaign-label">
                        <span className={`stage-dot stage-${campaign.funnelStage.toLowerCase()}`} />
                        <span className="campaign-name-text">{campaign.name}</span>
                        <span className="campaign-type-badge">{campaign.type}</span>
                      </div>
                      <div className="gantt-timeline-col">
                        <div className="timeline-grid">
                          {visibleRange.isMonthly
                            ? visibleRange.weeks?.map((_, i) => <div key={i} className="grid-line" />)
                            : visibleRange.months?.map((_, i) => <div key={i} className="grid-line" />)
                          }
                        </div>
                        <div
                          className={`campaign-bar ${getStagePattern(campaign.funnelStage)}`}
                          style={{ left: barPos.left, width: barPos.width, backgroundColor: platform.color }}
                          onMouseEnter={() => setHoveredCampaign(campaign)}
                          onMouseLeave={() => setHoveredCampaign(null)}
                        >
                          <span className="bar-label">{formatCurrency(campaign.totalSpend)}</span>
                        </div>
                        {hoveredCampaign?.id === campaign.id && (
                          <div className="campaign-tooltip" style={{ left: barPos.left }}>
                            <div className="tooltip-header">{campaign.name}</div>
                            <div className="tooltip-row"><span>Platform:</span> {platform.name}</div>
                            <div className="tooltip-row"><span>Dates:</span> {formatDate(campaign.startDate)} - {formatDate(campaign.endDate)}</div>
                            <div className="tooltip-row"><span>Budget:</span> {formatCurrency(campaign.totalSpend)}</div>
                            <div className="tooltip-row"><span>Daily:</span> ${campaign.dailySpend}/day</div>
                            <div className="tooltip-row"><span>Stage:</span> {campaign.funnelStage}</div>
                          </div>
                        )}
                      </div>
                      <div className="gantt-budget-col">{formatCurrency(campaign.totalSpend)}</div>
                    </div>
                  );
                })}
              </div>
            );
          })}
        </div>
      </div>

      {selectedCampaign && (
        <div className="campaign-detail-panel">
          <div className="detail-panel-header">
            <h3>{selectedCampaign.name}</h3>
            <button className="close-btn" onClick={() => setSelectedCampaign(null)}><X size={18} /></button>
          </div>
          <div className="detail-panel-body">
            <div className="detail-grid">
              <div className="detail-item">
                <span className="detail-label">Date Range</span>
                <span className="detail-value">{formatDate(selectedCampaign.startDate, 'long')} - {formatDate(selectedCampaign.endDate, 'long')}</span>
              </div>
              <div className="detail-item">
                <span className="detail-label">Total Budget</span>
                <span className="detail-value">{formatCurrency(selectedCampaign.totalSpend)}</span>
              </div>
              <div className="detail-item">
                <span className="detail-label">Daily Spend</span>
                <span className="detail-value">${selectedCampaign.dailySpend}/day</span>
              </div>
              <div className="detail-item">
                <span className="detail-label">Duration</span>
                <span className="detail-value">{getDaysBetween(selectedCampaign.startDate, selectedCampaign.endDate)} days</span>
              </div>
              <div className="detail-item">
                <span className="detail-label">Funnel Stage</span>
                <span className={`stage-badge stage-${selectedCampaign.funnelStage.toLowerCase()}`}>{selectedCampaign.funnelStage}</span>
              </div>
              <div className="detail-item">
                <span className="detail-label">Objective</span>
                <span className="detail-value">{selectedCampaign.objective}</span>
              </div>
            </div>
            <div className="detail-item full-width">
              <span className="detail-label">Format & Tactics</span>
              <p className="detail-text">{selectedCampaign.format}</p>
            </div>
            {selectedCampaign.targeting && (
              <div className="detail-item full-width">
                <span className="detail-label">Targeting</span>
                <p className="detail-text">{selectedCampaign.targeting}</p>
              </div>
            )}
          </div>
        </div>
      )}
    </div>
  );
};

// =============================================================================
// PLATFORM CARD
// =============================================================================
interface PlatformCardProps {
  platform: Platform;
  expanded: boolean;
  onToggle: () => void;
}

const PlatformCard: React.FC<PlatformCardProps> = ({ platform, expanded, onToggle }) => (
  <div className={`platform-card ${expanded ? 'expanded' : ''}`}>
    <div className="platform-card-header" onClick={onToggle}>
      <div className="platform-card-left">
        <div className="platform-logo-wrap-lg">
          <PlatformLogo platformId={platform.id} size={26} />
        </div>
        <div>
          <h4>{platform.name}</h4>
          <span className="campaign-count">{platform.campaigns.length} campaign{platform.campaigns.length !== 1 ? 's' : ''}</span>
        </div>
      </div>
      <div className="platform-card-right">
        <span className="platform-budget">{formatCurrency(platform.totalBudget)}</span>
        {expanded ? <ChevronUp size={18} /> : <ChevronDown size={18} />}
      </div>
    </div>
    {expanded && (
      <div className="platform-card-body">
        {platform.campaigns.map((c, i) => (
          <div key={i} className="campaign-detail-card">
            <div className="campaign-detail-top">
              <span className="campaign-detail-name">{c.name}</span>
              <span className="campaign-detail-budget">{formatCurrency(c.totalSpend)}</span>
            </div>
            <div className="campaign-detail-meta">
              <span><Calendar size={12} /> {formatDate(c.startDate)} - {formatDate(c.endDate)}</span>
              <span><DollarSign size={12} /> ${c.dailySpend}/day</span>
              <span className={`stage-badge stage-${c.funnelStage.toLowerCase()}`}>{c.funnelStage}</span>
            </div>
            <p className="campaign-format">{c.format}</p>
            {c.targeting && <div className="campaign-targeting"><Target size={12} /> {c.targeting}</div>}
          </div>
        ))}
      </div>
    )}
  </div>
);

// =============================================================================
// RESULTS COMING SOON
// =============================================================================
interface ResultsComingSoonProps {
  startDate: string;
}

const ResultsComingSoon: React.FC<ResultsComingSoonProps> = ({ startDate }) => {
  const start = new Date(startDate);
  const today = new Date();
  const daysUntil = Math.ceil((start.getTime() - today.getTime()) / (1000 * 60 * 60 * 24));

  return (
    <div className="results-soon">
      <div className="results-icon"><BarChart3 size={48} /></div>
      <h3>Results Coming Soon</h3>
      <p>{daysUntil > 0
        ? `Campaign launches in ${daysUntil} days. Performance data will be available once live.`
        : "Campaign is live. Performance data is being collected."
      }</p>
      <div className="results-timeline">
        <Clock size={16} />
        <span>Launch: {start.toLocaleDateString('en-US', { month: 'long', day: 'numeric', year: 'numeric' })}</span>
      </div>
    </div>
  );
};

// =============================================================================
// PROJECTIONS TAB
// =============================================================================
interface ProjectionsTabProps {
  projections: CampaignData['projections'];
  platforms: Platform[];
}

const ProjectionsTab: React.FC<ProjectionsTabProps> = ({ projections, platforms }) => {
  const [expandedPhases, setExpandedPhases] = useState<string[]>(() => {
    return projections?.byPhase?.length ? [projections.byPhase[0].phaseId] : [];
  });
  const [showAssumptions, setShowAssumptions] = useState(false);

  if (!projections) return null;

  const togglePhase = (phaseId: string) => {
    setExpandedPhases(prev =>
      prev.includes(phaseId)
        ? prev.filter(id => id !== phaseId)
        : [...prev, phaseId]
    );
  };

  const funnelStageConfig = {
    awareness: { name: 'Awareness', subtitle: 'Top of Funnel', color: '#D4A574', icon: Eye },
    consideration: { name: 'Consideration', subtitle: 'Middle of Funnel', color: '#8B7355', icon: Users },
    conversion: { name: 'Conversion', subtitle: 'Bottom of Funnel', color: '#4A7C59', icon: Target }
  };

  const campaignTotal = projections.campaignTotal;
  const phases = projections.byPhase || [];

  return (
    <div className="projections-tab">
      <div className="projections-header-banner">
        <div className="banner-icon"><TrendingUp size={24} /></div>
        <div className="banner-content">
          <h3>Campaign Projections</h3>
          <p>
            Generated: {new Date(projections.generated).toLocaleDateString('en-US', { month: 'long', day: 'numeric', year: 'numeric' })}
            {projections.lastUpdated && projections.lastUpdated !== projections.generated && (
              <span> • Updated: {new Date(projections.lastUpdated).toLocaleDateString('en-US', { month: 'long', day: 'numeric', year: 'numeric' })}</span>
            )}
          </p>
        </div>
        <div className="banner-badge">
          <Lock size={14} />
          <span>LOCKED</span>
        </div>
      </div>

      <div className="card projections-main-card">
        <div className="card-header">
          <div>
            <h2 className="card-title">Total Campaign Projections</h2>
            <p className="card-subtitle">{campaignTotal.campaignDuration} • {campaignTotal.durationDays} days</p>
          </div>
        </div>

        <div className="projections-metrics-grid">
          <div className="projection-metric-card highlight">
            <div className="metric-icon"><Target size={20} /></div>
            <div className="metric-content">
              <span className="metric-label">Total Registrations</span>
              <span className="metric-value">{campaignTotal.totalRegistrations.toLocaleString()}</span>
            </div>
          </div>

          <div className="projection-metric-card highlight">
            <div className="metric-icon"><DollarSign size={20} /></div>
            <div className="metric-content">
              <span className="metric-label">Average CPL</span>
              <span className="metric-value">${campaignTotal.avgCpl.toFixed(2)}</span>
            </div>
          </div>

          <div className="projection-metric-card">
            <div className="metric-icon"><Eye size={20} /></div>
            <div className="metric-content">
              <span className="metric-label">Total Impressions</span>
              <span className="metric-value">{formatLargeNumber(campaignTotal.totalImpressions)}</span>
            </div>
          </div>

          <div className="projection-metric-card">
            <div className="metric-icon"><MousePointer size={20} /></div>
            <div className="metric-content">
              <span className="metric-label">Total Clicks</span>
              <span className="metric-value">{formatLargeNumber(campaignTotal.totalClicks)}</span>
            </div>
          </div>

          <div className="projection-metric-card">
            <div className="metric-icon"><Percent size={20} /></div>
            <div className="metric-content">
              <span className="metric-label">Avg. Conversion Rate</span>
              <span className="metric-value">{campaignTotal.avgCvr}%</span>
            </div>
          </div>

          <div className="projection-metric-card">
            <div className="metric-icon"><DollarSign size={20} /></div>
            <div className="metric-content">
              <span className="metric-label">Total Budget</span>
              <span className="metric-value">{formatCurrency(campaignTotal.totalBudget)}</span>
            </div>
          </div>
        </div>
      </div>

      {phases.map((phase) => {
        const isExpanded = expandedPhases.includes(phase.phaseId);
        const phaseStartDate = new Date(phase.startDate).toLocaleDateString('en-US', { month: 'short', day: 'numeric' });
        const phaseEndDate = new Date(phase.endDate).toLocaleDateString('en-US', { month: 'short', day: 'numeric', year: 'numeric' });

        return (
          <div key={phase.phaseId} className={`phase-accordion ${isExpanded ? 'expanded' : ''}`}>
            <div className="phase-header" onClick={() => togglePhase(phase.phaseId)}>
              <div className="phase-header-left">
                <span className="phase-toggle">
                  {isExpanded ? <ChevronDown size={18} /> : <ChevronRight size={18} />}
                </span>
                <div className="phase-info">
                  <h3 className="phase-name">{phase.phaseName}</h3>
                  <span className="phase-dates">{phaseStartDate} - {phaseEndDate} • {phase.durationDays} days • Budget: {formatCurrency(phase.performance.budget)}</span>
                </div>
              </div>
              <div className="phase-header-right">
                <div className="phase-summary">
                  <span className="phase-summary-label">Projected:</span>
                  <span className="phase-summary-value">{phase.performance.totalRegistrations.toLocaleString()} registrations @ ${phase.performance.cpl.toFixed(2)} CPL</span>
                </div>
              </div>
            </div>

            {isExpanded && (
              <div className="phase-content">
                <div className="phase-section">
                  <h4 className="phase-section-title">Phase Performance Projections</h4>
                  <div className="phase-metrics-grid">
                    <div className="phase-metric">
                      <span className="pm-label">Registrations</span>
                      <span className="pm-value">{phase.performance.totalRegistrations.toLocaleString()}</span>
                    </div>
                    <div className="phase-metric">
                      <span className="pm-label">Impressions</span>
                      <span className="pm-value">{formatLargeNumber(phase.performance.totalImpressions)}</span>
                    </div>
                    <div className="phase-metric">
                      <span className="pm-label">Clicks</span>
                      <span className="pm-value">{formatLargeNumber(phase.performance.totalClicks)}</span>
                    </div>
                    <div className="phase-metric">
                      <span className="pm-label">Click-Through Rate</span>
                      <span className="pm-value">{phase.performance.ctr}%</span>
                    </div>
                    <div className="phase-metric">
                      <span className="pm-label">Conversion Rate</span>
                      <span className="pm-value">{phase.performance.cvr}%</span>
                    </div>
                    <div className="phase-metric">
                      <span className="pm-label">Cost Per Lead</span>
                      <span className="pm-value">${phase.performance.cpl.toFixed(2)}</span>
                    </div>
                    <div className="phase-metric">
                      <span className="pm-label">Cost Per Click</span>
                      <span className="pm-value">${phase.performance.cpc.toFixed(2)}</span>
                    </div>
                  </div>
                </div>

                <div className="phase-section">
                  <h4 className="phase-section-title">Platform Breakdown</h4>
                  <div className="phase-platform-table">
                    <div className="ppt-header">
                      <div className="ppt-col ppt-platform">Platform</div>
                      <div className="ppt-col ppt-impressions">Impressions</div>
                      <div className="ppt-col ppt-clicks">Clicks</div>
                      <div className="ppt-col ppt-reg">Registrations</div>
                      <div className="ppt-col ppt-cpl">CPL</div>
                    </div>
                    {phase.platformBreakdown.map((p, i) => (
                      <div key={i} className={`ppt-row ${i % 2 === 0 ? 'even' : 'odd'}`}>
                        <div className="ppt-col ppt-platform">
                          <PlatformLogo platformId={p.platformId} size={18} />
                          <span>{p.platformName}</span>
                        </div>
                        <div className="ppt-col ppt-impressions">{formatLargeNumber(p.projectedImpressions)}</div>
                        <div className="ppt-col ppt-clicks">{p.projectedClicks ? formatLargeNumber(p.projectedClicks) : '—'}</div>
                        <div className="ppt-col ppt-reg">{p.projectedRegistrations ? p.projectedRegistrations.toLocaleString() : '—'}</div>
                        <div className="ppt-col ppt-cpl">{p.projectedCPL ? `$${p.projectedCPL.toFixed(2)}` : '—'}</div>
                      </div>
                    ))}
                  </div>
                </div>

                <div className="phase-section">
                  <h4 className="phase-section-title">Funnel Breakdown</h4>
                  <div className="phase-funnel-grid">
                    {Object.entries(phase.funnelBreakdown).map(([stageId, stageData]) => {
                      const config = funnelStageConfig[stageId as keyof typeof funnelStageConfig];
                      const Icon = config.icon;

                      return (
                        <div key={stageId} className="phase-funnel-card" style={{ borderLeftColor: config.color }}>
                          <div className="pfc-header" style={{ backgroundColor: `${config.color}15` }}>
                            <div className="pfc-title">
                              <Icon size={16} style={{ color: config.color }} />
                              <span>{config.name}</span>
                            </div>
                            <div className="pfc-budget">
                              {formatCurrency(stageData.budget)} ({stageData.budgetPercent}%)
                            </div>
                          </div>
                          <div className="pfc-metrics">
                            {stageData.impressions && (
                              <div className="pfc-metric">
                                <span className="pfc-metric-label">Impressions</span>
                                <span className="pfc-metric-value">{formatLargeNumber(stageData.impressions)}</span>
                              </div>
                            )}
                            {stageData.clicks && (
                              <div className="pfc-metric">
                                <span className="pfc-metric-label">Clicks</span>
                                <span className="pfc-metric-value">{formatLargeNumber(stageData.clicks)}</span>
                              </div>
                            )}
                            {stageData.ctr && (
                              <div className="pfc-metric">
                                <span className="pfc-metric-label">CTR</span>
                                <span className="pfc-metric-value">{stageData.ctr}%</span>
                              </div>
                            )}
                            {stageData.registrations !== undefined && (
                              <div className="pfc-metric">
                                <span className="pfc-metric-label">Registrations</span>
                                <span className="pfc-metric-value">{stageData.registrations.toLocaleString()}</span>
                              </div>
                            )}
                            {stageData.cvr && (
                              <div className="pfc-metric">
                                <span className="pfc-metric-label">CVR</span>
                                <span className="pfc-metric-value">{stageData.cvr}%</span>
                              </div>
                            )}
                            {stageData.cpl && (
                              <div className="pfc-metric">
                                <span className="pfc-metric-label">CPL</span>
                                <span className="pfc-metric-value">${stageData.cpl.toFixed(2)}</span>
                              </div>
                            )}
                          </div>
                        </div>
                      );
                    })}
                  </div>
                </div>
              </div>
            )}
          </div>
        );
      })}

      <div className="card assumptions-card">
        <div
          className="assumptions-header"
          onClick={() => setShowAssumptions(!showAssumptions)}
        >
          <div className="assumptions-title">
            {showAssumptions ? <ChevronDown size={18} /> : <ChevronRight size={18} />}
            <span>Methodology & Assumptions</span>
          </div>
          <span className="assumptions-toggle">{showAssumptions ? 'Hide' : 'Show'}</span>
        </div>

        {showAssumptions && (
          <div className="assumptions-content">
            <div className="assumptions-section">
              <h4>Assumptions</h4>
              <ul>
                {projections.assumptions.map((assumption, i) => (
                  <li key={i}>{assumption}</li>
                ))}
              </ul>
            </div>

            <div className="assumptions-section">
              <h4>Data Sources</h4>
              <ul>
                {projections.dataSources.map((source, i) => (
                  <li key={i}>{source}</li>
                ))}
              </ul>
            </div>
          </div>
        )}
      </div>

      <div className="projections-disclaimer">
        <div className="disclaimer-icon"><AlertTriangle size={20} /></div>
        <div className="disclaimer-content">
          <h4>Important</h4>
          <p>
            These projections are estimates based on historical performance and industry benchmarks.
            Actual results may vary based on creative quality, market conditions, targeting accuracy,
            competitive landscape, and seasonal factors. Projections serve as planning guidelines,
            not guarantees. See Results tab for actual performance once the campaign is live.
          </p>
        </div>
      </div>
    </div>
  );
};

// =============================================================================
// MAIN DASHBOARD COMPONENT
// =============================================================================
interface MediaPlanDashboardProps {
  data: CampaignData;
}

export default function MediaPlanDashboard({ data }: MediaPlanDashboardProps) {
  const [activeTab, setActiveTab] = useState('plan');
  const [expandedStage, setExpandedStage] = useState<string | null>('conversion');
  const [showFunnelDetail, setShowFunnelDetail] = useState(false);
  const [expandedPlatform, setExpandedPlatform] = useState<string | null>(null);
  const [ganttView, setGanttView] = useState('full');

  const showResults = data.results?.available;
  const showProjections = data.projections?.enabled;

  const tabs = [
    { id: 'plan', label: 'Plan', icon: Layers },
    { id: 'strategy', label: 'Strategy', icon: Target },
    ...(showProjections ? [{ id: 'projections', label: 'Projections', icon: TrendingUp }] : []),
    { id: 'schedule', label: 'Media Schedule', icon: Calendar },
    ...(showResults ? [{ id: 'results', label: 'Results', icon: BarChart3 }] : [])
  ];

  return (
    <div className="dashboard">
      {/* Header */}
      <header className="header">
        <div className="header-left">
          <div className="brand-logo">P</div>
          <div className="header-text">
            <h1>{data.project.name}</h1>
            <div className="header-meta">
              <span>{data.project.client}</span>
              <span>•</span>
              <span><Calendar size={13} /> {data.project.period}</span>
            </div>
          </div>
        </div>
        <div className="header-right">
          <div className="header-period">Total Campaign Investment</div>
          <div className="header-budget">{formatFullCurrency(data.budget.total)}</div>
          <div className="header-objective">{data.project.objective}</div>
        </div>
      </header>

      {/* Navigation */}
      <nav className="nav-tabs">
        {tabs.map(tab => {
          const Icon = tab.icon;
          return (
            <button
              key={tab.id}
              className={`nav-tab ${activeTab === tab.id ? 'active' : ''}`}
              onClick={() => setActiveTab(tab.id)}
            >
              <Icon size={15} />
              {tab.label}
            </button>
          );
        })}
      </nav>

      {/* Tab: Plan */}
      {activeTab === 'plan' && (
        <div className="main-grid">
          <div className="main-content">
            {data.project.phases && data.project.phases.length > 0 && (
              <div className="card">
                <div className="card-header">
                  <div>
                    <h2 className="card-title">Campaign Timeline</h2>
                    <p className="card-subtitle">Phase progression and milestones</p>
                  </div>
                </div>
                <CampaignTimeline phases={data.project.phases} />
              </div>
            )}

            <div className="card">
              <div className="card-header">
                <div>
                  <h2 className="card-title">Channel Overview</h2>
                  <p className="card-subtitle">Click any channel for campaign details</p>
                </div>
              </div>
              <div className="platforms-grid">
                {data.platforms.map(p => (
                  <PlatformCard
                    key={p.id}
                    platform={p}
                    expanded={expandedPlatform === p.id}
                    onToggle={() => setExpandedPlatform(expandedPlatform === p.id ? null : p.id)}
                  />
                ))}
              </div>
            </div>
          </div>

          <div className="sidebar">
            <div className="sidebar-card">
              <h3 className="sidebar-title">Budget Breakdown</h3>
              <BudgetDonut data={data.budget} />
            </div>

            {data.audience && (
              <div className="sidebar-card">
                <h3 className="sidebar-title">Target Audience</h3>
                <div className="audience-list">
                  {data.audience.demographics && (
                    <div className="audience-item">
                      <span className="audience-label">Demographics</span>
                      <span className="audience-value">{data.audience.demographics}</span>
                    </div>
                  )}
                  {data.audience.income && (
                    <div className="audience-item">
                      <span className="audience-label">Income</span>
                      <span className="audience-value">{data.audience.income}</span>
                    </div>
                  )}
                  {data.audience.psychographics && (
                    <div className="audience-item">
                      <span className="audience-label">Psychographics</span>
                      <span className="audience-value">{data.audience.psychographics}</span>
                    </div>
                  )}
                  {data.audience.locations && (
                    <div className="audience-item">
                      <span className="audience-label">Geographic Focus</span>
                      <span className="audience-value">{data.audience.locations}</span>
                    </div>
                  )}
                  {data.audience.estimatedReach && (
                    <div className="audience-item">
                      <span className="audience-label">Estimated Reach</span>
                      <span className="audience-value">{data.audience.estimatedReach}</span>
                    </div>
                  )}
                </div>
              </div>
            )}
          </div>
        </div>
      )}

      {/* Tab: Strategy */}
      {activeTab === 'strategy' && (
        <div className="main-grid full-width">
          <div className="main-content">
            <div className="card">
              <div className="card-header">
                <div>
                  <h2 className="card-title">Marketing Funnel Strategy</h2>
                  <p className="card-subtitle">Click any stage to explore objectives, tactics, and rationale</p>
                </div>
                <button
                  className={`toggle-btn ${showFunnelDetail ? 'active' : ''}`}
                  onClick={() => setShowFunnelDetail(!showFunnelDetail)}
                >
                  <Layers size={14} />
                  {showFunnelDetail ? 'Hide Campaigns' : 'Show Campaigns'}
                </button>
              </div>
              <FunnelVisualization
                platforms={data.platforms}
                expandedStage={expandedStage}
                onToggle={(id) => setExpandedStage(expandedStage === id ? null : id)}
                showDetail={showFunnelDetail}
              />
            </div>
          </div>
        </div>
      )}

      {/* Tab: Schedule */}
      {activeTab === 'schedule' && (
        <div className="main-grid full-width">
          <div className="main-content">
            <div className="card">
              <div className="card-header">
                <div>
                  <h2 className="card-title">Media Schedule</h2>
                  <p className="card-subtitle">Click any campaign bar to see full details</p>
                </div>
              </div>
              <TrueGanttChart
                platforms={data.platforms}
                projectStart={data.project.startDate}
                projectEnd={data.project.endDate}
                selectedView={ganttView}
                onViewChange={setGanttView}
              />
            </div>
          </div>
        </div>
      )}

      {/* Tab: Projections */}
      {activeTab === 'projections' && data.projections && (
        <div className="main-grid full-width">
          <div className="main-content">
            <ProjectionsTab projections={data.projections} platforms={data.platforms} />
          </div>
        </div>
      )}

      {/* Tab: Results */}
      {activeTab === 'results' && (
        <div className="main-grid full-width">
          <div className="main-content">
            <div className="card">
              {data.results?.available ? (
                <div><p>Performance data here</p></div>
              ) : (
                <ResultsComingSoon startDate={data.project.startDate} />
              )}
            </div>
          </div>
        </div>
      )}
    </div>
  );
}
