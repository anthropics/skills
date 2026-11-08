---
name: media-plan-dashboard
description: Create self-hosted media plan dashboards that sync with Google Sheets. Use this skill when the user asks to build advertising campaign dashboards, media planning visualizations, marketing budget trackers, or campaign performance dashboards that need to pull data from Google Sheets.
license: MIT
---

# Media Plan Dashboard Skill

Create production-ready, self-hosted media plan dashboards that automatically sync campaign data from Google Sheets. These dashboards visualize advertising campaigns, budgets, timelines, funnel strategies, and performance projections.

## When to Use This Skill

- Building media planning dashboards for advertising agencies
- Creating campaign visualization tools that update from spreadsheets
- Developing marketing budget tracking interfaces
- Building client-facing campaign strategy presentations
- Creating self-hosted alternatives to media planning SaaS tools

## Architecture Overview

The dashboard consists of:

1. **React Frontend** - Single-page application with multiple tabs (Plan, Strategy, Schedule, Projections, Results)
2. **Google Sheets Integration** - Fetches data via Sheets API or published CSV
3. **Data Transformation Layer** - Maps sheet columns to dashboard data structures
4. **Auto-refresh** - Periodic polling for live updates

## Data Structure

The dashboard expects data in this structure (see `reference/data-schema.md` for full schema):

```typescript
interface CampaignData {
  project: {
    name: string;
    client: string;
    period: string;
    objective: string;
    startDate: string;
    endDate: string;
    phases: Phase[];
  };
  budget: BudgetBreakdown;
  audience: TargetAudience;
  platforms: Platform[];
  projections?: Projections;
  results?: Results;
}
```

## Google Sheets Setup

### Option 1: Published CSV (Simplest, No API Key)

1. Create Google Sheet with required tabs (Campaigns, Budget, Platforms)
2. File > Share > Publish to web
3. Select "Comma-separated values (.csv)" for each tab
4. Use the published URL in the dashboard

### Option 2: Sheets API (More Control)

1. Create project in Google Cloud Console
2. Enable Google Sheets API
3. Create API key (restrict to Sheets API)
4. Use sheet ID and API key in configuration

See `reference/google-sheets-setup.md` for detailed instructions.

## Sheet Structure

### Tab: "Campaigns"
| Column | Description | Example |
|--------|-------------|---------|
| platform_id | Platform identifier | meta, google, spotify |
| campaign_name | Campaign name | English Reach Campaign |
| type | Campaign type | Reach, Lead Gen, Search |
| funnel_stage | Awareness/Consideration/Conversion | Awareness |
| objective | Campaign objective | Brand visibility |
| start_date | Start date (YYYY-MM-DD) | 2025-01-01 |
| end_date | End date (YYYY-MM-DD) | 2025-02-15 |
| daily_spend | Daily budget | 115 |
| total_spend | Total budget | 5290 |
| format | Ad format description | Awareness Campaign... |
| targeting | Targeting details | 100% AHI |
| status | Planned/Active/Completed | Planned |

### Tab: "Platforms"
| Column | Description | Example |
|--------|-------------|---------|
| id | Platform identifier | meta |
| name | Display name | Meta Ads |
| total_budget | Platform budget | 13455 |

### Tab: "Budget"
| Column | Description | Example |
|--------|-------------|---------|
| category | Budget category | Digital Campaigns |
| amount | Budget amount | 30650 |

### Tab: "Project"
| Column | Description | Example |
|--------|-------------|---------|
| field | Field name | name |
| value | Field value | The New Village |

## Implementation Approach

### 1. Create Project Structure

```
media-plan-dashboard/
├── src/
│   ├── components/
│   │   ├── MediaPlanDashboard.tsx    # Main dashboard
│   │   ├── BudgetDonut.tsx           # Budget visualization
│   │   ├── GanttChart.tsx            # Timeline/schedule
│   │   ├── FunnelVisualization.tsx   # Marketing funnel
│   │   ├── PlatformCard.tsx          # Platform details
│   │   └── ProjectionsTab.tsx        # Projections view
│   ├── hooks/
│   │   └── useGoogleSheets.ts        # Data fetching hook
│   ├── utils/
│   │   ├── sheetsApi.ts              # Sheets API utilities
│   │   └── dataTransform.ts          # Sheet → Dashboard mapper
│   ├── config/
│   │   └── platforms.ts              # Platform configurations
│   └── types/
│       └── campaign.ts               # TypeScript interfaces
├── public/
└── package.json
```

### 2. Google Sheets Hook

```typescript
// hooks/useGoogleSheets.ts
import { useState, useEffect, useCallback } from 'react';
import { transformSheetData } from '../utils/dataTransform';

interface UseGoogleSheetsOptions {
  sheetId: string;
  apiKey?: string;
  publishedUrls?: {
    campaigns: string;
    platforms: string;
    budget: string;
    project: string;
  };
  refreshInterval?: number; // ms
}

export function useGoogleSheets(options: UseGoogleSheetsOptions) {
  const [data, setData] = useState(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState(null);
  const [lastUpdated, setLastUpdated] = useState<Date | null>(null);

  const fetchData = useCallback(async () => {
    try {
      let rawData;

      if (options.publishedUrls) {
        // CSV approach
        rawData = await fetchPublishedCSV(options.publishedUrls);
      } else if (options.apiKey) {
        // API approach
        rawData = await fetchSheetsAPI(options.sheetId, options.apiKey);
      }

      const transformed = transformSheetData(rawData);
      setData(transformed);
      setLastUpdated(new Date());
      setError(null);
    } catch (err) {
      setError(err.message);
    } finally {
      setLoading(false);
    }
  }, [options]);

  useEffect(() => {
    fetchData();

    if (options.refreshInterval) {
      const interval = setInterval(fetchData, options.refreshInterval);
      return () => clearInterval(interval);
    }
  }, [fetchData, options.refreshInterval]);

  return { data, loading, error, lastUpdated, refetch: fetchData };
}
```

### 3. Data Transformation

```typescript
// utils/dataTransform.ts
export function transformSheetData(raw: SheetData): CampaignData {
  return {
    project: transformProject(raw.project),
    budget: transformBudget(raw.budget),
    audience: transformAudience(raw.audience),
    platforms: transformPlatforms(raw.platforms, raw.campaigns),
    projections: raw.projections ? transformProjections(raw.projections) : undefined,
    results: raw.results ? transformResults(raw.results) : undefined,
  };
}

function transformPlatforms(platforms: any[], campaigns: any[]): Platform[] {
  return platforms.map(p => ({
    id: p.id,
    name: p.name,
    color: platformConfig[p.id]?.color || '#666',
    totalBudget: parseFloat(p.total_budget),
    campaigns: campaigns
      .filter(c => c.platform_id === p.id)
      .map(transformCampaign)
  }));
}

function transformCampaign(c: any): Campaign {
  return {
    id: c.campaign_id || `${c.platform_id}-${c.campaign_name}`.toLowerCase().replace(/\s+/g, '-'),
    name: c.campaign_name,
    type: c.type,
    funnelStage: c.funnel_stage,
    objective: c.objective,
    startDate: c.start_date,
    endDate: c.end_date,
    dailySpend: parseFloat(c.daily_spend),
    totalSpend: parseFloat(c.total_spend),
    format: c.format,
    status: c.status || 'Planned',
    targeting: c.targeting
  };
}
```

## Platform Configuration

Supported platforms with logos from SimpleIcons CDN:

```typescript
const platformConfig = {
  'meta': { name: 'Meta Ads', logo: 'https://cdn.simpleicons.org/meta/1877F2', color: '#1877F2' },
  'facebook': { name: 'Facebook', logo: 'https://cdn.simpleicons.org/facebook/1877F2', color: '#1877F2' },
  'instagram': { name: 'Instagram', logo: 'https://cdn.simpleicons.org/instagram/E4405F', color: '#E4405F' },
  'google': { name: 'Google Ads', logo: 'https://cdn.simpleicons.org/googleads/4285F4', color: '#4285F4' },
  'linkedin': { name: 'LinkedIn', logo: 'https://cdn.simpleicons.org/linkedin/0A66C2', color: '#0A66C2' },
  'spotify': { name: 'Spotify Audio', logo: 'https://cdn.simpleicons.org/spotify/1DB954', color: '#1DB954' },
  'youtube': { name: 'YouTube', logo: 'https://cdn.simpleicons.org/youtube/FF0000', color: '#FF0000' },
  'tiktok': { name: 'TikTok', logo: 'https://cdn.simpleicons.org/tiktok/000000', color: '#000000' },
  'twitter': { name: 'Twitter/X', logo: 'https://cdn.simpleicons.org/x/000000', color: '#000000' },
  'pinterest': { name: 'Pinterest', logo: 'https://cdn.simpleicons.org/pinterest/E60023', color: '#E60023' },
  // Fallback to emoji for platforms without logos
  'programmatic': { name: 'Programmatic', emoji: '🎯', color: '#6B5B4F' },
  'ooh': { name: 'Out of Home', emoji: '🚏', color: '#8B7355' },
  'radio': { name: 'Radio', emoji: '📻', color: '#D4A574' },
  'podcast': { name: 'Podcast', emoji: '🎙️', color: '#8B7355' },
};
```

## Design Guidelines

This dashboard uses a refined, professional aesthetic:

### Typography
- **Display**: Cormorant Garamond (serif) for headers and large numbers
- **Body**: DM Sans for UI elements and body text

### Color Palette
- **Primary Background**: Warm cream gradient (#FAF8F5 → #F5F0E8 → #EDE6DB)
- **Text**: Deep brown (#2C2416)
- **Accents**: Warm copper (#D4A574), muted brown (#8B7355), forest green (#4A7C59)
- **Cards**: Clean white with subtle shadows

### Funnel Stage Colors
- **Awareness**: Warm copper (#D4A574)
- **Consideration**: Muted brown (#8B7355)
- **Conversion**: Forest green (#4A7C59)

## Deployment Options

### Static Hosting (Recommended for Published CSV)
- Vercel, Netlify, GitHub Pages
- No backend required
- Build once, deploy static files

### Self-Hosted with Backend (For API Key Security)
- Node.js/Express backend proxies Sheets API
- Keeps API key server-side
- Enables caching and rate limiting

### Docker Deployment
```dockerfile
FROM node:20-alpine AS builder
WORKDIR /app
COPY package*.json ./
RUN npm ci
COPY . .
RUN npm run build

FROM nginx:alpine
COPY --from=builder /app/dist /usr/share/nginx/html
EXPOSE 80
```

## Example Usage

```tsx
import { useGoogleSheets } from './hooks/useGoogleSheets';
import MediaPlanDashboard from './components/MediaPlanDashboard';

function App() {
  const { data, loading, error, lastUpdated } = useGoogleSheets({
    publishedUrls: {
      campaigns: 'https://docs.google.com/spreadsheets/d/SHEET_ID/export?format=csv&gid=0',
      platforms: 'https://docs.google.com/spreadsheets/d/SHEET_ID/export?format=csv&gid=123',
      budget: 'https://docs.google.com/spreadsheets/d/SHEET_ID/export?format=csv&gid=456',
      project: 'https://docs.google.com/spreadsheets/d/SHEET_ID/export?format=csv&gid=789',
    },
    refreshInterval: 60000 // Refresh every minute
  });

  if (loading) return <LoadingSpinner />;
  if (error) return <ErrorMessage error={error} />;

  return (
    <>
      <MediaPlanDashboard data={data} />
      <UpdateIndicator lastUpdated={lastUpdated} />
    </>
  );
}
```

## Security Considerations

1. **Never expose API keys in client-side code** - Use published CSV or a backend proxy
2. **Validate sheet data** - Don't trust spreadsheet input blindly
3. **Rate limit refreshes** - Avoid hammering the Sheets API
4. **Use read-only access** - Dashboard should only read, never write

## Customization Points

- **Branding**: Update logo, colors, and typography in CSS variables
- **Platforms**: Add/modify platform configurations
- **Metrics**: Customize which KPIs appear in projections
- **Phases**: Adapt phase structure to campaign timeline
- **Export**: Add PDF/image export functionality
