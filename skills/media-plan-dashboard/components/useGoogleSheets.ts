import { useState, useEffect, useCallback } from 'react';
import { CampaignData } from './types';
import { transformSheetData, RawSheetData } from './dataTransform';

// =============================================================================
// GOOGLE SHEETS HOOK
// Fetches campaign data from Google Sheets and transforms it for the dashboard
// =============================================================================

interface PublishedUrls {
  campaigns: string;
  platforms: string;
  budget: string;
  project: string;
  audience?: string;
  projections?: string;
}

interface UseGoogleSheetsOptions {
  // Option 1: Use published CSV URLs (no API key needed)
  publishedUrls?: PublishedUrls;

  // Option 2: Use Sheets API (requires API key)
  sheetId?: string;
  apiKey?: string;

  // Refresh interval in milliseconds (default: no auto-refresh)
  refreshInterval?: number;

  // Enable debug logging
  debug?: boolean;
}

interface UseGoogleSheetsResult {
  data: CampaignData | null;
  loading: boolean;
  error: string | null;
  lastUpdated: Date | null;
  refetch: () => Promise<void>;
}

/**
 * Parse CSV string into array of objects
 */
function parseCSV(csvText: string): Record<string, string>[] {
  const lines = csvText.trim().split('\n');
  if (lines.length < 2) return [];

  // Parse header row
  const headers = parseCSVLine(lines[0]);

  // Parse data rows
  const data: Record<string, string>[] = [];
  for (let i = 1; i < lines.length; i++) {
    const values = parseCSVLine(lines[i]);
    const row: Record<string, string> = {};

    headers.forEach((header, index) => {
      // Normalize header names: lowercase, replace spaces with underscores
      const normalizedHeader = header.toLowerCase().trim().replace(/\s+/g, '_');
      row[normalizedHeader] = values[index]?.trim() || '';
    });

    // Skip empty rows
    if (Object.values(row).some(v => v !== '')) {
      data.push(row);
    }
  }

  return data;
}

/**
 * Parse a single CSV line, handling quoted values
 */
function parseCSVLine(line: string): string[] {
  const result: string[] = [];
  let current = '';
  let inQuotes = false;

  for (let i = 0; i < line.length; i++) {
    const char = line[i];

    if (char === '"') {
      if (inQuotes && line[i + 1] === '"') {
        // Escaped quote
        current += '"';
        i++;
      } else {
        // Toggle quote mode
        inQuotes = !inQuotes;
      }
    } else if (char === ',' && !inQuotes) {
      result.push(current);
      current = '';
    } else {
      current += char;
    }
  }

  result.push(current);
  return result;
}

/**
 * Fetch data from published Google Sheets CSV URLs
 */
async function fetchPublishedCSV(urls: PublishedUrls): Promise<RawSheetData> {
  const fetchSheet = async (url: string): Promise<Record<string, string>[]> => {
    const response = await fetch(url, {
      headers: { 'Accept': 'text/csv' }
    });

    if (!response.ok) {
      throw new Error(`Failed to fetch sheet: ${response.status} ${response.statusText}`);
    }

    const csvText = await response.text();
    return parseCSV(csvText);
  };

  // Fetch all sheets in parallel
  const [campaigns, platforms, budget, project, audience, projections] = await Promise.all([
    fetchSheet(urls.campaigns),
    fetchSheet(urls.platforms),
    fetchSheet(urls.budget),
    fetchSheet(urls.project),
    urls.audience ? fetchSheet(urls.audience) : Promise.resolve([]),
    urls.projections ? fetchSheet(urls.projections) : Promise.resolve([])
  ]);

  return {
    campaigns,
    platforms,
    budget,
    project,
    audience,
    projections
  };
}

/**
 * Fetch data from Google Sheets API
 */
async function fetchSheetsAPI(sheetId: string, apiKey: string): Promise<RawSheetData> {
  const baseUrl = `https://sheets.googleapis.com/v4/spreadsheets/${sheetId}/values`;

  const fetchRange = async (range: string): Promise<Record<string, string>[]> => {
    const url = `${baseUrl}/${encodeURIComponent(range)}?key=${apiKey}`;
    const response = await fetch(url);

    if (!response.ok) {
      throw new Error(`Failed to fetch range ${range}: ${response.status}`);
    }

    const data = await response.json();
    const values = data.values || [];

    if (values.length < 2) return [];

    const headers = values[0].map((h: string) =>
      h.toLowerCase().trim().replace(/\s+/g, '_')
    );

    return values.slice(1).map((row: string[]) => {
      const obj: Record<string, string> = {};
      headers.forEach((header: string, index: number) => {
        obj[header] = row[index]?.trim() || '';
      });
      return obj;
    });
  };

  // Fetch all ranges in parallel
  const [campaigns, platforms, budget, project, audience, projections] = await Promise.all([
    fetchRange('Campaigns'),
    fetchRange('Platforms'),
    fetchRange('Budget'),
    fetchRange('Project'),
    fetchRange('Audience').catch(() => []),
    fetchRange('Projections').catch(() => [])
  ]);

  return {
    campaigns,
    platforms,
    budget,
    project,
    audience,
    projections
  };
}

/**
 * Hook to fetch and transform Google Sheets data for the media plan dashboard
 *
 * @example Using published CSV (simpler, no API key)
 * ```tsx
 * const { data, loading, error } = useGoogleSheets({
 *   publishedUrls: {
 *     campaigns: 'https://docs.google.com/spreadsheets/d/SHEET_ID/export?format=csv&gid=0',
 *     platforms: 'https://docs.google.com/spreadsheets/d/SHEET_ID/export?format=csv&gid=123',
 *     budget: 'https://docs.google.com/spreadsheets/d/SHEET_ID/export?format=csv&gid=456',
 *     project: 'https://docs.google.com/spreadsheets/d/SHEET_ID/export?format=csv&gid=789',
 *   },
 *   refreshInterval: 60000 // Refresh every minute
 * });
 * ```
 *
 * @example Using Sheets API (more control)
 * ```tsx
 * const { data, loading, error } = useGoogleSheets({
 *   sheetId: 'your-sheet-id',
 *   apiKey: 'your-api-key', // Keep this server-side in production!
 *   refreshInterval: 300000 // Refresh every 5 minutes
 * });
 * ```
 */
export function useGoogleSheets(options: UseGoogleSheetsOptions): UseGoogleSheetsResult {
  const [data, setData] = useState<CampaignData | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [lastUpdated, setLastUpdated] = useState<Date | null>(null);

  const fetchData = useCallback(async () => {
    try {
      setLoading(true);
      setError(null);

      let rawData: RawSheetData;

      if (options.publishedUrls) {
        if (options.debug) console.log('[useGoogleSheets] Fetching from published CSV URLs');
        rawData = await fetchPublishedCSV(options.publishedUrls);
      } else if (options.sheetId && options.apiKey) {
        if (options.debug) console.log('[useGoogleSheets] Fetching from Sheets API');
        rawData = await fetchSheetsAPI(options.sheetId, options.apiKey);
      } else {
        throw new Error('Either publishedUrls or sheetId+apiKey must be provided');
      }

      if (options.debug) {
        console.log('[useGoogleSheets] Raw data:', rawData);
      }

      const transformed = transformSheetData(rawData);

      if (options.debug) {
        console.log('[useGoogleSheets] Transformed data:', transformed);
      }

      setData(transformed);
      setLastUpdated(new Date());
    } catch (err) {
      const message = err instanceof Error ? err.message : 'Unknown error fetching data';
      console.error('[useGoogleSheets] Error:', message);
      setError(message);
    } finally {
      setLoading(false);
    }
  }, [options.publishedUrls, options.sheetId, options.apiKey, options.debug]);

  useEffect(() => {
    fetchData();

    if (options.refreshInterval && options.refreshInterval > 0) {
      const interval = setInterval(fetchData, options.refreshInterval);
      return () => clearInterval(interval);
    }
  }, [fetchData, options.refreshInterval]);

  return { data, loading, error, lastUpdated, refetch: fetchData };
}

/**
 * Generate published CSV URLs from a Google Sheet ID
 *
 * @param sheetId The Google Sheet ID (from the URL)
 * @param gids Object mapping tab names to their gid numbers
 * @returns PublishedUrls object for use with useGoogleSheets
 *
 * @example
 * ```tsx
 * const urls = generatePublishedUrls('1ABC123xyz', {
 *   campaigns: 0,
 *   platforms: 123456789,
 *   budget: 987654321,
 *   project: 111222333
 * });
 * ```
 */
export function generatePublishedUrls(
  sheetId: string,
  gids: { campaigns: number; platforms: number; budget: number; project: number; audience?: number; projections?: number }
): PublishedUrls {
  const baseUrl = `https://docs.google.com/spreadsheets/d/${sheetId}/export?format=csv&gid=`;

  return {
    campaigns: `${baseUrl}${gids.campaigns}`,
    platforms: `${baseUrl}${gids.platforms}`,
    budget: `${baseUrl}${gids.budget}`,
    project: `${baseUrl}${gids.project}`,
    ...(gids.audience && { audience: `${baseUrl}${gids.audience}` }),
    ...(gids.projections && { projections: `${baseUrl}${gids.projections}` })
  };
}
