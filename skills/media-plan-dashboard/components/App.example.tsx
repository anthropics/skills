/**
 * Example App.tsx showing how to integrate the Media Plan Dashboard
 * with Google Sheets data fetching.
 *
 * This file demonstrates two approaches:
 * 1. Published CSV (simpler, no API key needed)
 * 2. Sheets API (more control, requires API key)
 */

import React from 'react';
import MediaPlanDashboard from './MediaPlanDashboard';
import { useGoogleSheets, generatePublishedUrls } from './useGoogleSheets';
import './MediaPlanDashboard.css';

// =============================================================================
// OPTION 1: Using Published CSV URLs (Recommended for simple setups)
// =============================================================================

/**
 * To use this approach:
 * 1. Open your Google Sheet
 * 2. Go to File > Share > Publish to web
 * 3. Select each tab and choose "Comma-separated values (.csv)"
 * 4. Copy the URL for each tab
 * 5. Note the 'gid' parameter in each URL
 */
function AppWithPublishedCSV() {
  // Replace with your actual Google Sheet ID and tab GIDs
  const SHEET_ID = 'your-google-sheet-id-here';

  const urls = generatePublishedUrls(SHEET_ID, {
    campaigns: 0,           // GID of your Campaigns tab
    platforms: 123456789,   // GID of your Platforms tab
    budget: 987654321,      // GID of your Budget tab
    project: 111222333,     // GID of your Project tab
    audience: 444555666,    // Optional: GID of your Audience tab
    projections: 777888999  // Optional: GID of your Projections tab
  });

  const { data, loading, error, lastUpdated, refetch } = useGoogleSheets({
    publishedUrls: urls,
    refreshInterval: 60000, // Refresh every minute
    debug: true // Enable console logging for debugging
  });

  if (loading && !data) {
    return <LoadingScreen />;
  }

  if (error && !data) {
    return <ErrorScreen error={error} onRetry={refetch} />;
  }

  if (!data) {
    return <ErrorScreen error="No data available" onRetry={refetch} />;
  }

  return (
    <>
      <MediaPlanDashboard data={data} />
      <UpdateIndicator lastUpdated={lastUpdated} onRefresh={refetch} />
    </>
  );
}

// =============================================================================
// OPTION 2: Using Google Sheets API (More control)
// =============================================================================

/**
 * To use this approach:
 * 1. Go to Google Cloud Console
 * 2. Create a project and enable Google Sheets API
 * 3. Create an API key and restrict it to Sheets API
 * 4. IMPORTANT: In production, proxy this through your backend!
 */
function AppWithSheetsAPI() {
  // WARNING: Never expose API keys in client-side code in production!
  // Use a backend proxy or environment variables with proper security
  const SHEET_ID = process.env.REACT_APP_SHEET_ID || '';
  const API_KEY = process.env.REACT_APP_SHEETS_API_KEY || '';

  const { data, loading, error, lastUpdated, refetch } = useGoogleSheets({
    sheetId: SHEET_ID,
    apiKey: API_KEY,
    refreshInterval: 300000, // Refresh every 5 minutes
    debug: process.env.NODE_ENV === 'development'
  });

  if (loading && !data) {
    return <LoadingScreen />;
  }

  if (error && !data) {
    return <ErrorScreen error={error} onRetry={refetch} />;
  }

  if (!data) {
    return <ErrorScreen error="No data available" onRetry={refetch} />;
  }

  return (
    <>
      <MediaPlanDashboard data={data} />
      <UpdateIndicator lastUpdated={lastUpdated} onRefresh={refetch} />
    </>
  );
}

// =============================================================================
// OPTION 3: Using Static/Demo Data (For development or demos)
// =============================================================================

import { demoData } from './demoData';

function AppWithDemoData() {
  return <MediaPlanDashboard data={demoData} />;
}

// =============================================================================
// UI Components
// =============================================================================

function LoadingScreen() {
  return (
    <div style={{
      minHeight: '100vh',
      display: 'flex',
      alignItems: 'center',
      justifyContent: 'center',
      background: 'linear-gradient(165deg, #FAF8F5 0%, #F5F0E8 50%, #EDE6DB 100%)',
      fontFamily: 'DM Sans, sans-serif'
    }}>
      <div style={{ textAlign: 'center' }}>
        <div style={{
          width: 48,
          height: 48,
          border: '3px solid #E8E4DE',
          borderTopColor: '#D4A574',
          borderRadius: '50%',
          animation: 'spin 1s linear infinite',
          margin: '0 auto 16px'
        }} />
        <p style={{ color: '#6B5B4F' }}>Loading campaign data...</p>
        <style>{`@keyframes spin { to { transform: rotate(360deg); }}`}</style>
      </div>
    </div>
  );
}

interface ErrorScreenProps {
  error: string;
  onRetry: () => void;
}

function ErrorScreen({ error, onRetry }: ErrorScreenProps) {
  return (
    <div style={{
      minHeight: '100vh',
      display: 'flex',
      alignItems: 'center',
      justifyContent: 'center',
      background: 'linear-gradient(165deg, #FAF8F5 0%, #F5F0E8 50%, #EDE6DB 100%)',
      fontFamily: 'DM Sans, sans-serif'
    }}>
      <div style={{
        textAlign: 'center',
        padding: 40,
        background: 'white',
        borderRadius: 16,
        boxShadow: '0 4px 24px rgba(0,0,0,0.08)',
        maxWidth: 400
      }}>
        <div style={{
          width: 64,
          height: 64,
          background: '#FFF0E6',
          borderRadius: '50%',
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
          margin: '0 auto 16px',
          fontSize: 28
        }}>⚠️</div>
        <h2 style={{
          fontFamily: 'Cormorant Garamond, serif',
          fontSize: 24,
          color: '#2C2416',
          marginBottom: 8
        }}>Unable to Load Data</h2>
        <p style={{
          color: '#6B5B4F',
          fontSize: 14,
          marginBottom: 20,
          lineHeight: 1.5
        }}>{error}</p>
        <button
          onClick={onRetry}
          style={{
            padding: '12px 24px',
            background: '#2C2416',
            color: 'white',
            border: 'none',
            borderRadius: 8,
            fontSize: 14,
            fontWeight: 500,
            cursor: 'pointer'
          }}
        >
          Try Again
        </button>
      </div>
    </div>
  );
}

interface UpdateIndicatorProps {
  lastUpdated: Date | null;
  onRefresh: () => void;
}

function UpdateIndicator({ lastUpdated, onRefresh }: UpdateIndicatorProps) {
  if (!lastUpdated) return null;

  return (
    <div style={{
      position: 'fixed',
      bottom: 20,
      right: 20,
      display: 'flex',
      alignItems: 'center',
      gap: 12,
      padding: '10px 16px',
      background: 'white',
      borderRadius: 8,
      boxShadow: '0 2px 12px rgba(0,0,0,0.1)',
      fontFamily: 'DM Sans, sans-serif',
      fontSize: 12,
      color: '#6B5B4F',
      zIndex: 1000
    }}>
      <span style={{
        width: 8,
        height: 8,
        background: '#4A7C59',
        borderRadius: '50%'
      }} />
      <span>
        Updated {lastUpdated.toLocaleTimeString()}
      </span>
      <button
        onClick={onRefresh}
        style={{
          padding: '4px 10px',
          background: '#F5F0E8',
          border: 'none',
          borderRadius: 4,
          fontSize: 11,
          color: '#2C2416',
          cursor: 'pointer'
        }}
      >
        Refresh
      </button>
    </div>
  );
}

// =============================================================================
// Export the app you want to use
// =============================================================================

// Uncomment the one you want to use:
export default AppWithPublishedCSV;
// export default AppWithSheetsAPI;
// export default AppWithDemoData;
