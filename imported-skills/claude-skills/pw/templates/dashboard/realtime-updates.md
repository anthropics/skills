# Realtime Updates Template

Tests live data via WebSocket or polling, connection handling, and reconnection.

## Prerequisites
- Authenticated session via `{{authStorageStatePath}}`
- Dashboard with live data at `{{baseUrl}}/dashboard`
- WebSocket endpoint: `{{wsEndpoint}}`

---

## TypeScript

```typescript
import { test, expect } from '@playwright/test';

test.describe('Realtime Updates', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  // Happy path: live metric updates via WebSocket
  test('updates metric when WebSocket message received', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByTestId('{{metricId}}')).toBeVisible();

    // Inject a WS message to simulate server push
    await page.evaluate(() => {
      const ws = (window as any).__dashboardWs;
      if (ws) ws.dispatchEvent(new MessageEvent('message', {
        data: JSON.stringify({ type: 'metric_update', id: '{{metricId}}', value: 9999 })
      }));
    });
    await expect(page.getByTestId('{{metricId}}')).toContainText('9,999');
  });

  // Happy path: connection status indicator
  test('shows "connected" status indicator', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByRole('status', { name: /live|connected/i })).toBeVisible();
  });

  // Happy path: data highlighted on update
  test('highlights updated value briefly', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.evaluate(() => {
      const ws = (window as any).__dashboardWs;
      if (ws) ws.dispatchEvent(new MessageEvent('message', {
        data: JSON.stringify({ type: 'metric_update', id: '{{metricId}}', value: 42 })
      }));
    });
    await expect(page.getByTestId('{{metricId}}')).toHaveClass(/updated|flash/);
    // Highlight fades
    await expect(page.getByTestId('{{metricId}}')).not.toHaveClass(/updated|flash/);
  });

  // Error case: WebSocket disconnected — shows offline indicator
  test('shows disconnected state when WebSocket closes', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.evaluate(() => {
      const ws = (window as any).__dashboardWs;
      if (ws) ws.close();
    });
    await expect(page.getByRole('status', { name: /disconnected|offline/i })).toBeVisible();
    await expect(page.getByText(/reconnecting/i)).toBeVisible();
  });

  // Error case: connection refused — error state shown
  test('shows connection error when WebSocket cannot connect', async ({ page }) => {
    await page.route('**/{{wsEndpoint}}', route => route.abort());
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByRole('alert')).toContainText(/connection.*failed|live updates.*unavailable/i);
  });

  // Edge case: reconnects automatically after disconnect
  test('reconnects automatically after network interruption', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.evaluate(() => {
      const ws = (window as any).__dashboardWs;
      if (ws) ws.close();
    });
    await expect(page.getByRole('status', { name: /disconnected/i })).toBeVisible();
    // Wait for auto-reconnect
    await expect(page.getByRole('status', { name: /connected|live/i })).toBeVisible();
  });

  // Edge case: stale data badge shown when disconnected
  test('shows stale data warning when disconnected', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.evaluate(() => {
      const ws = (window as any).__dashboardWs;
      if (ws) ws.close();
    });
    await expect(page.getByText(/data may be outdated|stale/i)).toBeVisible();
  });
});
```

---

## JavaScript

```javascript
const { test, expect } = require('@playwright/test');

test.describe('Realtime Updates', () => {
  test.use({ storageState: '{{authStorageStatePath}}' });

  test('shows connected status on load', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await expect(page.getByRole('status', { name: /live|connected/i })).toBeVisible();
  });

  test('shows disconnected state when WS closes', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.evaluate(() => {
      const ws = window.__dashboardWs;
      if (ws) ws.close();
    });
    await expect(page.getByRole('status', { name: /disconnected|offline/i })).toBeVisible();
  });

  test('updates metric on WS message', async ({ page }) => {
    await page.goto('{{baseUrl}}/dashboard');
    await page.evaluate(() => {
      const ws = window.__dashboardWs;
      if (ws) ws.dispatchEvent(new MessageEvent('message', {
        data: JSON.stringify({ type: 'metric_update', id: '{{metricId}}', value: 9999 })
      }));
    });
    await expect(page.getByTestId('{{metricId}}')).toContainText('9,999');
  });
});
```

## Variants
| Variant | Description |
|---------|-------------|
| Live update | WS message updates metric value |
| Connected status | Status indicator shows "live" |
| Update highlight | Changed value briefly highlighted |
| Disconnected | WS close → disconnected indicator |
| Connection refused | WS blocked → error alert |
| Auto-reconnect | Reconnects after close |
| Stale data | Warning shown while disconnected |
