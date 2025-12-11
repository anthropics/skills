import { afterAll, afterEach, beforeAll, vi } from 'vitest';
import { server } from './src/mocks/server';

// ============================================================================
// MSW Setup - API Mocking
// ============================================================================

beforeAll(() => {
  console.log('🔧 Starting MSW server...');
  server.listen({ onUnhandledRequest: 'error' });
});

afterEach(() => {
  // Reset all request handlers after each test
  // This allows you to override specific handlers in individual tests
  server.resetHandlers();
});

afterAll(() => {
  console.log('🔧 Stopping MSW server...');
  server.close();
});

// ============================================================================
// Global Test Utilities
// ============================================================================

// Create test ID selector helper
global.testId = (id: string) => `[data-testid="${id}"]`;

// Mock window.matchMedia for responsive tests
Object.defineProperty(window, 'matchMedia', {
  writable: true,
  value: vi.fn().mockImplementation((query) => ({
    matches: false,
    media: query,
    onchange: null,
    addListener: vi.fn(),
    removeListener: vi.fn(),
    addEventListener: vi.fn(),
    removeEventListener: vi.fn(),
    dispatchEvent: vi.fn(),
  })),
});

// Mock IntersectionObserver
global.IntersectionObserver = class IntersectionObserver {
  constructor() {}
  disconnect() {}
  observe() {}
  takeRecords() {
    return [];
  }
  unobserve() {}
} as any;

// Suppress console errors in tests (optional)
// const originalError = console.error;
// beforeAll(() => {
//   console.error = vi.fn();
// });
// afterAll(() => {
//   console.error = originalError;
// });
