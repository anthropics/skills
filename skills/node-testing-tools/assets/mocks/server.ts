import { setupServer } from 'msw/node';
import { rest } from 'msw';

// ============================================================================
// MSW Request Handlers
// ============================================================================
// Add your API endpoints here that you want to mock in tests
// MSW will intercept fetch/XHR requests and respond with these handlers

export const server = setupServer(
  // Example: GET user by ID
  rest.get('/api/users/:id', (req, res, ctx) => {
    const { id } = req.params;
    return res(
      ctx.json({
        id,
        name: 'Test User',
        email: `user-${id}@example.com`,
      })
    );
  }),

  // Example: POST create user
  rest.post('/api/users', async (req, res, ctx) => {
    const body = await req.json();
    return res(
      ctx.status(201),
      ctx.json({
        id: '123',
        ...body,
      })
    );
  }),

  // Example: GET list users with query params
  rest.get('/api/users', (req, res, ctx) => {
    const page = req.url.searchParams.get('page') || '1';
    const limit = req.url.searchParams.get('limit') || '10';

    return res(
      ctx.json({
        data: Array.from({ length: parseInt(limit) }, (_, i) => ({
          id: String(i + 1),
          name: `User ${i + 1}`,
          email: `user-${i + 1}@example.com`,
        })),
        pagination: { page: parseInt(page), limit: parseInt(limit) },
      })
    );
  }),

  // Example: GET health check
  rest.get('/api/health', (req, res, ctx) => {
    return res(ctx.json({ status: 'ok' }));
  })
);

// ============================================================================
// Server Lifecycle
// ============================================================================
// In vitest.setup.ts:
//   beforeAll(() => server.listen({ onUnhandledRequest: 'error' }));
//   afterEach(() => server.resetHandlers());
//   afterAll(() => server.close());
