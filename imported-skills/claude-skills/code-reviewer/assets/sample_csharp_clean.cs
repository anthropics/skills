// Sample C# file showing the fixed version of sample_csharp_smells.cs.
// Same shape, but every smell has been resolved per the patterns documented
// in rules/universal.md and languages/csharp.md.
//
// Run:
//   python scripts/code_quality_checker.py assets/sample_csharp_clean.cs
//
// Expected: no HIGH C#-specific smells flagged.

using System;
using System.Net.Http;
using System.Threading.Tasks;
using System.Data.SqlClient;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;

namespace Sample
{
    public class DbOptions
    {
        // FIX: connection string from configuration, never inlined.
        public string ConnectionString { get; init; } = "";
    }

    public class UserService
    {
        private readonly string _connectionString;
        private readonly HttpClient _httpClient;
        private readonly ILogger<UserService> _logger;

        // FIX: IHttpClientFactory + IOptions, no hardcoded secrets, no `new HttpClient()`.
        public UserService(
            IHttpClientFactory httpClientFactory,
            IOptions<DbOptions> dbOptions,
            ILogger<UserService> logger)
        {
            _httpClient = httpClientFactory.CreateClient("api");
            _connectionString = dbOptions.Value.ConnectionString;
            _logger = logger;
        }

        // FIX: async Task (not async void) so callers can await and observe exceptions.
        public async Task HandleClickAsync()
        {
            // FIX: await the Task instead of blocking on it.
            var data = await FetchAsync().ConfigureAwait(false);
            _logger.LogInformation("Fetched {Length} bytes", data.Length);
        }

        public async Task<string> FetchAsync()
        {
            try
            {
                // FIX: await the async call — Task is no longer discarded.
                await FireAndForgetAsync().ConfigureAwait(false);

                // FIX: real null check, no `!`.
                var user = await GetCurrentUserAsync().ConfigureAwait(false);
                if (user is null)
                {
                    throw new InvalidOperationException("No current user");
                }
                _ = user.Name;

                return await _httpClient
                    .GetStringAsync("https://api.example/data")
                    .ConfigureAwait(false);
            }
            catch (HttpRequestException ex)
            {
                // FIX: catch specific exception, log with context, rethrow.
                _logger.LogError(ex, "Upstream fetch failed");
                throw;
            }
        }

        // FIX: real type, not `dynamic`.
        public User? CurrentUser { get; private set; }

        // FIX: `unsafe` removed — none of the logic actually needed pointers.
        public int FirstValue(int[] values) => values.Length > 0 ? values[0] : 0;

        // FIX: no #pragma / [SuppressMessage] — root cause fixed instead.
        public string GetName(int id)
        {
            // FIX: `using var` disposes connection + command deterministically.
            using var conn = new SqlConnection(_connectionString);
            // FIX: parameterized query, no string concatenation.
            using var cmd = new SqlCommand("SELECT name FROM users WHERE id = @id", conn);
            cmd.Parameters.AddWithValue("@id", id);
            conn.Open();
            return (string)cmd.ExecuteScalar();
        }

        private Task<User?> GetCurrentUserAsync() => Task.FromResult<User?>(null);
        private Task FireAndForgetAsync() => Task.CompletedTask;
    }

    public record User(int Id, string Name);
}
