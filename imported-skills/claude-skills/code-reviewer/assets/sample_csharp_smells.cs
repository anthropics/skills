// Sample C# file demonstrating every C#-specific pattern the code-reviewer
// skill detects. Each smell is labelled inline. This file is NOT meant to
// compile cleanly — it is a fixture for code_quality_checker.py and
// pr_analyzer.py.
//
// Run:
//   python scripts/code_quality_checker.py assets/sample_csharp_smells.cs
//
// Expected output: see expected_outputs/sample_csharp_smells_quality.json

using System;
using System.Net.Http;
using System.Threading.Tasks;
using System.Data.SqlClient;
using System.Diagnostics.CodeAnalysis;

namespace Sample
{
    public class UserService
    {
        // [hardcoded_secrets] hardcoded connection string with password
        public string ConnectionString = "Server=prod;Database=app;Password=hunter2;";

        // [csharp_async_void] async void on a non-event-handler signature
        public async void HandleClick(object sender, EventArgs e)
        {
            // [csharp_blocking_async] .Result blocks on Task in a sync context
            var data = FetchAsync().Result;
            // [console_log] Debug.WriteLine output statement
            Debug.WriteLine(data);
        }

        public async Task<string> FetchAsync()
        {
            // [csharp_new_httpclient] new HttpClient() in method body
            // [csharp_undisposed_idisposable] HttpClient not in `using`
            var client = new HttpClient();

            try
            {
                // [csharp_missing_await] FireAndForgetAsync() returns Task, never awaited
                FireAndForgetAsync();

                // [csharp_null_forgiving] `user!.Name` forces null-forgiving
                var name = user!.Name;

                return await client.GetStringAsync("https://api.example/data");
            }
            catch (Exception)
            {
                // [csharp_swallowed_exception] empty catch (Exception)
            }
            return null!;
        }

        // [loose_type] C# `dynamic` overuse
        public dynamic Untyped = null;

        // [csharp_unsafe_block] `unsafe` modifier on a method
        public unsafe void Pointers()
        {
            int x = 0;
            int* p = &x;
        }

        // [analyzer_disable] #pragma warning disable
        #pragma warning disable CS0168
        // [analyzer_disable] [SuppressMessage] attribute
        [SuppressMessage("Style", "IDE0060")]
        public string GetName(SqlConnection conn, int id)
        {
            // [csharp_undisposed_idisposable] SqlCommand without `using`
            // [sql_concatenation] string concatenation builds SQL with user input
            var cmd = new SqlCommand("SELECT name FROM users WHERE id = " + id, conn);
            return cmd.ExecuteScalar().ToString();
        }
    }
}
