// Sample Java file showing the fixed version of sample_java_smells.java.
// Same shape, but every smell has been resolved per the patterns documented
// in rules/universal.md and languages/java.md.
//
// Run:
//   python scripts/code_quality_checker.py assets/sample_java_clean.java
//
// Expected: no HIGH Java-specific smells flagged.

package sample;

import java.io.FileInputStream;
import java.io.InputStream;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import com.fasterxml.jackson.databind.ObjectMapper;

public class UserService {

    // FIX: heavy object shared as a singleton instead of constructed per call.
    private static final ObjectMapper MAPPER = new ObjectMapper();

    // FIX: connection string injected from configuration, never inlined.
    private final String connectionString;

    public UserService(String connectionString) {
        this.connectionString = connectionString;
    }

    public String getName(Connection conn, int id) {
        // FIX: try-with-resources guarantees the stream and statement close.
        try (InputStream config = new FileInputStream("/etc/config");
             // FIX: parameterized query, no string concatenation.
             PreparedStatement stmt =
                 conn.prepareStatement("SELECT name FROM users WHERE id = ?")) {
            stmt.setInt(1, id);
            try (ResultSet rs = stmt.executeQuery()) {
                return rs.next() ? rs.getString("name") : null;
            }
        } catch (Exception e) {
            // FIX: rethrow with context instead of swallowing.
            throw new IllegalStateException("Failed to load user " + id, e);
        }
    }

    public void process() {
        try {
            Thread.sleep(1000);
        } catch (InterruptedException e) {
            // FIX: restore the interrupt flag so cancellation still propagates.
            Thread.currentThread().interrupt();
        }
    }
}
