// Sample Java file demonstrating the Java-specific patterns the code-reviewer
// skill detects. Each smell is labelled inline. This file is NOT meant to
// compile cleanly — it is a fixture for code_quality_checker.py and
// pr_analyzer.py.
//
// Run:
//   python scripts/code_quality_checker.py assets/sample_java_smells.java
//
// Expected output: see expected_outputs/sample_java_smells_quality.json

package sample;

import java.io.FileInputStream;
import java.sql.Connection;
import java.sql.Statement;
import com.fasterxml.jackson.databind.ObjectMapper;

public class UserService {

    // [hardcoded_secrets] hardcoded JDBC URL with password
    public String connectionString = "jdbc:postgresql://prod/app?user=app&password=hunter2";

    // [analyzer_disable] @SuppressWarnings without justification
    @SuppressWarnings("unchecked")
    public String getName(Connection conn, int id) throws Exception {
        // [java_unclosed_resource] FileInputStream not in try-with-resources
        FileInputStream fis = new FileInputStream("/etc/config");

        // [java_per_use_heavy_object] new ObjectMapper() constructed per call
        ObjectMapper mapper = new ObjectMapper();

        try {
            Statement stmt = conn.createStatement();
            // [sql_concatenation] string concatenation builds SQL with user input
            return stmt.executeQuery("SELECT name FROM users WHERE id = " + id).toString();
        } catch (Exception e) {
            // [java_empty_catch] empty catch swallows the exception
        }
        return null;
    }

    public void process() {
        try {
            Thread.sleep(1000);
        } catch (InterruptedException e) {
            // [java_swallowed_interrupt] interrupt flag not restored
            // [console_log] printStackTrace used as error handling
            e.printStackTrace();
        }
    }

    public void log(String message) {
        // [console_log] System.out.println left in production code
        System.out.println(message);
    }
}
