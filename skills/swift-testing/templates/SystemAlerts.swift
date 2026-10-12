import XCTest

extension XCUIApplication {
    /// Handles common iOS permission alerts if they appear.
    /// Safe to call anytime (no-op if no alert).
    func handleSystemAlertsIfPresent(timeout: TimeInterval = 2) {
        let alert = self.alerts.firstMatch
        guard alert.waitForExistence(timeout: timeout) else { return }

        // Try common button titles; adjust for your locale/environment as needed.
        let allow = alert.buttons["Allow"]
        let allowWhileUsing = alert.buttons["Allow While Using App"]
        let ok = alert.buttons["OK"]
        let dontAllow = alert.buttons["Don’t Allow"]

        if allow.exists { allow.tap(); return }
        if allowWhileUsing.exists { allowWhileUsing.tap(); return }
        if ok.exists { ok.tap(); return }

        // Conservative fallback: dismiss without granting if required by policy
        if dontAllow.exists { dontAllow.tap(); return }
    }
}
