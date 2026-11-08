import XCTest

struct ScreenTemplate {
    let app: XCUIApplication

    // MARK: - Elements (use accessibilityIdentifier strings)
    var screenTitle: XCUIElement { app.staticTexts["screen.title"] }

    // MARK: - Assertions
    func assertLoaded(file: StaticString = #file, line: UInt = #line) {
        screenTitle.waitForVisible(timeout: 10, file: file, line: line)
    }

    // MARK: - Actions
    func doPrimaryAction() {
        // Example:
        // app.buttons["screen.primaryAction"].tapWhenHittable()
    }
}
