import XCTest

class BaseUITestCase: XCTestCase {
    let app = XCUIApplication()

    override func setUp() {
        super.setUp()
        continueAfterFailure = false

        // Prefer deterministic state.
        // If your app supports it, consider:
        // app.launchArguments += ["-uiTesting"]
        // app.launchEnvironment["UITEST_DISABLE_ANIMATIONS"] = "1"

        app.launch()
    }

    override func tearDown() {
        defer { super.tearDown() }

        guard let run = testRun, run.hasSucceeded == false else { return }

        let screenshot = XCUIScreen.main.screenshot()
        let attachment = XCTAttachment(screenshot: screenshot)
        attachment.name = "Failure Screenshot"
        attachment.lifetime = .keepAlways
        add(attachment)
    }
}
