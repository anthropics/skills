import XCTest

extension XCUIApplication {
    func scrollToMakeVisible(_ element: XCUIElement,
                             in container: XCUIElement? = nil,
                             maxSwipes: Int = 8,
                             file: StaticString = #file,
                             line: UInt = #line) {
        let scrollContainer = container ?? self.scrollViews.firstMatch

        XCTAssertTrue(scrollContainer.exists, "No scroll container found.", file: file, line: line)

        var swipes = 0
        while !element.exists && swipes < maxSwipes {
            scrollContainer.swipeUp()
            swipes += 1
        }

        XCTAssertTrue(element.exists,
                      "Element not found after \(maxSwipes) swipes.",
                      file: file,
                      line: line)
    }
}
