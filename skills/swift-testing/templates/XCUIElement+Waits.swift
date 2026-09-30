import XCTest

extension XCUIElement {
    @discardableResult
    func waitForVisible(timeout: TimeInterval = 10,
                        file: StaticString = #file,
                        line: UInt = #line) -> Bool {
        let exists = self.waitForExistence(timeout: timeout)
        XCTAssertTrue(exists, "Expected element to exist within \(timeout)s.", file: file, line: line)
        return exists
    }

    func waitForHittable(timeout: TimeInterval = 10,
                         file: StaticString = #file,
                         line: UInt = #line) {
        let predicate = NSPredicate(format: "exists == true AND hittable == true")
        let exp = XCTNSPredicateExpectation(predicate: predicate, object: self)
        let result = XCTWaiter().wait(for: [exp], timeout: timeout)
        XCTAssertEqual(result, .completed, "Expected element to be hittable within \(timeout)s.", file: file, line: line)
    }

    func tapWhenHittable(timeout: TimeInterval = 10,
                         file: StaticString = #file,
                         line: UInt = #line) {
        waitForHittable(timeout: timeout, file: file, line: line)
        tap()
    }

    func clearAndTypeText(_ text: String,
                          file: StaticString = #file,
                          line: UInt = #line) {
        waitForHittable(timeout: 10, file: file, line: line)
        tap()

        if let existing = self.value as? String, !existing.isEmpty {
            let deleteString = String(repeating: XCUIKeyboardKey.delete.rawValue, count: existing.count)
            typeText(deleteString)
        }
        typeText(text)
    }
}
