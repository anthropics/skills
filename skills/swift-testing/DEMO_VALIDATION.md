# Test Run: "Login Scenario" using `swift-testing`

*This document demonstrates the output of the new `swift-testing` skill when processing a standard Login scenario.*

## Input Scenario
> "User opens the app, enters email 'test@example.com' and password 'password', taps login, and sees the Home screen title."

---

## Agent Output

### 1. Test Plan
1. Launch application.
2. Wait for Login screen to load (anchor: `login.title`).
3. Enter "test@example.com" into `login.email`.
4. Enter "password" into `login.password`.
5. Tap `login.submit`.
6. Wait for Home screen to load (anchor: `home.title`).
7. Assert `home.title` is visible.

### 2. Swift Test Code

```swift
import XCTest

final class LoginFlowTests: BaseUITestCase {

    func test_login_success_showsHome() {
        // Arrange
        let loginScreen = LoginScreen(app: app)
        let homeScreen = HomeScreen(app: app)

        // Act
        app.handleSystemAlertsIfPresent()
        
        loginScreen.assertLoaded()
        loginScreen.login(email: "test@example.com", password: "password")

        // Assert
        homeScreen.assertLoaded()
        XCTAssertTrue(homeScreen.screenTitle.exists, "Expected Home title to be visible after login")
    }
}
```

### 3. Screen Objects

```swift
import XCTest

struct LoginScreen {
    let app: XCUIApplication

    var title: XCUIElement { app.staticTexts["login.title"] }
    var emailField: XCUIElement { app.textFields["login.email"] }
    var passwordField: XCUIElement { app.secureTextFields["login.password"] }
    var submitButton: XCUIElement { app.buttons["login.submit"] }

    func assertLoaded(file: StaticString = #file, line: UInt = #line) {
        title.waitForVisible(file: file, line: line)
    }

    func login(email: String, password: String) {
        emailField.clearAndTypeText(email)
        passwordField.clearAndTypeText(password)
        submitButton.tapWhenHittable()
    }
}

struct HomeScreen {
    let app: XCUIApplication

    var screenTitle: XCUIElement { app.staticTexts["home.title"] }

    func assertLoaded(file: StaticString = #file, line: UInt = #line) {
        screenTitle.waitForVisible(timeout: 10, file: file, line: line)
    }
}
```

### 4. Accessibility identifiers required
- `login.title` (StaticText)
- `login.email` (TextField)
- `login.password` (SecureTextField)
- `login.submit` (Button)
- `home.title` (StaticText)

### 5. Stability notes
- **Waits**: Used `waitForVisible` for screen anchors (`login.title`, `home.title`).
- **Keyboard**: `clearAndTypeText` handles focus; if keyboard issues arise, consider adding `app.dismissKeyboard()` in `login()`.
- **Alerts**: Included `app.handleSystemAlertsIfPresent()` at start of flow.
