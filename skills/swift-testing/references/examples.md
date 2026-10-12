# End-to-end example

Scenario:
- Launch app
- Login with valid creds
- Verify home is displayed
- Open settings
- Logout and verify login screen appears

Expected:
- Home title visible after login
- Login screen visible after logout

Output should include:
- LoginScreen, HomeScreen, SettingsScreen
- LoginFlowTests
- Identifier list:
  - login.email, login.password, login.submit
  - home.title, home.settingsButton
  - settings.logout
