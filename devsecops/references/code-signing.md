# Code Signing

Code signing ensures that the code has not been tampered with, and verifies the identity of the developer. Here are some
best practices that could be followed:

1. Ensure all Pull Requests (PRs) are signed with the user’s GPG key.
2. Every PR must be reviewed by another core team member before being merged into the stable/main/master branch, with
  github settings set to reflect this.
3. Require Multi-Factor Authentication (MFA) for all users where applicable and available. Encourage the use of hardware
  MFA such as Yubikeys.
4. Rotate GPG keys regularly to mitigate the risk of key compromise.
5. Maintain clear documentation on the code signing procedures for your team members.

---

