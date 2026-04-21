# Repository Hardening

If a threat actor obtains access to your repository, it could have very severe consequences. In order to help avoid
this, you could consider implementing the following best practices:

1. Require Multi-Factor Authentication (MFA) for all repository members.
2. Enable protected branches to prevent unauthorized changes to critical branches. [Learn more about protected
  branches](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches/about-protected-branches).
3. Follow the [Security hardening for GitHub
  Actions](https://docs.github.com/en/actions/security-guides/security-hardening-for-github-actions) to avoid token
  stealing and other vulnerabilities.
4. Implement strict access controls to limit who can push to critical branches and repositories.
5. Conduct regular security audits of the repository to identify and mitigate potential vulnerabilities.
6. Require all commits to be signed to verify the identity of contributors and ensure the integrity of the code.
7. Regularly update dependencies and use tools to check for and manage vulnerabilities in dependencies.

---

