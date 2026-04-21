# Continuous Integration and Continuous Deployment (CI/CD)

Continuous Integration and Continuous Deployment are there to ensure good code quality and create rapid and secure
deployments. Some best practices are:

1. Ensure every PR undergoes CI testing (e.g., GitHub Actions) that must pass before merging. CI tests should at least
  include unit tests, integration tests, and checks for known vulnerabilities in dependencies.
2. The CI/CD pipeline should check for misconfigurations and leaked credentials.
3. Produce deterministic builds with a strict set of dependencies and/or a build container that can reliably produce the
  same results on different machines.
4. Integrate security scanning tools to detect vulnerabilities in code and dependencies during the CI process.
5. Use isolated environments for building and testing to prevent contamination between different stages of the pipeline.
6. Implement strict access controls for CI/CD pipelines to limit who can modify the pipeline configurations.

---

