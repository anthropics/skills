# Supply Chain Levels for Software Artifacts

Supply chain levels for software artifacts provide a framework for categorizing and securing software components based
on their risk levels. This approach helps projects prioritize their security efforts towards software components with
the highest risk levels.

## Framework for Supply Chain Levels

1. **Level 1: Critical Artifacts**
   - These artifacts are essential to the core functionality of the software and pose a high risk if compromised.
   - Examples: Core libraries.

2. **Level 2: High-Risk Artifacts**
   - Artifacts that are important but not critical. Their compromise could lead to significant security issues.
   - Examples: Middleware, database connectors, oracles, authentication modules.

3. **Level 3: Moderate-Risk Artifacts**
   - Artifacts that are used frequently but have a lower risk profile. Their compromise could cause inconvenience but
   not catastrophic failure.
   - Examples: User interface libraries, utility functions, data processing modules.

4. **Level 4: Low-Risk Artifacts**
   - Artifacts that have minimal impact on security if compromised.
   - Examples: Logging libraries, test utilities.

## Best Practices for Securing Supply Chain Levels

1. **Critical Artifacts**
   - Implement strict access controls and require code reviews for all changes.
   - Use robust security testing, including static and dynamic analysis.
   - Monitor continuously for vulnerabilities and apply patches promptly.

2. **High-Risk Artifacts**
   - Enforce strong access controls and conduct regular security assessments.
   - Perform regular updates and vulnerability scans.
   - Implement automated security testing in CI/CD pipelines.

3. **Moderate-Risk Artifacts**
   - Apply standard security practices, including access controls and regular updates.
   - Use automated tools to scan for vulnerabilities periodically.
   - Ensure that dependencies are from trusted sources.

4. **Low-Risk Artifacts**
   - Follow basic security hygiene, such as using trusted sources and applying updates.
   - Perform occasional security reviews and audits.

---

