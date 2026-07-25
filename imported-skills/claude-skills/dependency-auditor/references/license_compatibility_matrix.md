# License Compatibility Matrix

This document provides a comprehensive reference for understanding license compatibility when combining open source software dependencies in your projects.

## Understanding License Types

### Permissive Licenses
- **MIT License**: Very permissive, allows commercial use, modification, and distribution
- **Apache 2.0**: Permissive with patent grant and trademark restrictions
- **BSD 3-Clause**: Permissive with non-endorsement clause
- **BSD 2-Clause**: Simple permissive license
- **ISC License**: Functionally equivalent to MIT

### Weak Copyleft Licenses
- **LGPL 2.1/3.0**: Library-level copyleft, allows linking but requires modifications to be shared
- **MPL 2.0**: File-level copyleft, compatible with many licenses

### Strong Copyleft Licenses
- **GPL 2.0/3.0**: Requires entire derivative work to be GPL-licensed
- **AGPL 3.0**: Extends GPL to network services (SaaS applications)

## Compatibility Matrix

| Project License | MIT | Apache-2.0 | BSD-3 | LGPL-2.1 | LGPL-3.0 | MPL-2.0 | GPL-2.0 | GPL-3.0 | AGPL-3.0 |
|----------------|-----|------------|-------|----------|----------|---------|---------|---------|----------|
| **MIT**        | ✅   | ✅          | ✅     | ⚠️        | ⚠️        | ⚠️       | ❌       | ❌       | ❌        |
| **Apache-2.0** | ✅   | ✅          | ✅     | ❌        | ⚠️        | ✅       | ❌       | ⚠️       | ⚠️        |
| **BSD-3**      | ✅   | ✅          | ✅     | ⚠️        | ⚠️        | ⚠️       | ❌       | ❌       | ❌        |
| **LGPL-2.1**   | ✅   | ❌          | ✅     | ✅        | ❌        | ❌       | ✅       | ❌       | ❌        |
| **LGPL-3.0**   | ✅   | ✅          | ✅     | ❌        | ✅        | ✅       | ❌       | ✅       | ✅        |
| **MPL-2.0**    | ✅   | ✅          | ✅     | ❌        | ✅        | ✅       | ❌       | ✅       | ✅        |
| **GPL-2.0**    | ✅   | ❌          | ✅     | ✅        | ❌        | ❌       | ✅       | ❌       | ❌        |
| **GPL-3.0**    | ✅   | ✅          | ✅     | ❌        | ✅        | ✅       | ❌       | ✅       | ✅        |
| **AGPL-3.0**   | ✅   | ✅          | ✅     | ❌        | ✅        | ✅       | ❌       | ✅       | ✅        |

**Legend:**
- ✅ Generally Compatible
- ⚠️ Compatible with conditions/restrictions
- ❌ Incompatible

## Detailed Compatibility Rules

### MIT Project with Other Licenses

**Compatible:**
- MIT, Apache-2.0, BSD (all variants), ISC: Full compatibility
- LGPL 2.1/3.0: Can use LGPL libraries via dynamic linking
- MPL 2.0: Can use MPL modules, must keep MPL files under MPL

**Incompatible:**
- GPL 2.0/3.0: GPL requires entire project to be GPL
- AGPL 3.0: AGPL extends to network services

### Apache 2.0 Project with Other Licenses

**Compatible:**
- MIT, BSD, ISC: Full compatibility
- LGPL 3.0: Compatible (LGPL 3.0 has Apache compatibility clause)
- MPL 2.0: Compatible
- GPL 3.0: Compatible (GPL 3.0 has Apache compatibility clause)

**Incompatible:**
- LGPL 2.1: License incompatibility
- GPL 2.0: License incompatibility (no Apache clause)

### GPL Projects

**GPL 2.0 Compatible:**
- MIT, BSD, ISC: Can incorporate permissive code
- LGPL 2.1: Compatible
- Other GPL 2.0: Compatible

**GPL 2.0 Incompatible:**
- Apache 2.0: Different patent clauses
- LGPL 3.0: Version incompatibility
- GPL 3.0: Version incompatibility

**GPL 3.0 Compatible:**
- All permissive licenses (MIT, Apache, BSD, ISC)
- LGPL 3.0: Version compatibility
- MPL 2.0: Explicit compatibility

## Common Compatibility Scenarios

### Scenario 1: Permissive Project with GPL Dependency
**Problem:** MIT-licensed project wants to use GPL library
**Impact:** Entire project must become GPL-licensed
**Solutions:**
1. Find alternative non-GPL library
2. Use dynamic linking (if possible)
3. Change project license to GPL
4. Remove the dependency

### Scenario 2: Apache Project with GPL 2.0 Dependency
**Problem:** Apache 2.0 project with GPL 2.0 dependency
**Impact:** License incompatibility due to patent clauses
**Solutions:**
1. Upgrade to GPL 3.0 if available
2. Find alternative library
3. Use via separate service (API boundary)

### Scenario 3: Commercial Product with AGPL Dependency
**Problem:** Proprietary software using AGPL library
**Impact:** AGPL copyleft extends to network services
**Solutions:**
1. Obtain commercial license
2. Replace with permissive alternative
3. Use via separate service with API boundary
4. Make entire application AGPL

## License Combination Rules

### Safe Combinations
1. **Permissive + Permissive**: Always safe
2. **Permissive + Weak Copyleft**: Usually safe with proper attribution
3. **GPL + Compatible Permissive**: Safe, result is GPL

### Risky Combinations
1. **Apache 2.0 + GPL 2.0**: Incompatible patent terms
2. **Different GPL versions**: Version compatibility issues
3. **Permissive + Strong Copyleft**: Changes project licensing

### Forbidden Combinations
1. **MIT + GPL** (without relicensing)
2. **Proprietary + Any Copyleft**
3. **LGPL 2.1 + Apache 2.0**

## Distribution Considerations

### Binary Distribution
- Must include all required license texts
- Must preserve copyright notices
- Must include source code for copyleft licenses
- Must provide installation instructions for LGPL

### Source Distribution
- Must include original license files
- Must preserve copyright headers
- Must document any modifications
- Must provide clear licensing information

### SaaS/Network Services
- AGPL extends copyleft to network services
- GPL/LGPL generally don't apply to network services
- Consider service boundaries carefully

## Compliance Best Practices

### 1. License Inventory
- Maintain complete list of all dependencies
- Track license changes in updates
- Document license obligations

### 2. Compatibility Checking
- Use automated tools for license scanning
- Implement CI/CD license gates
- Regular compliance audits

### 3. Documentation
- Clear project license declaration
- Complete attribution files
- License change history

### 4. Legal Review
- Consult legal counsel for complex scenarios
- Review before major releases
- Consider business model implications

## Risk Mitigation Strategies

### High-Risk Licenses
- **AGPL**: Avoid in commercial/proprietary projects
- **GPL in permissive projects**: Plan migration strategy
- **Unknown licenses**: Investigate immediately

### Medium-Risk Scenarios
- **Version incompatibilities**: Upgrade when possible
- **Patent clause conflicts**: Seek legal advice
- **Multiple copyleft licenses**: Verify compatibility

### Risk Assessment Framework
1. **Identify** all dependencies and their licenses
2. **Classify** by license type and risk level
3. **Analyze** compatibility with project license
4. **Document** decisions and rationale
5. **Monitor** for license changes

## Common Misconceptions

### ❌ Wrong Assumptions
- "MIT allows everything" (still requires attribution)
- "Linking doesn't create derivatives" (depends on license)
- "GPL only affects distribution" (AGPL affects network use)
- "Commercial use is always forbidden" (most FOSS allows it)

### ✅ Correct Understanding
- Each license has specific requirements
- Combination creates most restrictive terms
- Network use may trigger copyleft (AGPL)
- Commercial licensing options often available

## Quick Reference Decision Tree

```
Is the dependency GPL/AGPL?
├─ YES → Is your project commercial/proprietary?
│   ├─ YES → ❌ Incompatible (find alternative)
│   └─ NO → ✅ Compatible (if same GPL version)
└─ NO → Is it permissive (MIT/Apache/BSD)?
    ├─ YES → ✅ Generally compatible
    └─ NO → Check specific compatibility matrix
```

## Tools and Resources

### Automated Tools
- **FOSSA**: Commercial license scanning
- **WhiteSource**: Enterprise license management
- **ORT**: Open source license scanning
- **License Finder**: Ruby-based license detection

### Manual Review Resources
- **choosealicense.com**: License picker and comparison
- **SPDX License List**: Standardized license identifiers
- **FSF License List**: Free Software Foundation compatibility
- **OSI Approved Licenses**: Open Source Initiative approved licenses

## Conclusion

License compatibility is crucial for legal compliance and risk management. When in doubt:

1. **Choose permissive licenses** for maximum compatibility
2. **Avoid strong copyleft** in proprietary projects
3. **Document all license decisions** thoroughly
4. **Consult legal experts** for complex scenarios
5. **Use automated tools** for continuous monitoring

Remember: This matrix provides general guidance but legal requirements may vary by jurisdiction and specific use cases. Always consult with legal counsel for important licensing decisions.