---
name: unity3d-enhanced
description: Advanced Unity3D development guidance covering common pitfalls, API migrations, and best practices for both 2D and 3D projects. Use when working with Unity projects, especially for debugging build errors, setting up project configurations, handling Unity API changes, or troubleshooting runtime exceptions.
license: Complete terms in LICENSE.txt
---

# Unity3D Enhanced Development Guide

This skill provides expert guidance for Unity3D development based on real-world lessons learned from both 2D and 3D Unity projects. It helps you avoid common pitfalls, debug complex errors, and follow best practices.

## When to Use This Skill

Use this skill when working with:
- Unity build errors or runtime exceptions
- Project configuration (Input System, URP, Physics)
- Asset references, GUIDs, and meta files
- Unity API migrations between versions
- Physics setup (Rigidbody, triggers, collisions)
- Imported models and camera setups
- Performance optimization
- Version control with Unity projects

## How to Use This Skill

To solve Unity development issues:

1. **Identify the issue category** from your error or task
2. **Run diagnostic scripts** from the `scripts/` directory (optional but recommended):
   - `scripts/guid_validator.py` - Validate all GUIDs, find duplicates and invalid formats
   - `scripts/meta_file_checker.py` - Check meta file synchronization with git
   - `scripts/project_health_check.py` - Comprehensive project configuration check
3. **Load the appropriate reference file** from the `reference/` directory:
   - `reference/guid-system.md` - GUID errors, meta files, asset references, prefabs
   - `reference/input-systems.md` - Input System setup, API migration, common errors
   - `reference/physics-system.md` - Rigidbody, triggers vs collisions, fast-moving objects
   - `reference/urp-setup.md` - Universal Render Pipeline, camera configuration
   - `reference/common-errors.md` - Catalog of common Unity errors and solutions
   - `reference/project-setup.md` - Project setup checklist, workflows, best practices
4. **Follow the specific instructions** in that file to diagnose and fix the issue
5. **Check examples** in the `examples/` directory for quick reference:
   - `examples/quick-fixes.md` - Common issues with one-line fixes

If the issue doesn't match any category, search the reference files for keywords from your error message, or ask for more context.

## Workflow

### For Build/Runtime Errors

1. **Identify error message** from Unity Console or build output
2. **Run diagnostic script** (optional): `python scripts/guid_validator.py <project_path>`
3. **Search keywords** in `reference/common-errors.md`
4. **Apply solution** from the matching error pattern
5. **Verify fix** by rebuilding or running the project

### For Project Setup

1. **Run health check** (optional): `python scripts/project_health_check.py <project_path>`
2. **Review checklist** in `reference/project-setup.md`
3. **Configure settings** before writing code
4. **Verify configuration** matches your requirements
5. **Test in Play mode** to ensure settings work

### For API Migrations

1. **Check Unity version** you're migrating to
2. **Review relevant API changes** in reference files
3. **Update code** following the migration examples
4. **Test thoroughly** after each change

### For Performance Issues

1. **Identify bottleneck** (Physics? Rendering? Input?)
2. **Load relevant reference** (e.g., `physics-system.md` for physics)
3. **Apply optimization strategies** from best practices section
4. **Profile with Unity Profiler** to verify improvements

## Diagnostic Scripts

The skill includes Python scripts for automated project validation:

### `scripts/guid_validator.py`
Validates GUIDs in Unity projects:
- Checks for invalid GUID formats (non-hexadecimal characters)
- Detects duplicate GUIDs across meta files
- Finds orphaned meta files without corresponding assets
- Identifies missing meta files

**Usage**: `python scripts/guid_validator.py <project_path> [--fix-orphaned]`

### `scripts/meta_file_checker.py`
Ensures meta files are synchronized with version control:
- Detects staged assets without meta files
- Finds orphaned meta files in git
- Validates git workflow for Unity assets

**Usage**: `python scripts/meta_file_checker.py <project_path> --check-git`

### `scripts/project_health_check.py`
Comprehensive project configuration check:
- Validates Input System configuration
- Checks URP setup
- Verifies version control settings
- Validates .gitignore configuration
- Checks physics settings

**Usage**: `python scripts/project_health_check.py <project_path>`

## Key Unity Concepts

### GUID System
Unity uses 32-character hexadecimal GUIDs to track assets. Never manually create GUIDs—always copy from `.meta` files. Keep meta files in version control.
→ See `reference/guid-system.md` for details
→ Use `scripts/guid_validator.py` to validate GUIDs

### Input Systems
Unity has legacy and new Input Systems. Mixing them causes errors. Configure `activeInputHandler` correctly before writing input code.
→ See `reference/input-systems.md` for details
→ Use `scripts/project_health_check.py` to verify configuration

### Physics
Understand when to use triggers vs collisions. Use triggers for fast-moving projectiles to avoid tunneling.
→ See `reference/physics-system.md` for details

### URP
Universal Render Pipeline requires additional camera setup. Always create cameras via Unity Editor when using URP.
→ See `reference/urp-setup.md` for details
→ Use `scripts/project_health_check.py` to verify URP setup

## Quick Reference

### Most Common Errors

| Error Pattern | Quick Fix | Details |
|--------------|-----------|---------|
| GUID extraction failed | Copy correct GUID from `.meta` file | `guid-system.md` |
| Input System exception | Set `activeInputHandler: 2` | `input-systems.md` |
| Fast bullets miss targets | Use triggers instead of collisions | `physics-system.md` |
| Camera data is null (URP) | Set `m_RendererIndex: 0` | `urp-setup.md` |
| NullReferenceException | Assign SerializeField in Inspector | `common-errors.md` |

### Unity API Changes by Version

**Unity 2023.1+**
- `Rigidbody.velocity` → `Rigidbody.linearVelocity`

**Unity 2019.1+**
- New Input System package available
- Can use legacy, new, or both systems

→ See reference files for complete migration guides

## Keywords

Unity, Unity3D, GUID, meta files, Input System, Rigidbody, physics, triggers, collisions, URP, Universal Render Pipeline, prefabs, scenes, API migration, version control, build errors, runtime errors, NullReferenceException, InvalidOperationException

## Additional Resources

### Unity Documentation
- [Input System Manual](https://docs.unity3d.com/Packages/com.unity.inputsystem@latest)
- [URP Documentation](https://docs.unity3d.com/Packages/com.unity.render-pipelines.universal@latest)
- [Physics Best Practices](https://docs.unity3d.com/Manual/BestPracticeUnderstandingPerformanceInUnity6.html)

### Lessons Learned From

This skill is based on real-world lessons from:
- **2D Unity Projects** (Unity 2022.3+ with URP)
  - Scene bootstrapping and prefab setup
  - Input system compatibility
  - Resources folder patterns
  - Component references

- **3D Unity Projects** (Unity 2023.1+)
  - VR development
  - Physics-based gameplay
  - Model imports and orientation
  - Fast-moving projectile detection

---

*Based on Unity 2022.3+ (URP) and Unity 2023.1+ projects.*
*Always verify API compatibility with your Unity version.*
