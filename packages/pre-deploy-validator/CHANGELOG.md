# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.0.0] - 2024-01-15

### Added
- Initial release of Pre-Deployment Validator
- Five check types: lint, typescript, tests, security-audit, build
- JSON-based configuration system
- Parallel and sequential execution modes
- Console and JSON reporting formats
- CLI interface with `pre-deploy-validator` command
- Branch-aware skipping for production/main branches
- Monorepo support with multi-project builds
- Coverage threshold validation for tests
- Comprehensive test suite with 85%+ coverage
- TypeScript strict mode support
- CommonJS and ESM exports

### Features
- Lint check with customizable command
- TypeScript type checking with tsc
- Test runner with coverage thresholds
- npm audit security scanning
- Multi-project build validation
- Timeout configuration per check
- Fail-block and fail-warn severity levels
- Rich terminal output with colors and symbols
- Machine-readable JSON output
- CLI options for config, format, and skip

### Documentation
- Comprehensive README with examples
- Configuration schema documentation
- API usage guide
- CI/CD integration examples
- GitHub Actions workflow template
- Four configuration examples (minimal, advanced, monorepo, custom)

### Testing
- Unit tests for all check types
- Reporter formatting tests
- CLI option parsing tests
- Error handling tests
- Integration test fixtures
- 85%+ code coverage

---

## Planned Releases

### [1.1.0] - Planned
- [ ] GitHub Action marketplace release
- [ ] Docker support for CI/CD
- [ ] Custom check plugins
- [ ] Test result caching
- [ ] Performance benchmarking

### [2.0.0] - Planned
- [ ] YAML config support
- [ ] Database migration validation
- [ ] Performance profiling checks
- [ ] Accessibility validation
