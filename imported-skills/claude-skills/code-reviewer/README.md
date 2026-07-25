# code-reviewer

Code review automation for TypeScript, JavaScript, Python, Go, Swift, Kotlin, C#, .NET, Java, C, C++, Rust, Ruby, PHP, and Dart/Flutter. Analyzes PRs for complexity and risk, checks code quality for SOLID violations and code smells, and generates review reports.

The full skill spec is [`SKILL.md`](./SKILL.md). This README is a quick reference for the 3 bundled scripts.

---

## How to use

### Quick install check

```bash
python scripts/pr_analyzer.py --help
python scripts/code_quality_checker.py --help
python scripts/review_report_generator.py --help
```

All three scripts are stdlib-only — no `pip install` required.

### Example 1 — review a pull request

```bash
# From inside the repo you want to analyze:
python /path/to/skills/code-reviewer/scripts/pr_analyzer.py . --base main --head HEAD
```

Outputs: complexity score (1-10), risk categorization (critical / high / medium / low), prioritized review order, commit-message validation.

### Example 2 — score a directory's code quality

```bash
python scripts/code_quality_checker.py /path/to/code

# Filter by language
python scripts/code_quality_checker.py /path/to/code --language csharp

# Machine-readable
python scripts/code_quality_checker.py /path/to/code --json
```

Outputs: quality score (0-100), letter grade, detected code smells, SOLID violations.

### Example 3 — combine into a review report

```bash
python scripts/review_report_generator.py /path/to/repo --format markdown --output review.md
```

Outputs: review verdict (approve / request changes / block), score, prioritized action items.

---

## Examples bundled with the skill

| File | Purpose |
|------|---------|
| [`assets/sample_csharp_smells.cs`](./assets/sample_csharp_smells.cs) | C# file with every C#-specific pattern this skill detects, labelled inline |
| [`assets/sample_csharp_clean.cs`](./assets/sample_csharp_clean.cs) | Same code refactored per `rules/universal.md` + `languages/csharp.md` |
| [`assets/sample_java_smells.java`](./assets/sample_java_smells.java) | Java file with every Java-specific pattern this skill detects, labelled inline |
| [`assets/sample_java_clean.java`](./assets/sample_java_clean.java) | Same code refactored per `rules/universal.md` + `languages/java.md` |
| [`assets/sample_c_smells.c`](./assets/sample_c_smells.c) | C file with every C-specific pattern this skill detects, labelled inline |
| [`assets/sample_c_clean.c`](./assets/sample_c_clean.c) | Same code refactored per `rules/universal.md` + `languages/c.md` |
| [`expected_outputs/*.json`](./expected_outputs/) | Expected `code_quality_checker.py --json` output for each fixture |

Use them as a regression-detection harness:

```bash
python scripts/code_quality_checker.py assets/sample_java_smells.java --json > /tmp/check.json
diff /tmp/check.json expected_outputs/sample_java_smells_quality.json
# silence means the detector still behaves as documented
```

---

## What it detects

See [`SKILL.md`](./SKILL.md) for the full pattern list, severity tiers, and references. Quick summary:

- **PR Analyzer** (`scripts/pr_analyzer.py`): hardcoded secrets / connection strings, SQL injection, debug statements (`console.*` / `System.out` / `printStackTrace`), analyzer suppressions (ESLint / Roslyn / `@SuppressWarnings`), `any` / `dynamic` overuse, TODO/FIXME, `unsafe` blocks, null-forgiving `!`, `async void`, blocking on `Task`.
- **Code Quality Checker** (`scripts/code_quality_checker.py`): long methods, large files, god classes, deep nesting, too many parameters, high cyclomatic complexity, swallowed exceptions, missing `await`, undisposed `IDisposable`, `new HttpClient()` in method body, unused `using` directives. Language-specific smell packs for C# (`async void`, blocking on `Task`), Java (empty catch, `printStackTrace`, swallowed `InterruptedException`, unclosed resources, per-call `ObjectMapper` / `Gson`), and C (banned functions `gets`/`strcpy`/`strcat`/`sprintf`/`vsprintf`, format-string vulnerability `printf(var)`, unbounded `scanf("%s")`, malloc-without-NULL-check, free-without-zeroing, `system()` with non-literal argument).
- **Review Report Generator** (`scripts/review_report_generator.py`): combines the above into a single markdown or JSON verdict.

---

## Review rules

Rules are split so every review loads exactly two files — the cross-language
baseline plus one language guide (see the dispatch table in [`SKILL.md`](./SKILL.md)):

- [`rules/universal.md`](./rules/universal.md) — cross-language rules: security, async/concurrency, resource management, exception handling, performance
- [`languages/`](./languages/) — one self-contained guide per language (`python`, `typescript`, `go`, `swift`, `kotlin`, `csharp`, `java`, `c`, `cpp`, `rust`, `ruby`, `php`, `dart`), each with Security / Async / Resource Management / Exception Handling / Performance / Idioms sections
