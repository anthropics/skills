---
name: ml-unit
description: "Run and check the output of MarkLogic Unit tests"
---

# Running mlUnit

## Overview
Runs as a gradle task from the marklogic directory of a project using the ml-gradle plugin.
Supports gradle task modifiers such as --info 

## Directories
marklogic - `.gradlew` is in this directory from the project root
marklogic/src/test - root directory
marklogic/src/test/ml-modules/root/test - suites contained here
marklogic/build/test-results/marklogic-unit-test - unit test results as XML

## Local Configuration
**gradle-local.properties** contains critical settings for running tests locally:
- `mlHost` - MarkLogic server host (typically `localhost`)
- `mlTestRestPort` - Port for test REST API (e.g., `9324`)
- `mlUsername` / `mlPassword` - Admin credentials
- `mlModulePaths` - Must include both `src/main/ml-modules,src/test/ml-modules`
- `isDeployUnitTestFramework=true` - Required to deploy test framework

This file is typically git-ignored and must be created for local development.

## Execution
**Ensure correct JAVA version:** `export JAVA_HOME=$(/usr/libexec/java_home -v 17)`
**Run all tests locally:** `./gradlew mlUnitTest -PenvironmentName=local`
**Run a specific test suite:** `./gradlew mlUnitTest -Psuite=service_session_cache -PenvironmentName=local`
**Run specific tests in a suite:** `./gradlew mlUnitTest -Psuite=service_session_cache -Ptests=count-all.xqy -PenvironmentName=local`
**Load modules after fixing based on test results:** `./gradlew -PenvironmentName=local mlLoadModules -i`
**Watch for changes and auto-reload:** `./gradlew mlWatch -i`

Note: Use `-Psuite=` (not `-Psuites=` or `-Ptest-suites=`) for single suite execution.

## Writing Tests (XQuery)
**Import test helper:**
```xquery
import module namespace test="http://marklogic.com/test"
  at "/test/test-helper.xqy";
```
**Common assertions:**
- `test:assert-equal($expected, $actual)` - Compare values
- `test:assert-true($condition)` - Verify boolean condition
- `test:assert-throws-error($function, $params)` - Verify error thrown
- Add assertion message as final argument for clarity

## Debugging and Analysis
**Using xdmp:log() for debugging:**
```xquery
let $value := some-lib:something()
let $_ := xdmp:log(("Debug value:", $value))
```
**Log files:** Messages appear in `PORT_ErrorLog.txt` (where PORT is the app server port)
**Test results:** JUnit XML files at `build/test-results/marklogic-unit-test/` contain failure messages and stacktraces
**HTTP header case sensitivity:** MarkLogic is case-sensitive for HTTP headers (e.g., "Cookie" vs "cookie")
**Test isolation:** Each test file runs as a separate HTTP request with its own context
**HTTP sessions:** Tests making HTTP requests (via `xdmp:http-get()`) create new sessions; session data must be explicitly shared between requests

## Test Data Management
**Suite lifecycle:**
- `suite-setup.xqy` runs once before all tests in the suite
- `setup.xqy` runs before each individual test (if present)
- Individual test files run independently
- `teardown.xqy` runs after each test (if present)
- `suite-teardown.xqy` runs once after all tests complete

**Teardown control options:**
- Skip suite teardown: `-Prs:runsuiteteardown=false`
- Skip test teardown: `-Prs:runteardown=false`

**Best practice:** Consider deleting test data in setup rather than teardown to maintain data for manual verification and debugging

## Dependencies
In build.gradle:
- classpath "com.marklogic:ml-gradle:6.0.0"
- classpath "com.marklogic:marklogic-unit-test-client:1.4.0"
