# Testing Framework Guide

Language and framework selection, configuration, and patterns.

---

## Table of Contents

- [Framework Selection](#framework-selection)
- [TypeScript/JavaScript](#typescriptjavascript)
- [Python](#python)
- [Java](#java)
- [Version Requirements](#version-requirements)

---

## Framework Selection

| Language | Recommended | Alternatives | Best For |
|----------|-------------|--------------|----------|
| TypeScript/JS | Jest | Vitest, Mocha | React, Node.js, Next.js |
| Python | Pytest | unittest, nose2 | Django, Flask, FastAPI |
| Java | JUnit 5 | TestNG | Spring, Android |
| Vite projects | Vitest | Jest | Modern Vite-based apps |

---

## TypeScript/JavaScript

### Jest Configuration

```javascript
// jest.config.js
module.exports = {
  preset: 'ts-jest',
  testEnvironment: 'node',
  testMatch: ['**/*.test.ts'],
  collectCoverageFrom: ['src/**/*.ts'],
  coverageThreshold: {
    global: { branches: 80, lines: 80 }
  }
};
```

### Jest Test Pattern

```typescript
describe('Calculator', () => {
  let calc: Calculator;

  beforeEach(() => {
    calc = new Calculator();
  });

  it('should add two numbers', () => {
    expect(calc.add(2, 3)).toBe(5);
  });

  it('should throw on invalid input', () => {
    expect(() => calc.add(null, 3)).toThrow('Invalid input');
  });
});
```

### Vitest Configuration

```typescript
// vitest.config.ts
import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    globals: true,
    environment: 'node',
    coverage: { provider: 'c8' }
  }
});
```

### Coverage Tools
- Istanbul/nyc: Traditional coverage
- c8: Native V8 coverage (faster)
- Vitest built-in: Integrated with test runner

---

## Python

### Pytest Configuration

```ini
# pytest.ini
[pytest]
testpaths = tests
python_files = test_*.py
python_functions = test_*
addopts = --cov=src --cov-report=term-missing
```

### Pytest Test Pattern

```python
import pytest
from calculator import Calculator

class TestCalculator:
    @pytest.fixture
    def calc(self):
        return Calculator()

    def test_add_positive_numbers(self, calc):
        assert calc.add(2, 3) == 5

    def test_add_raises_on_invalid_input(self, calc):
        with pytest.raises(ValueError, match="Invalid input"):
            calc.add(None, 3)

    @pytest.mark.parametrize("a,b,expected", [
        (1, 2, 3),
        (-1, 1, 0),
        (0, 0, 0),
    ])
    def test_add_various_inputs(self, calc, a, b, expected):
        assert calc.add(a, b) == expected
```

### Coverage Tools
- coverage.py: Standard Python coverage
- pytest-cov: Pytest plugin wrapper
- Report formats: HTML, XML, LCOV

---

## Java

### JUnit 5 Configuration (Maven)

```xml
<!-- pom.xml -->
<dependency>
    <groupId>org.junit.jupiter</groupId>
    <artifactId>junit-jupiter</artifactId>
    <version>5.9.3</version>
    <scope>test</scope>
</dependency>
<plugin>
    <groupId>org.jacoco</groupId>
    <artifactId>jacoco-maven-plugin</artifactId>
    <version>0.8.10</version>
</plugin>
```

### JUnit 5 Test Pattern

```java
import org.junit.jupiter.api.*;
import static org.junit.jupiter.api.Assertions.*;

class CalculatorTest {
    private Calculator calc;

    @BeforeEach
    void setUp() {
        calc = new Calculator();
    }

    @Test
    @DisplayName("should add two positive numbers")
    void testAddPositive() {
        assertEquals(5, calc.add(2, 3));
    }

    @Test
    @DisplayName("should throw on null input")
    void testAddThrowsOnNull() {
        assertThrows(IllegalArgumentException.class,
            () -> calc.add(null, 3));
    }

    @ParameterizedTest
    @CsvSource({"1,2,3", "-1,1,0", "0,0,0"})
    void testAddVarious(int a, int b, int expected) {
        assertEquals(expected, calc.add(a, b));
    }
}
```

### Coverage Tools
- JaCoCo: Standard Java coverage
- Cobertura: Alternative XML format
- Report formats: HTML, XML, CSV

---

## Version Requirements

| Tool | Minimum Version | Notes |
|------|-----------------|-------|
| Node.js | 16+ | Required for Jest 29+ |
| Jest | 29+ | Modern async support |
| Vitest | 0.34+ | Stable API |
| Python | 3.8+ | f-strings, async support |
| Pytest | 7+ | Modern fixtures |
| Java | 11+ | JUnit 5 support |
| JUnit | 5.9+ | ParameterizedTest improvements |
| TypeScript | 4.5+ | Strict mode features |
