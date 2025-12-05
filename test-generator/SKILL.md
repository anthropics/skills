---
name: test-generator
description: Use this skill to generate comprehensive test suites including unit tests, integration tests, and edge cases for functions, classes, APIs, and components with appropriate test framework setup
license: Apache-2.0
---

# Test Generator

Generate comprehensive, well-structured test suites that ensure code quality and reliability through thorough testing coverage.

## When to Use

Use this skill when:
- The user asks to "generate tests" or "create test suite"
- The user wants to "add test coverage" for code
- The user needs to test a specific function, class, or module
- The user is implementing TDD and needs test scaffolding
- Code exists but lacks adequate tests

## Test Generation Process

### Step 1: Analyze the Code

**Understand what needs testing:**

1. **Read the source code** to understand:
   - What does the code do?
   - What are the inputs and outputs?
   - What are the dependencies?
   - What are the edge cases?
   - What are the error conditions?

2. **Identify the code type:**
   - Functions/methods
   - Classes
   - API endpoints
   - React/Vue components
   - Database operations
   - Async operations

3. **Determine testing approach:**
   - Unit tests (isolated functionality)
   - Integration tests (component interactions)
   - End-to-end tests (full workflows)

### Step 2: Choose Test Framework

Select the appropriate framework for the language:

**JavaScript/TypeScript:**
- Jest (most common)
- Vitest (modern, fast)
- Mocha + Chai
- Testing Library (for React/Vue components)
- Cypress/Playwright (E2E)

**Python:**
- pytest (recommended)
- unittest (built-in)
- doctest (for simple cases)

**Go:**
- testing (built-in)
- testify (assertions)

**Java:**
- JUnit 5
- Mockito (mocking)
- AssertJ (assertions)

**Rust:**
- Built-in test framework
- cargo test

Ask the user about their framework preference if unclear.

### Step 3: Generate Test Structure

Create a well-organized test file:

```javascript
// For: src/utils/calculator.js
// Create: src/utils/calculator.test.js

import { describe, it, expect } from 'jest';
import { calculator } from './calculator';

describe('calculator', () => {
  describe('add', () => {
    // Happy path tests
    it('should add two positive numbers', () => {
      expect(calculator.add(2, 3)).toBe(5);
    });

    // Edge cases
    it('should handle zero', () => {
      expect(calculator.add(0, 5)).toBe(5);
      expect(calculator.add(5, 0)).toBe(5);
    });

    it('should handle negative numbers', () => {
      expect(calculator.add(-2, 3)).toBe(1);
      expect(calculator.add(-2, -3)).toBe(-5);
    });

    it('should handle decimals', () => {
      expect(calculator.add(0.1, 0.2)).toBeCloseTo(0.3);
    });

    // Error cases
    it('should throw error for non-numeric input', () => {
      expect(() => calculator.add('a', 2)).toThrow('Invalid input');
    });
  });
});
```

### Step 4: Cover Test Scenarios

Generate tests for all scenarios:

#### 4.1 Happy Path (Expected Usage)

Test the normal, expected use cases:
- Valid inputs producing expected outputs
- Standard workflows
- Common use patterns

```python
def test_user_creation_with_valid_data():
    """Test creating a user with all valid fields."""
    user = create_user(
        email="user@example.com",
        name="John Doe",
        age=30
    )

    assert user.email == "user@example.com"
    assert user.name == "John Doe"
    assert user.age == 30
    assert user.id is not None
```

#### 4.2 Edge Cases

Test boundary conditions and special cases:
- Empty inputs
- Zero values
- Very large values
- Minimum/maximum boundaries
- Special characters
- Unicode/international input

```python
def test_empty_string():
    """Test handling of empty string input."""
    result = process_text("")
    assert result == ""

def test_max_length_string():
    """Test handling of maximum length string."""
    long_text = "a" * 10000
    result = process_text(long_text)
    assert len(result) <= 10000

def test_unicode_characters():
    """Test handling of unicode characters."""
    text = "Hello 世界 🌍"
    result = process_text(text)
    assert "世界" in result
```

#### 4.3 Error Conditions

Test how errors are handled:
- Invalid inputs
- Missing required parameters
- Type mismatches
- Resource not found
- Permission denied

```python
def test_invalid_email_format():
    """Test that invalid email format raises ValueError."""
    with pytest.raises(ValueError, match="Invalid email format"):
        create_user(email="invalid-email", name="John")

def test_missing_required_field():
    """Test that missing required field raises error."""
    with pytest.raises(TypeError):
        create_user(name="John")  # Missing email
```

#### 4.4 State and Side Effects

Test stateful behavior and side effects:
- Database changes
- File system operations
- External API calls
- State mutations

```python
def test_user_is_saved_to_database(db_session):
    """Test that user is persisted to database."""
    user = create_user(email="test@example.com", name="Test")

    # Verify in database
    saved_user = db_session.query(User).filter_by(email="test@example.com").first()
    assert saved_user is not None
    assert saved_user.name == "Test"
```

#### 4.5 Async Operations

Test asynchronous code properly:

```javascript
describe('fetchUserData', () => {
  it('should fetch user data successfully', async () => {
    const userId = '123';
    const userData = await fetchUserData(userId);

    expect(userData).toHaveProperty('id', userId);
    expect(userData).toHaveProperty('name');
  });

  it('should handle fetch errors', async () => {
    await expect(fetchUserData('invalid')).rejects.toThrow('User not found');
  });
});
```

### Step 5: Add Mocking and Fixtures

Use mocks and fixtures for dependencies:

**Mocking external dependencies:**

```javascript
import { jest } from '@jest/globals';
import { sendEmail } from './emailService';

// Mock the email service
jest.mock('./emailService');

describe('User registration', () => {
  it('should send welcome email on successful registration', async () => {
    sendEmail.mockResolvedValue({ success: true });

    await registerUser({ email: 'test@example.com' });

    expect(sendEmail).toHaveBeenCalledWith({
      to: 'test@example.com',
      subject: 'Welcome!',
      body: expect.any(String)
    });
  });
});
```

**Using fixtures:**

```python
import pytest

@pytest.fixture
def sample_user():
    """Provide a sample user for tests."""
    return {
        'email': 'test@example.com',
        'name': 'Test User',
        'age': 25
    }

def test_user_validation(sample_user):
    """Test user validation with fixture."""
    result = validate_user(sample_user)
    assert result.is_valid
```

### Step 6: Test Organization

Organize tests logically:

```python
# test_user_service.py

class TestUserCreation:
    """Tests for user creation functionality."""

    def test_create_user_with_valid_data(self):
        """Test creating user with valid data."""
        pass

    def test_create_user_with_invalid_email(self):
        """Test error handling for invalid email."""
        pass

class TestUserRetrieval:
    """Tests for user retrieval functionality."""

    def test_get_user_by_id(self):
        """Test retrieving user by ID."""
        pass

    def test_get_user_not_found(self):
        """Test handling when user doesn't exist."""
        pass

class TestUserUpdate:
    """Tests for user update functionality."""

    def test_update_user_email(self):
        """Test updating user email."""
        pass
```

### Step 7: Add Test Documentation

Document tests clearly:

```python
def test_password_hashing():
    """
    Test that passwords are properly hashed.

    This test verifies that:
    1. Plain text passwords are not stored
    2. Hashed passwords are different from original
    3. Hash is verifiable using check_password
    4. Same password hashed twice produces different hashes (due to salt)
    """
    password = "secure_password_123"
    hashed = hash_password(password)

    assert hashed != password
    assert check_password(password, hashed)
    assert hash_password(password) != hashed  # Different salt
```

## Framework-Specific Patterns

### Jest/Vitest (JavaScript/TypeScript)

```javascript
import { describe, it, expect, beforeEach, afterEach } from 'vitest';

describe('MyComponent', () => {
  let instance;

  beforeEach(() => {
    instance = new MyComponent();
  });

  afterEach(() => {
    instance.cleanup();
  });

  it('should initialize with default state', () => {
    expect(instance.state).toEqual({});
  });
});
```

### pytest (Python)

```python
import pytest

class TestCalculator:
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup before each test."""
        self.calc = Calculator()
        yield
        # Teardown after each test
        self.calc = None

    def test_addition(self):
        assert self.calc.add(2, 3) == 5

    @pytest.mark.parametrize("a,b,expected", [
        (2, 3, 5),
        (0, 0, 0),
        (-1, 1, 0),
        (100, 200, 300),
    ])
    def test_addition_multiple_cases(self, a, b, expected):
        assert self.calc.add(a, b) == expected
```

### Go testing

```go
package calculator

import "testing"

func TestAdd(t *testing.T) {
    tests := []struct {
        name     string
        a, b     int
        expected int
    }{
        {"positive numbers", 2, 3, 5},
        {"with zero", 0, 5, 5},
        {"negative numbers", -2, -3, -5},
    }

    for _, tt := range tests {
        t.Run(tt.name, func(t *testing.T) {
            result := Add(tt.a, tt.b)
            if result != tt.expected {
                t.Errorf("Add(%d, %d) = %d; want %d", tt.a, tt.b, result, tt.expected)
            }
        })
    }
}
```

### JUnit (Java)

```java
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import static org.junit.jupiter.api.Assertions.*;

@DisplayName("Calculator Tests")
class CalculatorTest {

    private Calculator calculator;

    @BeforeEach
    void setUp() {
        calculator = new Calculator();
    }

    @Test
    @DisplayName("Should add two positive numbers")
    void testAddPositiveNumbers() {
        assertEquals(5, calculator.add(2, 3));
    }

    @Test
    @DisplayName("Should throw exception for invalid input")
    void testInvalidInput() {
        assertThrows(IllegalArgumentException.class, () -> {
            calculator.divide(10, 0);
        });
    }
}
```

## Component Testing

### React Components (with Testing Library)

```javascript
import { render, screen, fireEvent, waitFor } from '@testing-library/react';
import { UserProfile } from './UserProfile';

describe('UserProfile', () => {
  it('should render user information', () => {
    const user = { name: 'John Doe', email: 'john@example.com' };

    render(<UserProfile user={user} />);

    expect(screen.getByText('John Doe')).toBeInTheDocument();
    expect(screen.getByText('john@example.com')).toBeInTheDocument();
  });

  it('should call onEdit when edit button is clicked', () => {
    const onEdit = jest.fn();
    const user = { name: 'John Doe', email: 'john@example.com' };

    render(<UserProfile user={user} onEdit={onEdit} />);

    fireEvent.click(screen.getByRole('button', { name: /edit/i }));

    expect(onEdit).toHaveBeenCalledWith(user);
  });

  it('should display loading state', async () => {
    render(<UserProfile userId="123" />);

    expect(screen.getByText(/loading/i)).toBeInTheDocument();

    await waitFor(() => {
      expect(screen.getByText('John Doe')).toBeInTheDocument();
    });
  });
});
```

## API Testing

```javascript
import request from 'supertest';
import app from './app';

describe('POST /api/users', () => {
  it('should create a new user', async () => {
    const userData = {
      email: 'test@example.com',
      name: 'Test User'
    };

    const response = await request(app)
      .post('/api/users')
      .send(userData)
      .expect(201);

    expect(response.body).toMatchObject({
      id: expect.any(String),
      email: userData.email,
      name: userData.name
    });
  });

  it('should return 400 for invalid email', async () => {
    const response = await request(app)
      .post('/api/users')
      .send({ email: 'invalid', name: 'Test' })
      .expect(400);

    expect(response.body).toHaveProperty('error');
  });
});
```

## Test Quality Guidelines

**Write tests that are:**

1. **Clear**: Test names describe what's being tested
2. **Independent**: Each test runs in isolation
3. **Repeatable**: Same results every time
4. **Fast**: Quick to run
5. **Thorough**: Cover edge cases and errors
6. **Maintainable**: Easy to update when code changes

**Avoid:**

- Tests that depend on external services (use mocks)
- Tests that depend on other tests' side effects
- Tests with hard-coded dates/times (use fixtures)
- Overly complex test logic
- Testing implementation details instead of behavior

## Coverage Goals

Aim for:
- **Unit tests**: 80-90% code coverage
- **Integration tests**: Critical paths and workflows
- **E2E tests**: Key user journeys

Don't aim for 100% coverage - focus on valuable tests.

## Test Output Structure

Generate tests in a file that:
1. Imports necessary dependencies
2. Sets up test fixtures and mocks
3. Organizes tests by functionality
4. Includes clear test names
5. Has helpful comments
6. Follows project conventions

## Error Handling

- If code language is unclear, ask the user
- If testing framework is not specified, suggest the most common one
- If dependencies are unclear, ask about mocking strategy
- If scope is too large, suggest breaking into multiple test files

## Example Interactions

### Example 1: Generate Unit Tests

User: "Generate tests for utils/stringHelper.js"

Response:
1. Read utils/stringHelper.js
2. Analyze functions and their behavior
3. Identify edge cases
4. Generate comprehensive test file
5. Include mocks for dependencies
6. Write to utils/stringHelper.test.js

### Example 2: Test React Component

User: "Create tests for my Button component"

Response:
1. Read the Button component
2. Identify props and interactions
3. Set up Testing Library
4. Generate tests for:
   - Rendering with different props
   - Click handlers
   - Disabled state
   - Styling variants
5. Write component.test.tsx

### Example 3: API Endpoint Tests

User: "Test the POST /api/products endpoint"

Response:
1. Analyze the endpoint implementation
2. Identify request/response format
3. Generate tests for:
   - Successful creation
   - Validation errors
   - Authentication
   - Edge cases
4. Use supertest or similar
5. Mock database operations
