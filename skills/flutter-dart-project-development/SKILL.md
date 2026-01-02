---
name: flutter-dart-project-development
description: Guides development of Flutter applications using Provider-based state management with best practices for architecture, testing, and modern Flutter patterns. Use this skill when working on Flutter/Dart projects that need state management guidance, code scaffolding, refactoring assistance, or architectural recommendations.
license: Complete terms in LICENSE.txt
---

# Flutter/Dart Project Development with Provider

## Overview

This skill provides comprehensive guidance for Flutter project development with a focus on Provider-based state management, architectural best practices, and modern Flutter patterns. It helps you implement clean, maintainable, and performant Flutter applications with consistent state management approaches.

**Keywords**: Flutter, Dart, Provider, ChangeNotifier, state management, widget testing, clean architecture, performance optimization, mobile development

## Core Principles

### Provider-First State Management

Always use Provider pattern for app-wide and feature-level state management:
- **Use ChangeNotifier with ChangeNotifierProvider** for state management
- Never mix state management styles - maintain consistency throughout the project
- Keep Providers focused on specific domains (User, Settings, Cart, etc.)

### State Management Guidelines

**When to Use Provider:**
- App-wide state (user authentication, theme, settings)
- Feature-level state shared across multiple widgets
- Data that needs to persist across navigation
- State that requires notification to multiple listeners

**When NOT to Use Provider:**
- Ephemeral state like `TextEditingController`
- Simple animations and transitions
- Local widget state (form inputs, switches, etc.)
- **For ephemeral state, use StatefulWidget instead**

### Context Usage Patterns

Follow these architectural guardrails for accessing Providers:

**For Actions (Callbacks):**
```dart
context.read<T>()
```
Use `read` when you need to trigger actions without causing rebuilds (e.g., in onPressed callbacks).

**For UI Updates:**
```dart
context.watch<T>()  // Simple watching
Consumer<T>         // When you need child optimization
Selector<T, R>      // For selective rebuilds based on specific properties
```

## High-Velocity Scaffolding

Use these targeted prompts with GitHub Copilot Chat (@workspace) to generate boilerplate instantly:

### Creating Provider Models

**Basic Provider:**
```
Create a UserProvider class extending ChangeNotifier with a private _user object, 
a getter, and a updateProfile method that calls notifyListeners()
```

**Provider with Multiple Properties:**
```
Create a SettingsProvider with theme mode, language preference, and notification 
settings. Include methods to update each property and persist to SharedPreferences
```

### Multi-Provider Setup

**Application Bootstrap:**
```
Generate a MultiProvider wrapper for main.dart including UserProvider, 
SettingsProvider, and CartProvider
```

Example structure:
```dart
MultiProvider(
  providers: [
    ChangeNotifierProvider(create: (_) => UserProvider()),
    ChangeNotifierProvider(create: (_) => SettingsProvider()),
    ChangeNotifierProvider(create: (_) => CartProvider()),
  ],
  child: MyApp(),
)
```

### Selective Rebuilds

**Performance Optimization:**
```
Convert this widget to use Selector instead of Consumer to only rebuild when 
the isLoggedIn property of AuthProvider changes
```

Example pattern:
```dart
Selector<AuthProvider, bool>(
  selector: (context, auth) => auth.isLoggedIn,
  builder: (context, isLoggedIn, child) {
    // Widget only rebuilds when isLoggedIn changes
  },
)
```

## Agentic Refactoring with Provider

### Multi-File State Migrations

Use GitHub Copilot Agent for complex refactoring tasks:

**Refactoring to Provider:**
```
Refactor the current ProfileScreen and its children to pull data from a new 
ProfileProvider instead of passing parameters through constructors
```

**Performance Analysis:**
```
Analyze my Build methods and suggest where to use context.select to improve 
performance by reducing unnecessary rebuilds
```

### Common Refactoring Patterns

1. **Constructor Parameters → Provider:**
   - Identify widgets receiving data through constructors
   - Create appropriate Provider class
   - Update widgets to use `context.watch` or `Consumer`
   - Remove constructor parameters

2. **Callback Props → Provider Actions:**
   - Move callbacks from props to Provider methods
   - Use `context.read` for triggering actions
   - Simplify widget trees by removing callback chains

3. **setState → ChangeNotifier:**
   - Convert StatefulWidget to StatelessWidget where appropriate
   - Move state to ChangeNotifier Provider
   - Replace setState calls with notifyListeners

## Integration with Modern Flutter Patterns

### Clean Architecture

Organize your Flutter project with clear separation of concerns:

**Directory Structure:**
```
lib/
├── domain/              # Business logic (pure Dart)
│   ├── models/
│   ├── repositories/
│   └── use_cases/
├── presentation/        # UI layer
│   ├── providers/       # State management
│   ├── screens/
│   └── widgets/
└── data/               # Data sources
    ├── api/
    ├── local/
    └── repositories/
```

**Key Principles:**
- Keep Providers in `presentation/providers/` directory
- Separate pure business logic in `domain/` layer
- Providers should orchestrate use cases, not contain business logic
- Use dependency injection for repositories in Providers

### Widget Testing with Mocked Providers

**Test Setup Pattern:**
```
Generate a widget test for LoginScreen that mocks AuthProvider using the 
mocktail package
```

Example test structure:
```dart
testWidgets('LoginScreen shows error on failed login', (tester) async {
  final mockAuthProvider = MockAuthProvider();
  
  when(() => mockAuthProvider.login(any(), any()))
      .thenAnswer((_) async => false);
  
  await tester.pumpWidget(
    ChangeNotifierProvider<AuthProvider>.value(
      value: mockAuthProvider,
      child: MaterialApp(home: LoginScreen()),
    ),
  );
  
  // Test assertions
});
```

### Performance Optimization Strategies

**1. Use Selector for Precise Rebuilds:**
```dart
Selector<CartProvider, int>(
  selector: (context, cart) => cart.itemCount,
  builder: (context, count, child) => Text('$count items'),
)
```

**2. Use context.select for Single Values:**
```dart
final username = context.select<UserProvider, String>(
  (user) => user.name,
);
```

**3. Provide child to Consumer:**
```dart
Consumer<ThemeProvider>(
  child: ExpensiveWidget(), // Won't rebuild
  builder: (context, theme, child) {
    return ThemedContainer(
      theme: theme,
      child: child,
    );
  },
)
```

## Configuration Files

### Copilot Instructions (.github/copilot-instructions.md)

Create this file to enforce Provider-first mindset:

```markdown
# Flutter Project - State Management Guidelines

## State Management Rules

1. **Always use ChangeNotifier with ChangeNotifierProvider** for state management
2. **Use context.read<T>()** for actions (callbacks)
3. **Use context.watch<T>() or Consumer<T>** for UI updates
4. **Do not use Providers for ephemeral state** like TextEditingController or simple animations
5. **Use StatefulWidget for ephemeral state** management

## Architecture Guidelines

- Place Providers in `presentation/providers/` directory
- Keep business logic in `domain/` layer, separate from Providers
- Use dependency injection for repositories
- Follow clean architecture principles

## Testing Standards

- Mock Providers using mocktail package
- Test Provider logic separately from UI
- Use widget tests with mocked Providers for screens
```

## Best Practices Summary

1. **Consistency:** Use Provider pattern throughout the project
2. **Separation:** Keep Provider state management separate from ephemeral state
3. **Performance:** Use Selector and context.select for optimized rebuilds
4. **Architecture:** Follow clean architecture with clear layer separation
5. **Testing:** Mock Providers for reliable widget and integration tests
6. **Documentation:** Maintain clear Provider responsibilities and contracts

## Common Pitfalls to Avoid

- ❌ Mixing Provider with other state management solutions
- ❌ Using Provider for ephemeral/local state
- ❌ Using context.watch in callbacks (causes unnecessary rebuilds)
- ❌ Creating overly broad Providers (prefer focused, single-responsibility Providers)
- ❌ Putting business logic directly in Providers (use use cases/repositories)
- ❌ Forgetting to dispose resources in Provider's dispose method
- ❌ Not using Selector/context.select for performance-critical widgets

## Additional Resources

- Provider package: https://pub.dev/packages/provider
- Flutter architecture samples: https://github.com/brianegan/flutter_architecture_samples
- Clean architecture guide: Focus on separation between domain, data, and presentation layers
