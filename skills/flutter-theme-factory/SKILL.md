---
name: flutter-theme-factory
description: Toolkit for styling Flutter apps with a theme. Apply pre-built or custom ThemeData configurations to any Flutter app — including full ColorScheme, TextTheme, component themes, and dark/light mode support. 12 pre-set themes available, or generate a custom theme on-the-fly.
license: MIT
---

# Flutter Theme Factory Skill

This skill provides a curated collection of professional Flutter `ThemeData` configurations, each with carefully selected color palettes, Google Fonts pairings, and component-level theming. Once a theme is chosen, it generates production-ready Dart code.

## Purpose

To apply consistent, professional styling to any Flutter application. Each theme includes:
- A cohesive `ColorScheme` with light and dark variants
- Complementary Google Fonts pairings for display, headline, title, body, and label text
- Component-level theming (`AppBarTheme`, `CardTheme`, `ElevatedButtonTheme`, `InputDecorationTheme`, etc.)
- A distinct visual identity suitable for different contexts and audiences

## Usage Instructions

1. **Show available themes**: Present the theme list below with descriptions
2. **Ask for their choice**: Ask which theme to apply
3. **Wait for selection**: Get explicit confirmation about the chosen theme
4. **Generate the theme**: Read the selected theme file from `themes/` and generate complete Dart code
5. **Deliver files**: Provide `app_theme.dart`, `app_colors.dart`, `app_typography.dart` ready to drop into their project

## Themes Available

| # | Theme | Vibe | Best For |
|---|-------|------|----------|
| 1 | **Ocean Depths** | Professional & calming maritime | Finance, consulting, corporate |
| 2 | **Sunset Boulevard** | Warm & vibrant energy | Social, lifestyle, food delivery |
| 3 | **Forest Canopy** | Natural & grounded earth tones | Wellness, sustainability, outdoor |
| 4 | **Modern Minimalist** | Clean & contemporary grayscale | Productivity, SaaS, developer tools |
| 5 | **Golden Hour** | Rich & warm autumnal | Photography, luxury, premium |
| 6 | **Arctic Frost** | Cool & crisp winter-inspired | Healthcare, fintech, analytics |
| 7 | **Desert Rose** | Soft & sophisticated dusty tones | Fashion, beauty, lifestyle |
| 8 | **Tech Innovation** | Bold & modern tech aesthetic | Startups, AI/ML, developer |
| 9 | **Botanical Garden** | Fresh & organic garden colors | Health, organic food, plants |
| 10 | **Midnight Galaxy** | Dramatic & cosmic deep tones | Gaming, entertainment, music |
| 11 | **Neon Tokyo** | Cyberpunk, high contrast neon | Gaming, nightlife, tech |
| 12 | **Terracotta Studio** | Warm clay, artisan craft | Art, handmade, interior design |

## Generated Code Structure

Each theme generates:

```
lib/core/theme/
├── app_theme.dart          # ThemeData for light & dark mode
├── app_colors.dart         # Color constants & ColorScheme
├── app_typography.dart     # Google Fonts TextTheme
└── app_spacing.dart        # Consistent spacing scale
```

### app_theme.dart Pattern
```dart
import 'package:flutter/material.dart';
import 'package:google_fonts/google_fonts.dart';
import 'app_colors.dart';
import 'app_typography.dart';

class AppTheme {
  static ThemeData get light => ThemeData(
    useMaterial3: true,
    brightness: Brightness.light,
    colorScheme: AppColors.lightScheme,
    textTheme: AppTypography.textTheme,
    appBarTheme: AppBarTheme(...),
    cardTheme: CardTheme(...),
    elevatedButtonTheme: ElevatedButtonThemeData(...),
    inputDecorationTheme: InputDecorationTheme(...),
    bottomNavigationBarTheme: BottomNavigationBarThemeData(...),
    floatingActionButtonTheme: FloatingActionButtonThemeData(...),
    chipTheme: ChipThemeData(...),
    dividerTheme: DividerThemeData(...),
    // ... all component themes
  );

  static ThemeData get dark => ThemeData(
    useMaterial3: true,
    brightness: Brightness.dark,
    colorScheme: AppColors.darkScheme,
    textTheme: AppTypography.textTheme,
    // ... dark variants
  );
}
```

### app_colors.dart Pattern
```dart
import 'package:flutter/material.dart';

class AppColors {
  // Brand colors
  static const Color primary = Color(0xFF...);
  static const Color secondary = Color(0xFF...);
  static const Color accent = Color(0xFF...);
  static const Color surface = Color(0xFF...);

  // Semantic colors
  static const Color success = Color(0xFF...);
  static const Color warning = Color(0xFF...);
  static const Color error = Color(0xFF...);
  static const Color info = Color(0xFF...);

  // Gradients
  static const LinearGradient primaryGradient = LinearGradient(...);
  static const LinearGradient backgroundGradient = LinearGradient(...);

  // Light scheme
  static const ColorScheme lightScheme = ColorScheme(
    brightness: Brightness.light,
    primary: ...,
    onPrimary: ...,
    secondary: ...,
    onSecondary: ...,
    surface: ...,
    onSurface: ...,
    error: ...,
    onError: ...,
    // ... all 30+ ColorScheme properties
  );

  // Dark scheme
  static const ColorScheme darkScheme = ColorScheme(
    brightness: Brightness.dark,
    // ... dark variants
  );
}
```

### app_typography.dart Pattern
```dart
import 'package:flutter/material.dart';
import 'package:google_fonts/google_fonts.dart';

class AppTypography {
  static String get _displayFont => GoogleFonts.playfairDisplay().fontFamily!;
  static String get _bodyFont => GoogleFonts.sourceSansPro().fontFamily!;

  static TextTheme get textTheme => TextTheme(
    displayLarge: TextStyle(fontFamily: _displayFont, fontSize: 57, fontWeight: FontWeight.w700),
    displayMedium: TextStyle(fontFamily: _displayFont, fontSize: 45, fontWeight: FontWeight.w600),
    displaySmall: TextStyle(fontFamily: _displayFont, fontSize: 36, fontWeight: FontWeight.w600),
    headlineLarge: TextStyle(fontFamily: _displayFont, fontSize: 32, fontWeight: FontWeight.w600),
    headlineMedium: TextStyle(fontFamily: _displayFont, fontSize: 28, fontWeight: FontWeight.w500),
    headlineSmall: TextStyle(fontFamily: _displayFont, fontSize: 24, fontWeight: FontWeight.w500),
    titleLarge: TextStyle(fontFamily: _bodyFont, fontSize: 22, fontWeight: FontWeight.w600),
    titleMedium: TextStyle(fontFamily: _bodyFont, fontSize: 16, fontWeight: FontWeight.w600),
    titleSmall: TextStyle(fontFamily: _bodyFont, fontSize: 14, fontWeight: FontWeight.w500),
    bodyLarge: TextStyle(fontFamily: _bodyFont, fontSize: 16, fontWeight: FontWeight.w400),
    bodyMedium: TextStyle(fontFamily: _bodyFont, fontSize: 14, fontWeight: FontWeight.w400),
    bodySmall: TextStyle(fontFamily: _bodyFont, fontSize: 12, fontWeight: FontWeight.w400),
    labelLarge: TextStyle(fontFamily: _bodyFont, fontSize: 14, fontWeight: FontWeight.w600),
    labelMedium: TextStyle(fontFamily: _bodyFont, fontSize: 12, fontWeight: FontWeight.w500),
    labelSmall: TextStyle(fontFamily: _bodyFont, fontSize: 11, fontWeight: FontWeight.w500),
  );
}
```

## Application Process

After a preferred theme is selected:
1. Read the corresponding theme file from the `themes/` directory
2. Generate complete `app_theme.dart`, `app_colors.dart`, `app_typography.dart`, `app_spacing.dart`
3. Include `pubspec.yaml` dependency additions (`google_fonts`, etc.)
4. Provide usage example in `main.dart`:
```dart
MaterialApp(
  theme: AppTheme.light,
  darkTheme: AppTheme.dark,
  themeMode: ThemeMode.system,
  ...
)
```
5. Ensure WCAG AA contrast ratios in both light and dark mode
6. Test all Material component themes are properly configured

## Create Your Own Theme

For cases where none of the existing themes work:
1. Ask the user for: brand colors (if any), mood/vibe, target audience, app category
2. Generate a custom theme following the same structure as preset themes
3. Give it a descriptive name
4. Show a preview widget that demonstrates the theme across key components
5. Apply the theme after user approval

### Preview Widget
When showing a theme preview, generate a `ThemePreview` widget that displays:
- Color palette swatches
- Typography samples (all text styles)
- Button variants (elevated, filled, outlined, text)
- Card with content
- TextField / Input
- BottomNavigationBar sample
- Chip variants
- Light vs Dark side-by-side comparison
