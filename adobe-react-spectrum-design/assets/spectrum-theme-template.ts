/**
 * React Spectrum Custom Theme Template
 *
 * This template demonstrates how to create a complete custom theme
 * for React Spectrum v3.45.0
 *
 * Usage:
 *   import { customTheme } from './spectrum-theme-template';
 *
 *   <Provider theme={customTheme}>
 *     <App />
 *   </Provider>
 */

import { Theme } from '@adobe/react-spectrum';

/**
 * Color Palette
 *
 * Define your color scales here. Each color family should have
 * a 12-step scale from lightest (50) to darkest (900).
 */
const colorPalette = {
  // Primary brand color - customize with your brand colors
  blue: {
    50: '#f0f4ff',
    75: '#e8ecff',
    100: '#e1e8ff',
    200: '#c2d0ff',
    300: '#a3b8ff',
    400: '#84a0ff',
    500: '#6b8cff', // Primary action color
    600: '#5272e8',
    700: '#3958d1',
    800: '#203ebc',
    900: '#0824a5',
  },

  // Secondary brand color - customize as needed
  teal: {
    50: '#e8f8f5',
    75: '#d4f0ed',
    100: '#c0e8e5',
    200: '#8dd9d1',
    300: '#5acabd',
    400: '#27bba9',
    500: '#00ac95', // Secondary action color
    600: '#009d82',
    700: '#008e6f',
    800: '#007f5c',
    900: '#007049',
  },

  // Neutral/Gray scale - used for text, backgrounds, borders
  gray: {
    50: '#fafbfc',
    75: '#f7f8fa',
    100: '#f5f6f8',
    200: '#ebeef3',
    300: '#d5dae5',
    400: '#b0b8ca',
    500: '#8b93a8',
    600: '#737f8f',
    700: '#565e6d',
    800: '#2f3439',
    900: '#121518',
  },

  // Semantic colors
  success: {
    50: '#f0f9f6',
    75: '#d9f2ea',
    100: '#c2ebde',
    200: '#8bd9be',
    300: '#54c79e',
    400: '#1db57e',
    500: '#11a538', // Positive/success color
    600: '#0d8f2a',
    700: '#097320',
    800: '#055d16',
    900: '#02470c',
  },

  // Warning color
  orange: {
    50: '#fffbf7',
    75: '#fff3eb',
    100: '#ffebd8',
    200: '#ffcfa3',
    300: '#ffb36d',
    400: '#ff9438',
    500: '#f8860b', // Notice/warning color
    600: '#e07608',
    700: '#c86005',
    800: '#b04a02',
    900: '#983400',
  },

  // Error/destructive color
  red: {
    50: '#fff5f5',
    75: '#ffe8e8',
    100: '#ffdada',
    200: '#ffb3b3',
    300: '#ff8d8d',
    400: '#ff6666',
    500: '#e63946', // Negative/error color
    600: '#d41f3a',
    700: '#c2082d',
    800: '#b00020',
    900: '#7d0014',
  },

  // Info/accent color
  purple: {
    50: '#f9f5ff',
    75: '#f2ebff',
    100: '#ede0ff',
    200: '#dcc0ff',
    300: '#cba0ff',
    400: '#bb81ff',
    500: '#ab61ff', // Info/accent color
    600: '#9b4dff',
    700: '#8b39ff',
    800: '#7b25ff',
    900: '#6b11ff',
  },
};

/**
 * Spectrum Theme Definition
 *
 * This is the main theme object that contains all the design tokens.
 * Customize the values to match your brand and design system.
 */
export const customTheme: Theme = {
  // Global color tokens
  global: {
    // Primary colors (used for main actions, links, focus states)
    colorPrimary: colorPalette.blue[500],
    colorSecondary: colorPalette.teal[500],

    // Semantic colors
    colorPositive: colorPalette.success[500],
    colorNegative: colorPalette.red[500],
    colorNotice: colorPalette.orange[500],
    colorInfo: colorPalette.purple[500],

    // Neutral colors (text, backgrounds, borders)
    colorGray50: colorPalette.gray[50],
    colorGray75: colorPalette.gray[75],
    colorGray100: colorPalette.gray[100],
    colorGray200: colorPalette.gray[200],
    colorGray300: colorPalette.gray[300],
    colorGray400: colorPalette.gray[400],
    colorGray500: colorPalette.gray[500],
    colorGray600: colorPalette.gray[600],
    colorGray700: colorPalette.gray[700],
    colorGray800: colorPalette.gray[800],
    colorGray900: colorPalette.gray[900],
  },

  // Component-specific overrides
  components: {
    // Button styling
    button: {
      // CTA (call-to-action) buttons
      primary: {
        backgroundColor: colorPalette.blue[500],
        color: '#ffffff',
        padding: '8px 16px',
        fontSize: '14px',
        fontWeight: 600,
        borderRadius: '4px',
        transition: 'background-color 200ms ease-in-out',

        '&:hover': {
          backgroundColor: colorPalette.blue[600],
        },

        '&:active': {
          backgroundColor: colorPalette.blue[700],
        },

        '&:disabled': {
          backgroundColor: colorPalette.gray[300],
          color: colorPalette.gray[500],
          cursor: 'not-allowed',
        },

        '&:focus-visible': {
          outline: `3px solid ${colorPalette.blue[500]}`,
          outlineOffset: '2px',
        },
      },

      // Secondary buttons
      secondary: {
        backgroundColor: colorPalette.gray[100],
        color: colorPalette.gray[900],
        border: `1px solid ${colorPalette.gray[300]}`,
        padding: '8px 16px',
        fontSize: '14px',
        fontWeight: 600,
        borderRadius: '4px',
        transition: 'all 200ms ease-in-out',

        '&:hover': {
          backgroundColor: colorPalette.gray[200],
        },

        '&:active': {
          backgroundColor: colorPalette.gray[300],
        },

        '&:disabled': {
          backgroundColor: colorPalette.gray[100],
          color: colorPalette.gray[400],
          cursor: 'not-allowed',
        },
      },
    },

    // Text input styling
    textfield: {
      // Normal input
      normal: {
        fontSize: '14px',
        padding: '8px 12px',
        border: `1px solid ${colorPalette.gray[300]}`,
        borderRadius: '4px',
        backgroundColor: '#ffffff',
        color: colorPalette.gray[900],
        transition: 'border-color 200ms ease-in-out',

        '&:focus': {
          borderColor: colorPalette.blue[500],
          outline: 'none',
          boxShadow: `0 0 0 3px ${colorPalette.blue[50]}`,
        },

        '&:disabled': {
          backgroundColor: colorPalette.gray[50],
          color: colorPalette.gray[500],
          borderColor: colorPalette.gray[200],
        },
      },

      // Error/invalid state
      invalid: {
        borderColor: colorPalette.red[500],

        '&:focus': {
          borderColor: colorPalette.red[500],
          boxShadow: `0 0 0 3px ${colorPalette.red[50]}`,
        },
      },

      // Valid/success state
      valid: {
        borderColor: colorPalette.success[500],

        '&:focus': {
          borderColor: colorPalette.success[500],
          boxShadow: `0 0 0 3px ${colorPalette.success[50]}`,
        },
      },
    },

    // Checkbox and radio styling
    checkbox: {
      checkmarkColor: '#ffffff',
      checkboxBorder: `2px solid ${colorPalette.gray[400]}`,
      checkboxBackground: '#ffffff',
      checkedBackground: colorPalette.blue[500],
      checkedBorder: `2px solid ${colorPalette.blue[500]}`,
      borderRadius: '4px',
      size: '18px',

      '&:focus-visible': {
        outline: `3px solid ${colorPalette.blue[500]}`,
        outlineOffset: '2px',
      },
    },

    // Dialog styling
    dialog: {
      backgroundColor: '#ffffff',
      borderRadius: '8px',
      boxShadow: `0 10px 40px rgba(0, 0, 0, 0.1)`,
      padding: '24px',
      maxWidth: '600px',
    },
  },

  // Typography scale
  typography: {
    // Display heading (large, prominent)
    displayLarge: {
      fontSize: '32px',
      lineHeight: '40px',
      fontWeight: 700,
      letterSpacing: '-0.5px',
    },

    displayMedium: {
      fontSize: '28px',
      lineHeight: '36px',
      fontWeight: 700,
      letterSpacing: '-0.25px',
    },

    displaySmall: {
      fontSize: '24px',
      lineHeight: '32px',
      fontWeight: 700,
    },

    // Heading styles
    headingLarge: {
      fontSize: '20px',
      lineHeight: '28px',
      fontWeight: 700,
    },

    headingMedium: {
      fontSize: '18px',
      lineHeight: '26px',
      fontWeight: 700,
    },

    headingSmall: {
      fontSize: '16px',
      lineHeight: '24px',
      fontWeight: 700,
    },

    // Body text
    bodyLarge: {
      fontSize: '16px',
      lineHeight: '24px',
      fontWeight: 400,
    },

    bodyRegular: {
      fontSize: '14px',
      lineHeight: '22px',
      fontWeight: 400,
    },

    bodySmall: {
      fontSize: '12px',
      lineHeight: '20px',
      fontWeight: 400,
    },

    // Captions and labels
    captionLarge: {
      fontSize: '13px',
      lineHeight: '20px',
      fontWeight: 500,
    },

    captionRegular: {
      fontSize: '12px',
      lineHeight: '18px',
      fontWeight: 500,
    },
  },

  // Spacing scale (8px base unit)
  dimension: {
    spacing: {
      xs: '4px',      // size-50
      sm: '8px',      // size-100
      md: '16px',     // size-200
      lg: '24px',     // size-300
      xl: '32px',     // size-400
      xxl: '40px',    // size-500
      '3xl': '48px',  // size-600
      '4xl': '64px',  // size-800
      '5xl': '80px',  // size-1000
    },

    borderRadius: {
      none: '0px',
      xs: '2px',
      sm: '4px',
      md: '6px',
      lg: '8px',
      xl: '12px',
      full: '50%',
    },

    shadow: {
      none: 'none',
      sm: '0 1px 2px rgba(0, 0, 0, 0.05)',
      md: '0 4px 6px rgba(0, 0, 0, 0.1)',
      lg: '0 10px 15px rgba(0, 0, 0, 0.15)',
      xl: '0 20px 25px rgba(0, 0, 0, 0.2)',
    },
  },

  // Animation tokens
  animation: {
    duration: {
      fast: '100ms',
      normal: '200ms',
      slow: '300ms',
    },

    easing: {
      easeIn: 'cubic-bezier(0.4, 0, 1, 1)',
      easeOut: 'cubic-bezier(0, 0, 0.2, 1)',
      easeInOut: 'cubic-bezier(0.4, 0, 0.2, 1)',
      linear: 'linear',
    },
  },

  // Responsive breakpoints
  breakpoints: {
    mobile: '0px',
    tablet: '640px',
    desktop: '1024px',
    wide: '1280px',
  },
};

/**
 * Dark Theme Variant
 *
 * Customize this for your dark mode theme.
 * Ensure sufficient color contrast (7:1 for text).
 */
export const customDarkTheme: Theme = {
  ...customTheme,

  global: {
    ...customTheme.global,
    // Override with dark-appropriate colors
  },

  components: {
    ...customTheme.components,
    dialog: {
      ...customTheme.components.dialog,
      backgroundColor: colorPalette.gray[900],
      color: colorPalette.gray[50],
    },
  },
};

/**
 * Compact Theme Variant
 *
 * Reduced spacing for dense information display.
 */
export const compactTheme: Theme = {
  ...customTheme,

  dimension: {
    ...customTheme.dimension,
    spacing: {
      xs: '2px',
      sm: '4px',
      md: '8px',
      lg: '12px',
      xl: '16px',
      xxl: '20px',
      '3xl': '24px',
      '4xl': '32px',
      '5xl': '40px',
    },
  },
};

/**
 * Accessible Theme Variant
 *
 * Increased spacing and larger fonts for better readability.
 */
export const accessibleTheme: Theme = {
  ...customTheme,

  typography: {
    ...customTheme.typography,
    bodyLarge: {
      fontSize: '18px',
      lineHeight: '28px',
      fontWeight: 400,
    },
    bodyRegular: {
      fontSize: '16px',
      lineHeight: '24px',
      fontWeight: 400,
    },
  },

  dimension: {
    ...customTheme.dimension,
    spacing: {
      xs: '8px',
      sm: '12px',
      md: '24px',
      lg: '32px',
      xl: '40px',
      xxl: '48px',
      '3xl': '64px',
      '4xl': '80px',
      '5xl': '96px',
    },
  },
};

/**
 * Usage Examples
 */

/*
// Basic usage
import { Provider } from '@adobe/react-spectrum';
import { customTheme } from './spectrum-theme-template';

export function App() {
  return (
    <Provider theme={customTheme} locale="en-US">
      <YourComponents />
    </Provider>
  );
}

// Theme switching
import { useState } from 'react';

export function ThemedApp() {
  const [theme, setTheme] = useState(customTheme);

  const switchToDark = () => setTheme(customDarkTheme);
  const switchToLight = () => setTheme(customTheme);
  const switchToCompact = () => setTheme(compactTheme);

  return (
    <Provider theme={theme}>
      <Button onPress={switchToLight}>Light</Button>
      <Button onPress={switchToDark}>Dark</Button>
      <Button onPress={switchToCompact}>Compact</Button>
      <YourComponents />
    </Provider>
  );
}

// Responsive theme
export function ResponsiveThemedApp() {
  const prefersDark = window.matchMedia(
    '(prefers-color-scheme: dark)'
  ).matches;

  const theme = prefersDark ? customDarkTheme : customTheme;

  return (
    <Provider theme={theme}>
      <YourComponents />
    </Provider>
  );
}
*/
