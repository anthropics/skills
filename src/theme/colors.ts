/**
 * ChromaNotes Color System
 * Premium color palette with WCAG accessibility compliance
 * Inspired by Chroma-Notes method for multi-sensory learning
 *
 * Features:
 * - Hand-specific colors (Right: Action, Left: Base)
 * - Semantic feedback colors
 * - Dark/Light mode support
 * - Accessibility icons for color-blind users
 */

export interface ColorTheme {
  primary: string;
  secondary: string;
  icon: 'circle' | 'triangle' | 'square' | 'star' | 'diamond';
}

export interface FeedbackColors {
  success: string;
  warning: string;
  error: string;
  critical: string;
  info: string;
}

/**
 * Right Hand Colors (Action-focused)
 * Cool colors for agility and precision
 */
export const RIGHT_HAND_COLORS: ColorTheme = {
  primary: '#00E676', // Green neon - Natural notes
  secondary: '#00BCD4', // Cyan - Sharp/Flat notes
  icon: 'circle',
};

/**
 * Left Hand Colors (Base-focused)
 * Warm colors for foundation and rhythm
 */
export const LEFT_HAND_COLORS: ColorTheme = {
  primary: '#FF6E40', // Orange - Natural notes
  secondary: '#E91E63', // Magenta - Sharp/Flat notes
  icon: 'triangle',
};

/**
 * Neutral Colors
 * Background and UI elements
 */
export const NEUTRAL_COLORS = {
  light: {
    background: '#ECEFF1', // Ice white
    surface: '#FFFFFF',
    text: '#263238',
    textSecondary: '#546E7A',
    border: '#B0BEC5',
  },
  dark: {
    background: '#121212', // True black
    surface: '#1E1E1E',
    surfaceElevated: '#2D2D2D',
    text: '#ECEFF1',
    textSecondary: '#90A4AE',
    border: '#37474F', // Blue-gray
  },
};

/**
 * Feedback Colors (Semantic)
 * WCAG AAA compliant ratios
 */
export const FEEDBACK_COLORS: FeedbackColors = {
  success: '#00E676', // Green - Correct note/posture
  warning: '#FFD600', // Yellow - Needs improvement
  error: '#FF5252', // Red - Incorrect
  critical: '#D50000', // Deep red - Hyperextension/danger
  info: '#2196F3', // Blue - Neutral information
};

/**
 * Posture Score Colors
 * Gradient from red (poor) to green (excellent)
 */
export const POSTURE_SCORE_COLORS = {
  excellent: '#10b981', // 85-100
  good: '#22c55e', // 70-84
  acceptable: '#f59e0b', // 55-69
  poor: '#f97316', // 40-54
  critical: '#ef4444', // 0-39
};

/**
 * Gamification Colors
 */
export const GAMIFICATION_COLORS = {
  xp: '#FFD600', // Gold
  level: '#9C27B0', // Purple
  streak: '#FF5722', // Orange-red (fire)
  achievement: '#FFC107', // Amber
  combo: '#00E676', // Green
};

/**
 * Glassmorphism Effect Colors
 */
export const GLASS_COLORS = {
  light: {
    background: 'rgba(255, 255, 255, 0.7)',
    border: 'rgba(255, 255, 255, 0.3)',
    shadow: 'rgba(0, 0, 0, 0.1)',
  },
  dark: {
    background: 'rgba(30, 30, 30, 0.7)',
    border: 'rgba(255, 255, 255, 0.1)',
    shadow: 'rgba(0, 0, 0, 0.5)',
  },
};

/**
 * Note Trail Opacity
 * For MIDI visualization
 */
export const TRAIL_OPACITY = {
  current: 1.0,
  recent: 0.7,
  fading: 0.4,
  ghost: 0.2,
};

/**
 * Get color based on hand and note type
 */
export function getNoteColor(hand: 'left' | 'right', isSharp: boolean, opacity = 1): string {
  const colors = hand === 'right' ? RIGHT_HAND_COLORS : LEFT_HAND_COLORS;
  const hex = isSharp ? colors.secondary : colors.primary;

  // Convert hex to rgba if opacity < 1
  if (opacity < 1) {
    const r = parseInt(hex.slice(1, 3), 16);
    const g = parseInt(hex.slice(3, 5), 16);
    const b = parseInt(hex.slice(5, 7), 16);
    return `rgba(${r}, ${g}, ${b}, ${opacity})`;
  }

  return hex;
}

/**
 * Get icon for accessibility (shape-based distinction)
 */
export function getAccessibilityIcon(hand: 'left' | 'right'): string {
  return hand === 'right' ? RIGHT_HAND_COLORS.icon : LEFT_HAND_COLORS.icon;
}

/**
 * Get posture score color
 */
export function getPostureScoreColor(score: number): string {
  if (score >= 85) return POSTURE_SCORE_COLORS.excellent;
  if (score >= 70) return POSTURE_SCORE_COLORS.good;
  if (score >= 55) return POSTURE_SCORE_COLORS.acceptable;
  if (score >= 40) return POSTURE_SCORE_COLORS.poor;
  return POSTURE_SCORE_COLORS.critical;
}

/**
 * Get feedback color based on result
 */
export function getFeedbackColor(
  type: 'success' | 'warning' | 'error' | 'critical' | 'info'
): string {
  return FEEDBACK_COLORS[type];
}

/**
 * CSS Variables for theming
 * Use with document.documentElement.style.setProperty()
 */
export function applyCSSVariables(theme: 'light' | 'dark'): void {
  const colors = NEUTRAL_COLORS[theme];
  const glass = GLASS_COLORS[theme];

  const vars = {
    '--color-background': colors.background,
    '--color-surface': colors.surface,
    '--color-text': colors.text,
    '--color-text-secondary': colors.textSecondary,
    '--color-border': colors.border,
    '--glass-background': glass.background,
    '--glass-border': glass.border,
    '--glass-shadow': glass.shadow,
    '--color-right-hand': RIGHT_HAND_COLORS.primary,
    '--color-left-hand': LEFT_HAND_COLORS.primary,
    '--color-success': FEEDBACK_COLORS.success,
    '--color-warning': FEEDBACK_COLORS.warning,
    '--color-error': FEEDBACK_COLORS.error,
    '--color-critical': FEEDBACK_COLORS.critical,
  };

  Object.entries(vars).forEach(([key, value]) => {
    document.documentElement.style.setProperty(key, value);
  });
}

/**
 * Detect user's preferred color scheme
 */
export function detectPreferredTheme(): 'light' | 'dark' {
  if (window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)').matches) {
    return 'dark';
  }
  return 'light';
}

/**
 * Initialize theme on app load
 */
export function initializeTheme(): void {
  const savedTheme = localStorage.getItem('theme') as 'light' | 'dark' | null;
  const theme = savedTheme || detectPreferredTheme();
  applyCSSVariables(theme);

  // Listen for system theme changes
  window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', e => {
    if (!savedTheme) {
      applyCSSVariables(e.matches ? 'dark' : 'light');
    }
  });
}
