export const themes = {
  white: {
    name: '简约白',
    tokens: {
      background: '#FFFFFF',
      backgroundElevated: '#F5F5F7',
      textPrimary: '#1D1D1F',
      textSecondary: '#424245',
      textTertiary: '#86868B',
      accent: '#0071E3',
      accentMuted: '#E8F4FD',
      border: '#D2D2D7',
      codeBackground: '#F5F5F7',
    },
    typography: {
      fontCJK: "'PingFang SC', 'Noto Sans SC', 'Microsoft YaHei', sans-serif",
      fontHeading: "'PingFang SC', 'Noto Sans SC', 'Microsoft YaHei', sans-serif",
    },
    spacing: { padding: 130, gap: 48 },
    radius: { image: 12, code: 12 },
  },
  dark: {
    name: '深色模式',
    tokens: {
      background: '#1C1C1E',
      backgroundElevated: '#2C2C2E',
      textPrimary: '#F5F5F7',
      textSecondary: '#98989D',
      textTertiary: '#636366',
      accent: '#0A84FF',
      accentMuted: '#1A3A5C',
      border: '#38383A',
      codeBackground: '#2C2C2E',
    },
    typography: {
      fontCJK: "'PingFang SC', 'Microsoft YaHei', 'Hiragino Sans GB', sans-serif",
      fontHeading: "'PingFang SC', 'Microsoft YaHei', 'Hiragino Sans GB', sans-serif",
    },
    spacing: { padding: 130, gap: 48 },
    radius: { image: 12, code: 12 },
  },
};
