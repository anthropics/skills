/** @type {import('next').NextConfig} */
const nextConfig = {
  webpack: (config) => {
    // Required for @imgly/background-removal (WASM-based)
    config.resolve.fallback = {
      ...config.resolve.fallback,
      fs: false,
      path: false,
    };
    return config;
  },
};

module.exports = nextConfig;
