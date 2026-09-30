const SECOND = 1000;

class RateLimiter {
  constructor(options = {}) {
    this.requestsPerSecond = options.requestsPerSecond || 3;
    this.delayMs = Math.floor(1000 / this.requestsPerSecond);
    this.queue = [];
    this.running = false;
    this.lastRequestTime = 0;
  }

  setRate(requestsPerSecond) {
    this.requestsPerSecond = requestsPerSecond;
    this.delayMs = Math.floor(1000 / requestsPerSecond);
  }

  async execute(fn) {
    return new Promise((resolve, reject) => {
      this.queue.push({ fn, resolve, reject });
      this.processQueue();
    });
  }

  async processQueue() {
    if (this.running || this.queue.length === 0) return;
    this.running = true;

    while (this.queue.length > 0) {
      const now = Date.now();
      const timeSinceLastRequest = now - this.lastRequestTime;

      if (timeSinceLastRequest < this.delayMs) {
        await this.sleep(this.delayMs - timeSinceLastRequest);
      }

      const item = this.queue.shift();
      try {
        this.lastRequestTime = Date.now();
        const result = await item.fn();
        item.resolve(result);
      } catch (err) {
        item.reject(err);
      }
    }

    this.running = false;
  }

  sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  clear() {
    this.queue = [];
    this.running = false;
  }

  get queueLength() {
    return this.queue.length;
  }

  get isRunning() {
    return this.running;
  }
}

function createRateLimiter(options) {
  return new RateLimiter(options);
}

function getDefaultRateLimiter(hasApiKey = false) {
  return new RateLimiter({
    requestsPerSecond: hasApiKey ? 10 : 3
  });
}

function validateDelay(delay) {
  if (typeof delay !== 'number') {
    throw new TypeError('Delay must be a number');
  }
  if (delay < 0) {
    throw new RangeError('Delay must be non-negative');
  }
  if (delay > 60000) {
    throw new RangeError('Delay must not exceed 60000ms');
  }
  return true;
}

function validateRateLimit(limit) {
  if (typeof limit !== 'number') {
    throw new TypeError('Rate limit must be a number');
  }
  if (limit < 1) {
    throw new RangeError('Rate limit must be at least 1');
  }
  if (limit > 100) {
    throw new RangeError('Rate limit must not exceed 100');
  }
  return true;
}

export {
  RateLimiter,
  createRateLimiter,
  getDefaultRateLimiter,
  validateDelay,
  validateRateLimit,
  SECOND
};

export default RateLimiter;
