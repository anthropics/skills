export class AuthError extends Error {
  constructor(message = 'AuthError') {
    super(message);
    this.name = 'AuthError';
  }
}

export class APIError extends Error {
  constructor(message = 'APIError') {
    super(message);
    this.name = 'APIError';
  }
}

export class ImageGenerationError extends APIError {
  constructor(message = 'ImageGenerationError') {
    super(message);
    this.name = 'ImageGenerationError';
  }
}

export class GeminiError extends Error {
  constructor(message = 'GeminiError') {
    super(message);
    this.name = 'GeminiError';
  }
}

export class TimeoutError extends GeminiError {
  constructor(message = 'TimeoutError') {
    super(message);
    this.name = 'TimeoutError';
  }
}

export class UsageLimitExceeded extends GeminiError {
  constructor(message = 'UsageLimitExceeded') {
    super(message);
    this.name = 'UsageLimitExceeded';
  }
}

export class ModelInvalid extends GeminiError {
  constructor(message = 'ModelInvalid') {
    super(message);
    this.name = 'ModelInvalid';
  }
}

export class TemporarilyBlocked extends GeminiError {
  constructor(message = 'TemporarilyBlocked') {
    super(message);
    this.name = 'TemporarilyBlocked';
  }
}

