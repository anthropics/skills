export class NCBIError extends Error {
  constructor(message, code = 'UNKNOWN_ERROR', details = {}) {
    super(message);
    this.name = 'NCBIError';
    this.code = code;
    this.details = details;
    this.timestamp = new Date().toISOString();
  }

  toJSON() {
    return {
      name: this.name,
      message: this.message,
      code: this.code,
      details: this.details,
      timestamp: this.timestamp
    };
  }
}

export class ValidationError extends NCBIError {
  constructor(message, field, receivedValue, details = {}) {
    super(message, 'VALIDATION_ERROR', { field, receivedValue, ...details });
    this.name = 'ValidationError';
  }
}

export class RateLimitError extends NCBIError {
  constructor(message, retryAfter = 60, details = {}) {
    super(message, 'RATE_LIMIT_ERROR', { retryAfter, ...details });
    this.name = 'RateLimitError';
  }
}

export class APIError extends NCBIError {
  constructor(message, errorCode, apiResponse = null, details = {}) {
    super(message, errorCode, { apiResponse, ...details });
    this.name = 'APIError';
  }
}

export class NetworkError extends NCBIError {
  constructor(message, url, originalError, details = {}) {
    super(message, 'NETWORK_ERROR', { url, originalError: originalError?.message, ...details });
    this.name = 'NetworkError';
  }
}

export class TimeoutError extends NCBIError {
  constructor(message, timeout = 30000, details = {}) {
    super(message, 'TIMEOUT_ERROR', { timeout, ...details });
    this.name = 'TimeoutError';
  }
}

export class AuthenticationError extends NCBIError {
  constructor(message, apiKeyIssue = false, details = {}) {
    super(message, 'AUTH_ERROR', { apiKeyIssue, ...details });
    this.name = 'AuthenticationError';
  }
}

export class ParameterError extends NCBIError {
  constructor(message, parameter, expected, received, details = {}) {
    super(message, 'PARAMETER_ERROR', { parameter, expected, received, ...details });
    this.name = 'ParameterError';
  }
}

export function createError(type, ...args) {
  const errorClasses = {
    ValidationError,
    RateLimitError,
    APIError,
    NetworkError,
    TimeoutError,
    AuthenticationError,
    ParameterError,
    NCBIError
  };
  
  const ErrorClass = errorClasses[type] || NCBIError;
  return new ErrorClass(...args);
}

export function handleAPIError(error, context = {}) {
  const { operation, database, parameters } = context;
  
  if (error.code === 'ECONNREFUSED' || error.code === 'ENOTFOUND') {
    return new NetworkError(
      '无法连接到NCBI服务器，请检查网络连接',
      error.config?.url || 'unknown',
      error
    );
  }
  
  if (error.code === 'ETIMEDOUT' || error.message?.includes('timeout')) {
    return new TimeoutError(
      '请求超时，请稍后重试',
      30000,
      { operation, database }
    );
  }
  
  if (error.response) {
    const { status, data } = error.response;
    
    if (status === 429) {
      const retryAfter = parseInt(error.response.headers['retry-after']) || 60;
      return new RateLimitError(
        '已达到API速率限制，请等待后再试',
        retryAfter,
        { operation, database }
      );
    }
    
    if (status === 401 || status === 403) {
      return new AuthenticationError(
        'API密钥无效或已过期',
        status === 403,
        { operation, database }
      );
    }
    
    if (status === 400) {
      return new ParameterError(
        data?.error || '请求参数无效',
        'request',
        'valid parameters',
        { received: parameters, response: data }
      );
    }
    
    if (status >= 500) {
      return new APIError(
        'NCBI服务器错误，请稍后重试',
        `HTTP_${status}`,
        data,
        { operation, database }
      );
    }
  }
  
  return new NCBIError(
    error.message || '发生未知错误',
    'UNKNOWN_ERROR',
    { originalError: error.message, ...context }
  );
}

export function handleValidationError(field, value, expectedType) {
  return new ValidationError(
    `字段 "${field}" 的值无效`,
    field,
    value,
    { expected: expectedType }
  );
}

export function parseNcbiError(error) {
  if (error.name === 'RateLimitError') {
    return {
      message: error.message || '请求过于频繁，请稍后再试',
      suggestion: error.retryAfter ? `请等待 ${error.retryAfter} 秒后重试` : '请稍后重试'
    };
  }
  
  if (error.name === 'ValidationError') {
    return {
      message: error.message || '参数验证失败',
      suggestion: error.details?.field ? `请检查参数 "${error.details.field}" 的值` : '请检查输入参数'
    };
  }
  
  if (error.name === 'AuthenticationError') {
    return {
      message: error.message || '认证失败',
      suggestion: '请检查 API 密钥是否正确'
    };
  }
  
  if (error.name === 'TimeoutError') {
    return {
      message: error.message || '请求超时',
      suggestion: '请增加超时时间或稍后重试'
    };
  }
  
  if (error.name === 'NetworkError') {
    return {
      message: error.message || '网络错误',
      suggestion: '请检查网络连接'
    };
  }
  
  if (error.name === 'APIError') {
    return {
      message: error.message || 'API 请求失败',
      suggestion: error.details?.code ? `错误代码: ${error.details.code}` : '请稍后重试'
    };
  }
  
  return {
    message: error.message || error.toString() || '发生未知错误',
    suggestion: null
  };
}

export default {
  NCBIError,
  ValidationError,
  RateLimitError,
  APIError,
  NetworkError,
  TimeoutError,
  AuthenticationError,
  ParameterError,
  createError,
  handleAPIError,
  handleValidationError
};
