/**
 * NCBI Database Skill - Main Entry Point
 * 
 * Query NCBI databases via E-utilities API
 * 
 * @module ncbi-database-skill
 */

import NCBIClient from './ncbi-client.js';
import { 
  NCBIError, 
  ValidationError, 
  APIError, 
  NetworkError, 
  TimeoutError 
} from './errors.js';
import { 
  validateDb, 
  validateId, 
  validateTerm, 
  validateRetMax, 
  validateRetMode, 
  validateEmail, 
  validateDelay 
} from './validators.js';
import RateLimiter from './rate-limiter.js';

export { 
  NCBIClient,
  NCBIError,
  ValidationError,
  APIError,
  NetworkError,
  TimeoutError,
  validateDb,
  validateId,
  validateTerm,
  validateRetMax,
  validateRetMode,
  validateEmail,
  validateDelay,
  RateLimiter
};

// Version from package.json
export { version } from '../package.json' assert { type: 'json' };
