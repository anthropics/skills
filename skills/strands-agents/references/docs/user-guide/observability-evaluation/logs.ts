/**
 * TypeScript logging examples for Strands SDK documentation.
 * 
 * These examples demonstrate how to configure logging in the TypeScript SDK.
 */

import { configureLogging, type Logger } from '@strands-agents/sdk'

// --8<-- [start:basic_console]
// Use the default console for logging
configureLogging(console)
// --8<-- [end:basic_console]

// Example with Pino
// --8<-- [start:pino_setup]
import pino from 'pino'

const pinoLogger = pino({
  level: 'debug',
  transport: {
    target: 'pino-pretty',
    options: {
      colorize: true
    }
  }
})

configureLogging(pinoLogger)
// --8<-- [end:pino_setup]

// Custom logger implementation
// --8<-- [start:custom_logger]
// Declare a mock logging service type for documentation
declare const myLoggingService: {
  log(level: string, ...args: unknown[]): void
}

const customLogger: Logger = {
  debug: (...args: unknown[]) => {
    // Send to your logging service
    myLoggingService.log('DEBUG', ...args)
  },
  info: (...args: unknown[]) => {
    myLoggingService.log('INFO', ...args)
  },
  warn: (...args: unknown[]) => {
    myLoggingService.log('WARN', ...args)
  },
  error: (...args: unknown[]) => {
    myLoggingService.log('ERROR', ...args)
  }
}

configureLogging(customLogger)
// --8<-- [end:custom_logger]

