export interface Logger {
  info(message: string): void;
  warn(message: string): void;
  error(message: string): void;
  debug(message: string): void;
}

export function createLogger(debugEnabled = false): Logger {
  const print = (level: string, message: string): void => {
    console.error(`[${level}] ${message}`);
  };

  return {
    info(message: string) {
      print("info", message);
    },
    warn(message: string) {
      print("warn", message);
    },
    error(message: string) {
      print("error", message);
    },
    debug(message: string) {
      if (debugEnabled) {
        print("debug", message);
      }
    },
  };
}

