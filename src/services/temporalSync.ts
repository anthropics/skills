/**
 * Temporal Synchronization System
 * Implements circular buffer for "time-travel" correlation between
 * video processing (high latency) and MIDI events (low latency)
 *
 * Problem: MIDI event arrives at time T, but video frame from that
 * exact moment might not be processed yet (video has 50-150ms latency)
 *
 * Solution: Buffer historical poses with timestamps, allowing
 * retrospective lookup of posture at any past moment
 */

import type { PostureAnalysis } from './handPostureDetection.v2';

/**
 * Single entry in the pose history buffer
 */
export interface PoseHistoryEntry {
  timestamp: number; // performance.now() when frame was captured/processed
  frameNumber: number; // Sequential frame counter for debugging
  landmarks: number[][]; // Raw 21 keypoints
  analysis: PostureAnalysis; // Computed posture analysis
  wasCorrelated: boolean; // Has this been matched to a MIDI event?
}

/**
 * MIDI event with pending analysis
 */
export interface PendingMIDIEvent {
  timestamp: number; // performance.now() when event was received
  noteNumber: number; // MIDI note (0-127)
  velocity: number; // Note velocity (0-127)
  channel: number; // MIDI channel
  type: 'noteOn' | 'noteOff';
}

/**
 * Result of correlating MIDI event with posture
 */
export interface CorrelatedEvent {
  midiEvent: PendingMIDIEvent;
  poseEntry: PoseHistoryEntry;
  timeDelta: number; // ms difference between MIDI and pose
  postureScore: number; // 0-100
  wasCorrect: boolean; // Did posture meet threshold?
}

/**
 * Configuration for temporal synchronization
 */
export interface SyncConfig {
  // How long to keep pose history (ms)
  maxHistoryDuration: number;
  // Expected latency offset (ms) - calibrated per system
  // Positive = video lags behind MIDI (typical)
  // Negative = MIDI lags behind video (rare, high-end audio interface)
  latencyOffset: number;
  // Maximum acceptable time delta for correlation (ms)
  maxCorrelationWindow: number;
  // Minimum posture score to consider "correct" (0-100)
  correctPostureThreshold: number;
}

/**
 * Default configuration based on typical web browser performance
 */
export const DEFAULT_SYNC_CONFIG: SyncConfig = {
  maxHistoryDuration: 3000, // 3 seconds of history
  latencyOffset: 80, // Assume ~80ms video processing delay
  maxCorrelationWindow: 150, // Accept matches within ±150ms
  correctPostureThreshold: 75, // 75/100 score = "correct"
};

/**
 * Circular Buffer implementation for pose history
 * Automatically discards old entries to prevent memory leaks
 */
export class PoseHistoryBuffer {
  private buffer: PoseHistoryEntry[] = [];
  private maxDuration: number;
  private frameCounter = 0;

  constructor(maxDuration: number) {
    this.maxDuration = maxDuration;
  }

  /**
   * Add new pose entry to buffer
   */
  push(landmarks: number[][], analysis: PostureAnalysis): void {
    const entry: PoseHistoryEntry = {
      timestamp: performance.now(),
      frameNumber: this.frameCounter++,
      landmarks,
      analysis,
      wasCorrelated: false,
    };

    this.buffer.push(entry);
    this.cleanup();
  }

  /**
   * Find pose entry closest to target timestamp
   * @param targetTime - Timestamp to search for (usually MIDI event time)
   * @param maxDelta - Maximum acceptable time difference (ms)
   * @returns Closest entry, or null if none within maxDelta
   */
  findClosest(targetTime: number, maxDelta: number): PoseHistoryEntry | null {
    if (this.buffer.length === 0) return null;

    let closest: PoseHistoryEntry | null = null;
    let minDelta = Infinity;

    for (const entry of this.buffer) {
      const delta = Math.abs(entry.timestamp - targetTime);
      if (delta < minDelta && delta <= maxDelta) {
        minDelta = delta;
        closest = entry;
      }
    }

    return closest;
  }

  /**
   * Find pose entry at or before target timestamp
   * Useful when video is known to lag behind MIDI
   */
  findAtOrBefore(targetTime: number, maxDelta: number): PoseHistoryEntry | null {
    if (this.buffer.length === 0) return null;

    let best: PoseHistoryEntry | null = null;
    let minDelta = Infinity;

    for (const entry of this.buffer) {
      // Only consider entries at or before target
      if (entry.timestamp <= targetTime) {
        const delta = targetTime - entry.timestamp;
        if (delta < minDelta && delta <= maxDelta) {
          minDelta = delta;
          best = entry;
        }
      }
    }

    return best;
  }

  /**
   * Get all entries within a time range
   * Useful for analyzing posture over a phrase
   */
  getRange(startTime: number, endTime: number): PoseHistoryEntry[] {
    return this.buffer.filter(entry => entry.timestamp >= startTime && entry.timestamp <= endTime);
  }

  /**
   * Get statistics about buffer state
   */
  getStats(): {
    size: number;
    oldestTimestamp: number;
    newestTimestamp: number;
    spanMs: number;
    correlatedCount: number;
  } {
    if (this.buffer.length === 0) {
      return {
        size: 0,
        oldestTimestamp: 0,
        newestTimestamp: 0,
        spanMs: 0,
        correlatedCount: 0,
      };
    }

    return {
      size: this.buffer.length,
      oldestTimestamp: this.buffer[0].timestamp,
      newestTimestamp: this.buffer[this.buffer.length - 1].timestamp,
      spanMs: this.buffer[this.buffer.length - 1].timestamp - this.buffer[0].timestamp,
      correlatedCount: this.buffer.filter(e => e.wasCorrelated).length,
    };
  }

  /**
   * Remove entries older than maxDuration
   */
  private cleanup(): void {
    const now = performance.now();
    const cutoffTime = now - this.maxDuration;

    // Remove from start until we hit an entry within the window
    while (this.buffer.length > 0 && this.buffer[0].timestamp < cutoffTime) {
      this.buffer.shift();
    }
  }

  /**
   * Clear all entries (use when restarting session)
   */
  clear(): void {
    this.buffer = [];
    this.frameCounter = 0;
  }
}

/**
 * MIDI Event Queue
 * Holds MIDI events waiting for correlation with pose data
 */
export class MIDIEventQueue {
  private queue: PendingMIDIEvent[] = [];
  private maxAge: number;

  constructor(maxAge: number) {
    this.maxAge = maxAge;
  }

  /**
   * Add MIDI event to queue
   */
  push(event: PendingMIDIEvent): void {
    this.queue.push(event);
    this.cleanup();
  }

  /**
   * Get all pending events (not yet correlated)
   */
  getAll(): PendingMIDIEvent[] {
    return [...this.queue];
  }

  /**
   * Remove event from queue (after correlation)
   */
  remove(event: PendingMIDIEvent): void {
    const index = this.queue.indexOf(event);
    if (index !== -1) {
      this.queue.splice(index, 1);
    }
  }

  /**
   * Remove events older than maxAge
   */
  private cleanup(): void {
    const now = performance.now();
    const cutoffTime = now - this.maxAge;
    this.queue = this.queue.filter(event => event.timestamp >= cutoffTime);
  }

  /**
   * Clear all events
   */
  clear(): void {
    this.queue = [];
  }

  /**
   * Get queue size
   */
  size(): number {
    return this.queue.length;
  }
}

/**
 * Main Temporal Synchronizer
 * Coordinates pose buffer, MIDI queue, and correlation logic
 */
export class TemporalSynchronizer {
  private poseBuffer: PoseHistoryBuffer;
  private midiQueue: MIDIEventQueue;
  private config: SyncConfig;
  private correlatedEvents: CorrelatedEvent[] = [];
  private maxCorrelatedHistory = 100; // Keep last 100 correlated events

  // Statistics
  private stats = {
    totalMIDIEvents: 0,
    successfulCorrelations: 0,
    failedCorrelations: 0,
    averageTimeDelta: 0,
    averagePostureScore: 0,
  };

  constructor(config: Partial<SyncConfig> = {}) {
    this.config = { ...DEFAULT_SYNC_CONFIG, ...config };
    this.poseBuffer = new PoseHistoryBuffer(this.config.maxHistoryDuration);
    this.midiQueue = new MIDIEventQueue(this.config.maxHistoryDuration);
  }

  /**
   * Add new pose to buffer
   */
  addPose(landmarks: number[][], analysis: PostureAnalysis): void {
    this.poseBuffer.push(landmarks, analysis);

    // Try to correlate pending MIDI events
    this.processCorrelations();
  }

  /**
   * Add MIDI event for correlation
   */
  addMIDIEvent(event: PendingMIDIEvent): void {
    this.midiQueue.push(event);
    this.stats.totalMIDIEvents++;

    // Try immediate correlation
    this.processCorrelations();
  }

  /**
   * Process pending correlations
   * Called after each new pose or MIDI event
   */
  private processCorrelations(): void {
    const pendingEvents = this.midiQueue.getAll();

    for (const midiEvent of pendingEvents) {
      // Adjust MIDI timestamp by latency offset
      const adjustedTime = midiEvent.timestamp + this.config.latencyOffset;

      // Find closest pose
      const poseEntry = this.poseBuffer.findClosest(adjustedTime, this.config.maxCorrelationWindow);

      if (poseEntry) {
        // Successful correlation!
        const timeDelta = Math.abs(poseEntry.timestamp - adjustedTime);

        const correlated: CorrelatedEvent = {
          midiEvent,
          poseEntry,
          timeDelta,
          postureScore: poseEntry.analysis.score,
          wasCorrect: poseEntry.analysis.score >= this.config.correctPostureThreshold,
        };

        this.correlatedEvents.push(correlated);
        poseEntry.wasCorrelated = true;
        this.midiQueue.remove(midiEvent);

        // Update statistics
        this.stats.successfulCorrelations++;
        this.updateStats(correlated);

        // Trim correlatedEvents to prevent unbounded growth
        if (this.correlatedEvents.length > this.maxCorrelatedHistory) {
          this.correlatedEvents.shift();
        }
      } else {
        // Check if event is too old to ever be correlated
        const eventAge = performance.now() - midiEvent.timestamp;
        if (eventAge > this.config.maxHistoryDuration) {
          this.midiQueue.remove(midiEvent);
          this.stats.failedCorrelations++;
        }
      }
    }
  }

  /**
   * Update running statistics
   */
  private updateStats(event: CorrelatedEvent): void {
    const n = this.stats.successfulCorrelations;

    // Running average of time delta
    this.stats.averageTimeDelta = (this.stats.averageTimeDelta * (n - 1) + event.timeDelta) / n;

    // Running average of posture score
    this.stats.averagePostureScore =
      (this.stats.averagePostureScore * (n - 1) + event.postureScore) / n;
  }

  /**
   * Get recent correlated events
   */
  getRecentCorrelations(count = 10): CorrelatedEvent[] {
    return this.correlatedEvents.slice(-count);
  }

  /**
   * Get all correlated events in time range
   */
  getCorrelationsInRange(startTime: number, endTime: number): CorrelatedEvent[] {
    return this.correlatedEvents.filter(
      event => event.midiEvent.timestamp >= startTime && event.midiEvent.timestamp <= endTime
    );
  }

  /**
   * Calculate accuracy over recent correlations
   * Returns percentage of notes played with correct posture
   */
  getAccuracy(recentCount = 20): number {
    const recent = this.correlatedEvents.slice(-recentCount);
    if (recent.length === 0) return 0;

    const correct = recent.filter(e => e.wasCorrect).length;
    return (correct / recent.length) * 100;
  }

  /**
   * Get comprehensive statistics
   */
  getStats(): typeof this.stats & {
    pendingMIDI: number;
    poseBufferSize: number;
    accuracy: number;
  } {
    return {
      ...this.stats,
      pendingMIDI: this.midiQueue.size(),
      poseBufferSize: this.poseBuffer.getStats().size,
      accuracy: this.getAccuracy(),
    };
  }

  /**
   * Calibrate latency offset based on recent correlations
   * Call this after ~30 seconds of playing for auto-calibration
   */
  calibrateLatency(): number {
    const recent = this.correlatedEvents.slice(-50);
    if (recent.length < 10) {
      console.warn('Not enough data for latency calibration');
      return this.config.latencyOffset;
    }

    // Calculate average time delta
    const avgDelta = recent.reduce((sum, e) => sum + e.timeDelta, 0) / recent.length;

    // Adjust offset to minimize delta
    const newOffset = this.config.latencyOffset + avgDelta;

    // console.log(`Latency calibration: ${this.config.latencyOffset}ms → ${newOffset.toFixed(0)}ms`);

    this.config.latencyOffset = newOffset;
    return newOffset;
  }

  /**
   * Reset synchronizer state
   */
  reset(): void {
    this.poseBuffer.clear();
    this.midiQueue.clear();
    this.correlatedEvents = [];
    this.stats = {
      totalMIDIEvents: 0,
      successfulCorrelations: 0,
      failedCorrelations: 0,
      averageTimeDelta: 0,
      averagePostureScore: 0,
    };
  }

  /**
   * Update configuration
   */
  updateConfig(newConfig: Partial<SyncConfig>): void {
    this.config = { ...this.config, ...newConfig };
  }
}
