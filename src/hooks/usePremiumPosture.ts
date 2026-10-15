/**
 * Premium Posture Analysis Hook
 * Integrates HandPostureAnalyzerV2, TemporalSynchronizer, and Gamification
 *
 * Features:
 * - Real-time posture analysis with 3D vector math
 * - MIDI-Pose temporal correlation
 * - XP bonuses for correct posture
 * - Performance metrics tracking
 */

import { useRef, useEffect, useCallback, useState } from 'react';
import { HandPostureAnalyzerV2, type PostureAnalysis } from '../services/handPostureDetection.v2';
import {
  TemporalSynchronizer,
  type PendingMIDIEvent,
  type CorrelatedEvent,
} from '../services/temporalSync';

interface UsePremiumPostureConfig {
  onPostureUpdate?: (analysis: PostureAnalysis) => void;
  onCorrelation?: (event: CorrelatedEvent) => void;
  onBonusXP?: (xp: number) => void; // Callback for XP rewards
  onAchievement?: (achievementId: string) => void; // Callback for achievements
  enableBonusXP?: boolean;
  postureThreshold?: number; // Minimum score for "correct" (0-100)
}

interface PremiumPostureState {
  currentAnalysis: PostureAnalysis | null;
  accuracy: number; // MIDI-Posture correlation accuracy (0-100)
  totalCorrelations: number;
  averagePostureScore: number;
  bonusXPEarned: number;
}

/**
 * Premium Posture Analysis Hook
 * Combines V2 analysis, temporal sync, and gamification
 */
export function usePremiumPosture(config: UsePremiumPostureConfig = {}) {
  const {
    onPostureUpdate,
    onCorrelation,
    onBonusXP,
    onAchievement,
    enableBonusXP = true,
    postureThreshold = 75,
  } = config;

  // Initialize synchronizer (singleton per session)
  const synchronizerRef = useRef<TemporalSynchronizer>(
    new TemporalSynchronizer({
      correctPostureThreshold: postureThreshold,
    })
  );

  // State tracking
  const [state, setState] = useState<PremiumPostureState>({
    currentAnalysis: null,
    accuracy: 0,
    totalCorrelations: 0,
    averagePostureScore: 0,
    bonusXPEarned: 0,
  });

  // Initialize filters (once)
  useEffect(() => {
    HandPostureAnalyzerV2.initializeFilters(0.7); // EMA alpha

    return () => {
      synchronizerRef.current.reset();
      HandPostureAnalyzerV2.resetFilters();
    };
  }, []);

  /**
   * Process pose from ml5.js handpose
   */
  const processPose = useCallback(
    (landmarks: number[][]) => {
      const handLandmarks = {
        keypoints: landmarks,
        handedness: 'Right' as const,
        confidence: 0.9,
      };

      // Analyze with V2 (includes EMA filtering)
      const analysis = HandPostureAnalyzerV2.analyzePosture(handLandmarks);

      // Add to temporal buffer
      synchronizerRef.current.addPose(landmarks, analysis);

      // Update state
      setState(prev => {
        const stats = synchronizerRef.current.getStats();
        return {
          ...prev,
          currentAnalysis: analysis,
          accuracy: stats.accuracy,
          totalCorrelations: stats.successfulCorrelations,
          averagePostureScore: stats.averagePostureScore,
        };
      });

      // Callback for external handling
      onPostureUpdate?.(analysis);

      // Check for achievements
      checkPostureAchievements(analysis);
    },
    [onPostureUpdate]
  );

  /**
   * Process MIDI event
   */
  const processMIDIEvent = useCallback(
    (event: PendingMIDIEvent) => {
      synchronizerRef.current.addMIDIEvent(event);

      // Get recent correlations
      const recent = synchronizerRef.current.getRecentCorrelations(1);

      if (recent.length > 0 && enableBonusXP) {
        const correlated = recent[0];

        // Award bonus XP for correct posture during note
        if (correlated.wasCorrect) {
          const bonusXP = calculateBonusXP(correlated.postureScore);
          onBonusXP?.(bonusXP);

          setState(prev => ({
            ...prev,
            bonusXPEarned: prev.bonusXPEarned + bonusXP,
          }));
        }

        onCorrelation?.(correlated);
      }
    },
    [enableBonusXP, onCorrelation, onBonusXP]
  );

  /**
   * Calculate bonus XP based on posture score
   */
  const calculateBonusXP = (postureScore: number): number => {
    if (postureScore >= 90) return 10; // Excellent
    if (postureScore >= 80) return 5; // Good
    if (postureScore >= 70) return 3; // Acceptable
    return 0;
  };

  /**
   * Check for posture-related achievements
   */
  const checkPostureAchievements = (analysis: PostureAnalysis) => {
    const { score, issues } = analysis;

    // Perfect posture (5 consecutive)
    if (score >= 95) {
      const recentCorrelations = synchronizerRef.current.getRecentCorrelations(5);
      if (recentCorrelations.every(c => c.postureScore >= 95)) {
        onAchievement?.('perfect_posture_streak');
      }
    }

    // No critical issues (hyperextension) for 50 notes
    if (!issues.some(i => i.severity === 'critical')) {
      const stats = synchronizerRef.current.getStats();
      if (stats.successfulCorrelations >= 50) {
        onAchievement?.('injury_prevention_master');
      }
    }

    // Consistent good posture (80+ for 20 notes)
    if (score >= 80) {
      const recentCorrelations = synchronizerRef.current.getRecentCorrelations(20);
      const average =
        recentCorrelations.reduce((sum, c) => sum + c.postureScore, 0) / recentCorrelations.length;

      if (average >= 80 && recentCorrelations.length === 20) {
        onAchievement?.('posture_consistency');
      }
    }
  };

  /**
   * Get detailed statistics
   */
  const getStatistics = useCallback(() => {
    return synchronizerRef.current.getStats();
  }, []);

  /**
   * Get correlation accuracy for time range
   */
  const getAccuracyRange = useCallback((startTime: number, endTime: number) => {
    const correlations = synchronizerRef.current.getCorrelationsInRange(startTime, endTime);
    if (correlations.length === 0) return 0;

    const correct = correlations.filter(c => c.wasCorrect).length;
    return (correct / correlations.length) * 100;
  }, []);

  /**
   * Calibrate latency offset (run after ~30s of playing)
   */
  const calibrateLatency = useCallback(() => {
    const newOffset = synchronizerRef.current.calibrateLatency();
    return newOffset;
  }, []);

  /**
   * Reset session
   */
  const reset = useCallback(() => {
    synchronizerRef.current.reset();
    HandPostureAnalyzerV2.resetFilters();
    setState({
      currentAnalysis: null,
      accuracy: 0,
      totalCorrelations: 0,
      averagePostureScore: 0,
      bonusXPEarned: 0,
    });
  }, []);

  return {
    // Core functions
    processPose,
    processMIDIEvent,

    // State
    ...state,

    // Utilities
    getStatistics,
    getAccuracyRange,
    calibrateLatency,
    reset,

    // Direct access (for advanced use)
    synchronizer: synchronizerRef.current,
  };
}
