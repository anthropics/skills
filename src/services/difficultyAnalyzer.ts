/**
 * Difficulty Analyzer with Color Coding System
 *
 * Analyzes MIDI data to determine difficulty levels and assign colors
 * to notes based on various musical complexity factors.
 */

import { Midi } from '@tonejs/midi';

export type DifficultyLevel = 'easy' | 'medium' | 'hard';

export interface NoteColor {
  color: string;
  backgroundColor: string;
  borderColor: string;
  label: string;
}

export interface NoteDifficulty {
  note: string;
  time: number;
  duration: number;
  difficulty: DifficultyLevel;
  color: NoteColor;
  factors: {
    speed: number; // Notes per second around this note
    interval: number; // Distance from previous note
    handSpan: number; // Required hand span
    complexity: number; // Overall complexity score (0-100)
  };
}

export interface DifficultyAnalysis {
  overallDifficulty: DifficultyLevel;
  difficultyScore: number; // 0-100
  notesDifficulty: NoteDifficulty[];
  statistics: {
    totalNotes: number;
    easyNotes: number;
    mediumNotes: number;
    hardNotes: number;
    averageTempo: number;
    maxNotesPerSecond: number;
    averageInterval: number;
  };
}

export class DifficultyAnalyzer {
  // Color schemes for different difficulty levels
  private static readonly COLOR_SCHEME: Record<DifficultyLevel, NoteColor> = {
    easy: {
      color: '#10b981', // Green text
      backgroundColor: '#d1fae5', // Light green background
      borderColor: '#059669', // Dark green border
      label: 'Fácil',
    },
    medium: {
      color: '#f59e0b', // Amber text
      backgroundColor: '#fef3c7', // Light amber background
      borderColor: '#d97706', // Dark amber border
      label: 'Médio',
    },
    hard: {
      color: '#ef4444', // Red text
      backgroundColor: '#fee2e2', // Light red background
      borderColor: '#dc2626', // Dark red border
      label: 'Difícil',
    },
  };

  /**
   * Analyze MIDI data for difficulty
   */
  static analyzeMidi(midi: Midi): DifficultyAnalysis {
    const allNotes = this.extractAllNotes(midi);
    const notesDifficulty = this.analyzeNotes(allNotes);
    const statistics = this.calculateStatistics(notesDifficulty);
    const overallDifficulty = this.determineOverallDifficulty(statistics);

    return {
      overallDifficulty,
      difficultyScore: statistics.difficultyScore,
      notesDifficulty,
      statistics: {
        totalNotes: statistics.totalNotes,
        easyNotes: statistics.easyNotes,
        mediumNotes: statistics.mediumNotes,
        hardNotes: statistics.hardNotes,
        averageTempo: statistics.averageTempo,
        maxNotesPerSecond: statistics.maxNotesPerSecond,
        averageInterval: statistics.averageInterval,
      },
    };
  }

  /**
   * Extract all notes from MIDI tracks
   */
  private static extractAllNotes(midi: Midi) {
    const notes: Array<{ name: string; time: number; duration: number; midi: number }> = [];

    midi.tracks.forEach(track => {
      track.notes.forEach(note => {
        notes.push({
          name: note.name,
          time: note.time,
          duration: note.duration,
          midi: note.midi,
        });
      });
    });

    // Sort by time
    return notes.sort((a, b) => a.time - b.time);
  }

  /**
   * Analyze individual notes for difficulty
   */
  private static analyzeNotes(
    notes: Array<{ name: string; time: number; duration: number; midi: number }>
  ): NoteDifficulty[] {
    return notes.map((note, index) => {
      const speed = this.calculateSpeed(notes, index);
      const interval = this.calculateInterval(notes, index);
      const handSpan = this.calculateHandSpan(notes, index);
      const complexity = this.calculateComplexity(speed, interval, handSpan);
      const difficulty = this.assignDifficulty(complexity);

      return {
        note: note.name,
        time: note.time,
        duration: note.duration,
        difficulty,
        color: this.COLOR_SCHEME[difficulty],
        factors: {
          speed,
          interval,
          handSpan,
          complexity,
        },
      };
    });
  }

  /**
   * Calculate note speed (notes per second in a 1-second window)
   */
  private static calculateSpeed(notes: Array<{ time: number }>, currentIndex: number): number {
    const currentTime = notes[currentIndex].time;
    const windowStart = currentTime - 0.5;
    const windowEnd = currentTime + 0.5;

    const notesInWindow = notes.filter(note => note.time >= windowStart && note.time <= windowEnd);

    return notesInWindow.length;
  }

  /**
   * Calculate interval from previous note (in semitones)
   */
  private static calculateInterval(notes: Array<{ midi: number }>, currentIndex: number): number {
    if (currentIndex === 0) return 0;

    const current = notes[currentIndex].midi;
    const previous = notes[currentIndex - 1].midi;

    return Math.abs(current - previous);
  }

  /**
   * Calculate required hand span (distance between simultaneous notes)
   */
  private static calculateHandSpan(
    notes: Array<{ time: number; midi: number }>,
    currentIndex: number
  ): number {
    const currentTime = notes[currentIndex].time;
    const currentMidi = notes[currentIndex].midi;
    const threshold = 0.1; // Notes within 100ms are considered simultaneous

    const simultaneousNotes = notes.filter(
      (note, idx) => idx !== currentIndex && Math.abs(note.time - currentTime) < threshold
    );

    if (simultaneousNotes.length === 0) return 0;

    const allMidiNotes = [currentMidi, ...simultaneousNotes.map(n => n.midi)];
    return Math.max(...allMidiNotes) - Math.min(...allMidiNotes);
  }

  /**
   * Calculate overall complexity score (0-100)
   */
  private static calculateComplexity(speed: number, interval: number, handSpan: number): number {
    // Weighted factors:
    // - Speed: 40% (high speed = harder)
    // - Interval: 30% (large jumps = harder)
    // - Hand span: 30% (wide chords = harder)

    const speedScore = Math.min((speed / 8) * 100, 100); // 8+ notes/sec = max difficulty
    const intervalScore = Math.min((interval / 12) * 100, 100); // Octave+ jump = max difficulty
    const handSpanScore = Math.min((handSpan / 24) * 100, 100); // 2 octaves = max difficulty

    return speedScore * 0.4 + intervalScore * 0.3 + handSpanScore * 0.3;
  }

  /**
   * Assign difficulty level based on complexity score
   */
  private static assignDifficulty(complexity: number): DifficultyLevel {
    if (complexity < 33) return 'easy';
    if (complexity < 66) return 'medium';
    return 'hard';
  }

  /**
   * Calculate statistics from analyzed notes
   */
  private static calculateStatistics(notesDifficulty: NoteDifficulty[]) {
    const totalNotes = notesDifficulty.length;
    const easyNotes = notesDifficulty.filter(n => n.difficulty === 'easy').length;
    const mediumNotes = notesDifficulty.filter(n => n.difficulty === 'medium').length;
    const hardNotes = notesDifficulty.filter(n => n.difficulty === 'hard').length;

    const averageTempo =
      notesDifficulty.reduce((sum, n) => sum + n.factors.speed, 0) / totalNotes || 0;

    const maxNotesPerSecond = Math.max(...notesDifficulty.map(n => n.factors.speed));

    const averageInterval =
      notesDifficulty.reduce((sum, n) => sum + n.factors.interval, 0) / totalNotes || 0;

    const difficultyScore =
      notesDifficulty.reduce((sum, n) => sum + n.factors.complexity, 0) / totalNotes || 0;

    return {
      totalNotes,
      easyNotes,
      mediumNotes,
      hardNotes,
      averageTempo,
      maxNotesPerSecond,
      averageInterval,
      difficultyScore,
    };
  }

  /**
   * Determine overall difficulty based on statistics
   */
  private static determineOverallDifficulty(statistics: {
    difficultyScore: number;
  }): DifficultyLevel {
    if (statistics.difficultyScore < 33) return 'easy';
    if (statistics.difficultyScore < 66) return 'medium';
    return 'hard';
  }

  /**
   * Get color for difficulty level
   */
  static getColor(difficulty: DifficultyLevel): NoteColor {
    return this.COLOR_SCHEME[difficulty];
  }

  /**
   * Get difficulty label with emoji
   */
  static getDifficultyLabel(difficulty: DifficultyLevel): string {
    const emojis = {
      easy: '🟢',
      medium: '🟡',
      hard: '🔴',
    };

    return `${emojis[difficulty]} ${this.COLOR_SCHEME[difficulty].label}`;
  }
}

export default DifficultyAnalyzer;
