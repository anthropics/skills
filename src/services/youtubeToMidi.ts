/**
 * YouTube to MIDI Conversion Service
 *
 * This service handles the conversion of YouTube videos to MIDI files.
 *
 * CURRENT STATE: Placeholder implementation with demo functionality
 * PRODUCTION: Will require backend API integration with:
 *   - Audio extraction from YouTube
 *   - AI-based pitch detection (e.g., using Spotify's Basic Pitch model)
 *   - MIDI file generation
 */

export interface ConversionOptions {
  videoId: string;
  videoUrl: string;
  startTime?: number;
  endTime?: number;
  trackInstrument?: 'piano' | 'guitar' | 'auto';
}

export interface ConversionResult {
  success: boolean;
  midiData?: ArrayBuffer;
  midiUrl?: string;
  metadata?: {
    title: string;
    duration: number;
    noteCount: number;
    difficulty: 'easy' | 'medium' | 'hard';
    averageTempo: number;
  };
  error?: string;
}

export interface ConversionProgress {
  stage: 'downloading' | 'analyzing' | 'converting' | 'complete' | 'error';
  progress: number; // 0-100
  message: string;
}

class YouTubeToMidiService {
  // Reserved for future backend API integration
  // private apiEndpoint: string;

  constructor() {
    // In production, this would be your backend API
    // this.apiEndpoint = import.meta.env.VITE_API_URL || 'http://localhost:3000/api';
  }

  /**
   * Convert YouTube video to MIDI
   *
   * @param options - Conversion options
   * @param onProgress - Progress callback
   * @returns Conversion result
   */
  async convertVideo(
    options: ConversionOptions,
    onProgress?: (progress: ConversionProgress) => void
  ): Promise<ConversionResult> {
    try {
      // Stage 1: Downloading
      onProgress?.({
        stage: 'downloading',
        progress: 10,
        message: 'Baixando áudio do YouTube...',
      });

      // Stage 2: Analyzing
      await this.delay(1000);
      onProgress?.({
        stage: 'analyzing',
        progress: 40,
        message: 'Analisando notas com IA...',
      });

      // Stage 3: Converting
      await this.delay(1500);
      onProgress?.({
        stage: 'converting',
        progress: 70,
        message: 'Gerando arquivo MIDI...',
      });

      // TODO: Replace with actual API call
      // const result = await this.callConversionAPI(options);

      // For now, use demo MIDI file
      const result = await this.getDemoMidi(options.videoId);

      // Stage 4: Complete
      onProgress?.({
        stage: 'complete',
        progress: 100,
        message: 'Conversão concluída!',
      });

      return result;
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : 'Erro desconhecido';

      onProgress?.({
        stage: 'error',
        progress: 0,
        message: `Erro: ${errorMessage}`,
      });

      return {
        success: false,
        error: errorMessage,
      };
    }
  }

  /**
   * Call the conversion API (placeholder)
   * TODO: Implement when backend API is ready
   *
   * @private - Reserved for future backend integration
   *
   * Example usage:
   * const result = await this.callConversionAPI(options);
   */
  /*
  private async callConversionAPI(options: ConversionOptions): Promise<ConversionResult> {
    const response = await fetch(`${this.apiEndpoint}/convert`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(options),
    });

    if (!response.ok) {
      throw new Error(`API Error: ${response.statusText}`);
    }

    const data = await response.json();
    return data;
  }
  */

  /**
   * Get a demo MIDI file for testing
   * This simulates the conversion process using sample MIDI files
   */
  private async getDemoMidi(videoId: string): Promise<ConversionResult> {
    // In a real implementation, you would have various demo MIDI files
    // For now, we'll return metadata for a simulated conversion

    return {
      success: true,
      metadata: {
        title: 'YouTube Video MIDI Conversion',
        duration: 180, // 3 minutes
        noteCount: 450,
        difficulty: this.calculateDifficulty(videoId),
        averageTempo: 120,
      },
      // Note: midiUrl or midiData would be provided by the actual backend
      midiUrl: undefined, // To be implemented with real conversion
    };
  }

  /**
   * Calculate difficulty based on video characteristics
   * This is a placeholder - real difficulty would be based on note analysis
   */
  private calculateDifficulty(videoId: string): 'easy' | 'medium' | 'hard' {
    // Simple hash-based assignment for demo purposes
    const hash = videoId.split('').reduce((acc, char) => acc + char.charCodeAt(0), 0);
    const mod = hash % 3;

    if (mod === 0) return 'easy';
    if (mod === 1) return 'medium';
    return 'hard';
  }

  /**
   * Utility: delay execution
   */
  private delay(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  /**
   * Validate YouTube URL
   */
  static validateYouTubeUrl(url: string): boolean {
    const patterns = [
      /(?:youtube\.com\/watch\?v=|youtu\.be\/|youtube\.com\/embed\/)([^&\n?#]+)/,
      /^([a-zA-Z0-9_-]{11})$/,
    ];

    return patterns.some(pattern => pattern.test(url));
  }

  /**
   * Extract video ID from YouTube URL
   */
  static extractVideoId(url: string): string | null {
    const patterns = [
      /(?:youtube\.com\/watch\?v=|youtu\.be\/|youtube\.com\/embed\/)([^&\n?#]+)/,
      /^([a-zA-Z0-9_-]{11})$/,
    ];

    for (const pattern of patterns) {
      const match = url.match(pattern);
      if (match && match[1]) {
        return match[1];
      }
    }

    return null;
  }
}

// Export singleton instance
export const youtubeToMidiService = new YouTubeToMidiService();

// Export class for testing
export default YouTubeToMidiService;
