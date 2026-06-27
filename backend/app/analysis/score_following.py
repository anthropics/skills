import numpy as np
import partitura as pt
from typing import List, Dict, Any, Tuple
import librosa
from scipy.spatial.distance import cdist
from dtaidistance import dtw

class ScoreFollower:
    """
    Real-time score following using dynamic time warping and musical feature matching
    """

    def __init__(self, score_midi_path: str = None, score_notes: List[Dict] = None):
        if score_midi_path:
            self.score_notes = self._load_score_notes(score_midi_path)
        elif score_notes:
            self.score_notes = score_notes
        else:
            raise ValueError("Either score_midi_path or score_notes must be provided")

        self.current_position = 0
        self.alignment_path = []
        self._extract_score_features()

    def _load_score_notes(self, midi_path: str) -> List[Dict]:
        """Load MIDI score and extract note information"""
        try:
            midi_data = pt.load_midi(midi_path)
            notes = []

            for note in midi_data.notes:
                notes.append({
                    'onset': note.start,
                    'duration': note.duration,
                    'pitch': note.midi_pitch,
                    'velocity': note.velocity,
                    'measure': getattr(note, 'measure', 0),
                    'staff': getattr(note, 'staff', 0)
                })

            return sorted(notes, key=lambda x: x['onset'])
        except Exception as e:
            print(f"Error loading MIDI score: {e}")
            return []

    def _extract_score_features(self):
        """Extract musical features from score for matching"""
        # Create onset-based feature matrix
        onsets = sorted(list(set([note['onset'] for note in self.score_notes])))
        self.score_onsets = onsets

        # Create pitch histogram for each onset
        self.score_features = []
        for onset in onsets:
            pitches = [note['pitch'] for note in self.score_notes
                      if abs(note['onset'] - onset) < 0.01]  # Small tolerance
            if pitches:
                # Create pitch class vector (chroma-like)
                pitch_class = np.zeros(12)
                for pitch in pitches:
                    pitch_class[pitch % 12] += 1
                self.score_features.append(pitch_class)
            else:
                self.score_features.append(np.zeros(12))

        self.score_features = np.array(self.score_features)

    def align_performance(self, performance_notes: List[Dict]) -> Dict[str, Any]:
        """
        Align performance notes with score using DTW on pitch features

        Args:
            performance_notes: List of performance note events

        Returns:
            Alignment results with timing information
        """
        if not performance_notes:
            return {'success': False, 'error': 'No performance notes provided'}

        # Extract performance features
        perf_onsets = sorted(list(set([note['onset'] for note in performance_notes])))
        perf_features = []

        for onset in perf_onsets:
            pitches = [note['pitch'] for note in performance_notes
                      if abs(note['onset'] - onset) < 0.01]
            if pitches:
                pitch_class = np.zeros(12)
                for pitch in pitches:
                    pitch_class[pitch % 12] += 1
                perf_features.append(pitch_class)
            else:
                perf_features.append(np.zeros(12))

        perf_features = np.array(perf_features)

        # Compute DTW alignment
        try:
            distance = dtw.distance(perf_features, self.score_features)
            path = dtw.warping_path(perf_features, self.score_features)

            # Convert path to alignment mapping
            alignment = []
            for perf_idx, score_idx in path:
                if perf_idx < len(perf_onsets) and score_idx < len(self.score_onsets):
                    alignment.append({
                        'performance_onset': perf_onsets[perf_idx],
                        'score_onset': self.score_onsets[score_idx],
                        'time_deviation': perf_onsets[perf_idx] - self.score_onsets[score_idx]
                    })

            return {
                'success': True,
                'alignment': alignment,
                'dtw_distance': distance,
                'performance_onsets': perf_onsets,
                'score_onsets': self.score_onsets
            }

        except Exception as e:
            return {'success': False, 'error': f'DTW alignment failed: {str(e)}'}

    def update_real_time(self, current_notes: List[Dict], window_size: int = 10) -> Dict[str, Any]:
        """
        Real-time score following update

        Args:
            current_notes: Recent performance notes
            window_size: Number of recent notes to consider

        Returns:
            Current score position and confidence
        """
        if not current_notes:
            return {'position': self.current_position, 'confidence': 0.0}

        # Use recent notes for alignment
        recent_notes = sorted(current_notes[-window_size:], key=lambda x: x['onset'])

        # Simple onset-based matching
        if recent_notes:
            current_perf_onset = recent_notes[-1]['onset']

            # Find closest score onset
            score_onsets = [note['onset'] for note in self.score_notes]
            closest_idx = np.argmin(np.abs(np.array(score_onsets) - current_perf_onset))
            closest_onset = score_onsets[closest_idx]

            # Calculate confidence based on pitch matching
            current_pitches = set(note['pitch'] for note in recent_notes)
            expected_pitches = set(note['pitch'] for note in self.score_notes
                                 if abs(note['onset'] - closest_onset) < 0.1)

            if expected_pitches:
                pitch_overlap = len(current_pitches.intersection(expected_pitches))
                confidence = pitch_overlap / len(expected_pitches)
            else:
                confidence = 0.0

            self.current_position = closest_onset

            return {
                'position': closest_onset,
                'confidence': confidence,
                'measure': self._get_measure_at_time(closest_onset),
                'expected_notes': list(expected_pitches),
                'played_notes': list(current_pitches),
                'timing_deviation': 0.0  # Added for compatibility
            }

        return {'position': self.current_position, 'confidence': 0.0}

    def _get_measure_at_time(self, time: float) -> int:
        """Get measure number at given time"""
        # Simple implementation - in practice, you'd use measure information from score
        measures = sorted(list(set(note.get('measure', 0) for note in self.score_notes)))
        return measures[0] if measures else 0
