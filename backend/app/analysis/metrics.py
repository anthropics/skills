import numpy as np
from typing import List, Dict, Any, Tuple
import mir_eval
import librosa

class PerformanceMetrics:
    """
    Comprehensive performance evaluation using mir_eval and pitch detection
    """

    def __init__(self, score_notes: List[Dict], performance_notes: List[Dict]):
        self.score_notes = score_notes
        self.performance_notes = performance_notes

    def compute_onset_metrics(self, alignment: List[Dict]) -> Dict[str, float]:
        """Compute onset detection metrics (F1, precision, recall)"""
        if not alignment:
            return {'onset_f1': 0.0, 'onset_precision': 0.0, 'onset_recall': 0.0}

        # Extract aligned onsets
        ref_onsets = [align['score_onset'] for align in alignment]
        est_onsets = [align['performance_onset'] for align in alignment]

        if not ref_onsets or not est_onsets:
            return {'onset_f1': 0.0, 'onset_precision': 0.0, 'onset_recall': 0.0}

        # Compute onset metrics with 50ms tolerance
        onset_tolerance = 0.05
        metrics = mir_eval.onset.evaluate(ref_onsets, est_onsets, onset_tolerance)

        return {
            'onset_f1': metrics['F-measure'],
            'onset_precision': metrics['Precision'],
            'onset_recall': metrics['Recall'],
            'onset_accuracy': self._compute_onset_accuracy(alignment)
        }

    def _compute_onset_accuracy(self, alignment: List[Dict]) -> float:
        """Compute timing accuracy of onsets"""
        if not alignment:
            return 0.0

        deviations = [abs(align['time_deviation']) for align in alignment]
        avg_deviation = np.mean(deviations) if deviations else 0.0

        # Convert to accuracy score (0-1, higher is better)
        max_tolerance = 0.2  # 200ms
        accuracy = max(0, 1 - (avg_deviation / max_tolerance))
        return accuracy

    def compute_pitch_metrics(self, alignment: List[Dict]) -> Dict[str, float]:
        """Compute pitch accuracy metrics"""
        if not alignment:
            return {'pitch_accuracy': 0.0, 'pitch_precision': 0.0, 'intonation_deviation': 0.0}

        correct_pitches = 0
        total_notes = 0
        pitch_deviations = []

        for align in alignment:
            perf_notes = [n for n in self.performance_notes
                         if abs(n['onset'] - align['performance_onset']) < 0.01]
            score_notes = [n for n in self.score_notes
                          if abs(n['onset'] - align['score_onset']) < 0.01]

            if perf_notes and score_notes:
                perf_pitches = set(n['pitch'] for n in perf_notes)
                score_pitches = set(n['pitch'] for n in score_notes)

                # Check for correct pitches
                if perf_pitches.intersection(score_pitches):
                    correct_pitches += 1

                # Calculate pitch deviation for closest notes
                closest_perf = min(perf_pitches, key=lambda p: min(abs(p - s) for s in score_pitches))
                closest_score = min(score_pitches, key=lambda s: abs(s - closest_perf))
                deviation = closest_perf - closest_score
                pitch_deviations.append(deviation)

                total_notes += 1

        if total_notes == 0:
            return {'pitch_accuracy': 0.0, 'pitch_precision': 0.0, 'intonation_deviation': 0.0}

        accuracy = correct_pitches / total_notes
        avg_deviation = np.mean(np.abs(pitch_deviations)) if pitch_deviations else 0.0

        return {
            'pitch_accuracy': accuracy,
            'pitch_precision': accuracy,  # Same as accuracy for simplicity
            'intonation_deviation': avg_deviation
        }

    def compute_rhythm_metrics(self, alignment: List[Dict]) -> Dict[str, float]:
        """Compute rhythm and timing metrics"""
        if len(alignment) < 2:
            return {'tempo_accuracy': 0.0, 'rhythmic_precision': 0.0, 'timing_consistency': 0.0}

        # Calculate inter-onset intervals (IOI)
        score_ioi = np.diff([align['score_onset'] for align in alignment])
        perf_ioi = np.diff([align['performance_onset'] for align in alignment])

        if len(score_ioi) != len(perf_ioi) or len(score_ioi) == 0:
            return {'tempo_accuracy': 0.0, 'rhythmic_precision': 0.0, 'timing_consistency': 0.0}

        # Tempo accuracy (ratio of performance IOI to score IOI)
        tempo_ratios = perf_ioi / (score_ioi + 1e-10)  # Add small epsilon to avoid division by zero
        tempo_accuracy = max(0, 1 - np.std(tempo_ratios))  # Lower std = more consistent tempo

        # Rhythmic precision (correlation between IOIs)
        if len(score_ioi) > 1:
            rhythmic_correlation = np.corrcoef(score_ioi, perf_ioi)[0, 1]
            rhythmic_precision = max(0, rhythmic_correlation)  # 0-1 range
        else:
            rhythmic_precision = 0.0

        # Timing consistency (std of timing deviations)
        timing_deviations = [align['time_deviation'] for align in alignment]
        timing_consistency = 1 - min(1, np.std(np.abs(timing_deviations)) / 0.5)  # Normalized

        return {
            'tempo_accuracy': float(tempo_accuracy),
            'rhythmic_precision': float(rhythmic_precision),
            'timing_consistency': float(timing_consistency)
        }

    def compute_expressivity_metrics(self) -> Dict[str, float]:
        """Compute dynamics and expressivity metrics"""
        if not self.performance_notes:
            return {'dynamic_range': 0.0, 'articulation_variety': 0.0, 'phrasing_consistency': 0.0}

        velocities = [note.get('velocity', 64) for note in self.performance_notes]

        if not velocities:
            return {'dynamic_range': 0.0, 'articulation_variety': 0.0, 'phrasing_consistency': 0.0}

        # Dynamic range (normalized 0-1)
        dynamic_range = (max(velocities) - min(velocities)) / 127.0

        # Articulation variety (std of note durations)
        durations = [note.get('duration', 0.5) for note in self.performance_notes]
        if durations:
            articulation_variety = min(1, np.std(durations) / 2.0)  # Normalized
        else:
            articulation_variety = 0.0

        # Phrasing consistency (grouping of notes)
        onsets = [note['onset'] for note in self.performance_notes]
        if len(onsets) > 1:
            gaps = np.diff(sorted(onsets))
            phrasing_consistency = 1 - min(1, np.std(gaps) / 1.0)  # Normalized
        else:
            phrasing_consistency = 0.0

        return {
            'dynamic_range': float(dynamic_range),
            'articulation_variety': float(articulation_variety),
            'phrasing_consistency': float(phrasing_consistency)
        }

    def compute_overall_assessment(self, alignment: List[Dict]) -> Dict[str, Any]:
        """Compute comprehensive performance assessment"""
        onset_metrics = self.compute_onset_metrics(alignment)
        pitch_metrics = self.compute_pitch_metrics(alignment)
        rhythm_metrics = self.compute_rhythm_metrics(alignment)
        expressivity_metrics = self.compute_expressivity_metrics()

        # Weighted overall score
        weights = {
            'onset': 0.3,
            'pitch': 0.3,
            'rhythm': 0.25,
            'expressivity': 0.15
        }

        overall_score = (
            onset_metrics['onset_f1'] * weights['onset'] +
            pitch_metrics['pitch_accuracy'] * weights['pitch'] +
            rhythm_metrics['tempo_accuracy'] * weights['rhythm'] +
            expressivity_metrics['dynamic_range'] * weights['expressivity']
        )

        # Performance level assessment
        if overall_score >= 0.9:
            level = "Expert"
        elif overall_score >= 0.7:
            level = "Advanced"
        elif overall_score >= 0.5:
            level = "Intermediate"
        else:
            level = "Beginner"

        return {
            'overall_score': float(overall_score),
            'performance_level': level,
            'onset_metrics': onset_metrics,
            'pitch_metrics': pitch_metrics,
            'rhythm_metrics': rhythm_metrics,
            'expressivity_metrics': expressivity_metrics,
            'note_count': {
                'score_notes': len(self.score_notes),
                'performance_notes': len(self.performance_notes),
                'aligned_notes': len(alignment)
            }
        }
