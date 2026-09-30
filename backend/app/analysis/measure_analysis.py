import numpy as np
from typing import List, Dict, Any, Tuple
from collections import defaultdict

class MeasureAnalyzer:
    """
    Analyze performance at the measure level for detailed feedback
    """

    def __init__(self, score_notes: List[Dict]):
        self.score_notes = score_notes
        self._group_notes_by_measure()

    def _group_notes_by_measure(self):
        """Group score notes by measure for analysis"""
        self.measure_notes = defaultdict(list)

        for note in self.score_notes:
            measure = note.get('measure', 0)
            self.measure_notes[measure].append(note)

    def analyze_measure_performance(self, performance_notes: List[Dict],
                                  alignment: List[Dict]) -> Dict[int, Dict[str, Any]]:
        """Analyze performance for each measure"""
        measure_results = {}

        for measure, score_notes in self.measure_notes.items():
            # Find performance notes in this measure
            measure_perf_notes = self._get_notes_in_measure(performance_notes, measure, alignment)
            measure_alignment = [align for align in alignment
                               if any(abs(align['score_onset'] - note['onset']) < 0.01
                                     for note in score_notes)]

            # Compute measure-specific metrics
            metrics = self._compute_measure_metrics(score_notes, measure_perf_notes, measure_alignment)
            measure_results[measure] = metrics

        return measure_results

    def _get_notes_in_measure(self, performance_notes: List[Dict], measure: int,
                            alignment: List[Dict]) -> List[Dict]:
        """Get performance notes that align with notes in the specified measure"""
        measure_score_notes = self.measure_notes[measure]
        measure_score_onsets = [note['onset'] for note in measure_score_notes]

        aligned_perf_notes = []
        for align in alignment:
            if align['score_onset'] in measure_score_onsets:
                perf_note = next((n for n in performance_notes
                                if abs(n['onset'] - align['performance_onset']) < 0.01), None)
                if perf_note:
                    aligned_perf_notes.append(perf_note)

        return aligned_perf_notes

    def _compute_measure_metrics(self, score_notes: List[Dict],
                               performance_notes: List[Dict],
                               alignment: List[Dict]) -> Dict[str, Any]:
        """Compute metrics for a specific measure"""
        total_score_notes = len(score_notes)
        total_perf_notes = len(performance_notes)

        if total_score_notes == 0:
            return {
                'accuracy': 0.0,
                'notes_played': 0,
                'notes_expected': 0,
                'timing_deviation': 0.0,
                'pitch_accuracy': 0.0,
                'completeness': 0.0
            }

        # Note accuracy
        note_accuracy = len(alignment) / total_score_notes if total_score_notes > 0 else 0

        # Timing deviation
        if alignment:
            timing_deviation = np.mean([abs(align['time_deviation']) for align in alignment])
        else:
            timing_deviation = 0.0

        # Pitch accuracy
        if alignment:
            correct_pitches = 0
            for align in alignment:
                perf_pitches = [n['pitch'] for n in performance_notes
                              if abs(n['onset'] - align['performance_onset']) < 0.01]
                score_pitches = [n['pitch'] for n in score_notes
                               if abs(n['onset'] - align['score_onset']) < 0.01]

                if set(perf_pitches).intersection(set(score_pitches)):
                    correct_pitches += 1

            pitch_accuracy = correct_pitches / len(alignment) if alignment else 0
        else:
            pitch_accuracy = 0.0

        return {
            'accuracy': float(note_accuracy),
            'notes_played': total_perf_notes,
            'notes_expected': total_score_notes,
            'timing_deviation': float(timing_deviation),
            'pitch_accuracy': float(pitch_accuracy),
            'completeness': float(note_accuracy)  # Same as accuracy for now
        }

    def get_problem_measures(self, measure_results: Dict[int, Dict],
                           threshold: float = 0.7) -> List[Dict[str, Any]]:
        """Identify measures that need improvement"""
        problem_measures = []

        for measure, results in measure_results.items():
            if results['accuracy'] < threshold:
                problem_measures.append({
                    'measure': measure,
                    'accuracy': results['accuracy'],
                    'issues': self._identify_measure_issues(results),
                    'suggestions': self._generate_suggestions(results)
                })

        return sorted(problem_measures, key=lambda x: x['accuracy'])

    def _identify_measure_issues(self, results: Dict[str, Any]) -> List[str]:
        """Identify specific issues in a measure"""
        issues = []

        if results['accuracy'] < 0.5:
            issues.append("Many missing or incorrect notes")
        elif results['accuracy'] < 0.8:
            issues.append("Some notes missing or incorrect")

        if results['timing_deviation'] > 0.1:
            issues.append("Timing inconsistencies")

        if results['pitch_accuracy'] < 0.8:
            issues.append("Pitch inaccuracies")

        if results['notes_played'] < results['notes_expected']:
            issues.append(f"Missing {results['notes_expected'] - results['notes_played']} notes")

        return issues if issues else ["Good overall performance"]

    def _generate_suggestions(self, results: Dict[str, Any]) -> List[str]:
        """Generate practice suggestions for problem measures"""
        suggestions = []

        if results['accuracy'] < 0.7:
            suggestions.append("Practice slowly with metronome")
            suggestions.append("Focus on note accuracy before speed")

        if results['timing_deviation'] > 0.1:
            suggestions.append("Use metronome to improve timing")
            suggestions.append("Count rhythms aloud")

        if results['pitch_accuracy'] < 0.8:
            suggestions.append("Review fingerings")
            suggestions.append("Practice scales and arpeggios in this key")

        if len(suggestions) == 0:
            suggestions.append("Continue practicing for consistency")

        return suggestions
