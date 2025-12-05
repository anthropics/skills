import React, { useState, useEffect, useRef } from 'react';
import MidiPlayer from '../Player/MidiPlayer';
import './PracticeMode.css';

interface Note {
  name: string;
  midi: number;
  time: number;
  duration: number;
  velocity: number;
}

interface PracticeModeProps {
  midiUrl?: string;
  midiData?: ArrayBuffer;
  onScoreChange?: (score: number) => void;
  expectedNotes?: Note[];
}

interface NoteEvent {
  note: string;
  time: number;
  correct: boolean;
}

const PracticeMode: React.FC<PracticeModeProps> = ({
  midiUrl,
  midiData,
  onScoreChange,
  expectedNotes = [],
}) => {
  const [isActive, setIsActive] = useState(false);
  const [currentNote, setCurrentNote] = useState<string | null>(null);
  const [playedNotes, setPlayedNotes] = useState<NoteEvent[]>([]);
  const [score, setScore] = useState({ correct: 0, incorrect: 0, missed: 0 });
  const [feedback, setFeedback] = useState<string>('');
  const [combo, setCombo] = useState(0);
  const [maxCombo, setMaxCombo] = useState(0);

  const expectedNotesRef = useRef<Note[]>(expectedNotes);
  const currentNoteIndex = useRef(0);

  useEffect(() => {
    expectedNotesRef.current = expectedNotes;
  }, [expectedNotes]);

  useEffect(() => {
    // Setup MIDI input listener
    if (isActive && typeof navigator.requestMIDIAccess !== 'undefined') {
      setupMidiInput();
    }
  }, [isActive]);

  const setupMidiInput = async () => {
    try {
      const midiAccess = await navigator.requestMIDIAccess();
      const inputs = midiAccess.inputs.values();

      for (const input of inputs) {
        input.onmidimessage = handleMidiMessage;
      }
    } catch (error) {
      console.error('MIDI access error:', error);
    }
  };

  const handleMidiMessage = (message: any) => {
    const [command, note, velocity] = message.data;

    // Note On message
    if (command === 144 && velocity > 0) {
      const noteName = midiNoteToName(note);
      handleNotePlay(noteName, velocity);
    }
  };

  const midiNoteToName = (midi: number): string => {
    const notes = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];
    const octave = Math.floor(midi / 12) - 1;
    const note = notes[midi % 12];
    return `${note}${octave}`;
  };

  const handleNotePlay = (note: string, _velocity: number) => {
    if (!isActive) return;

    const expectedNote = expectedNotesRef.current[currentNoteIndex.current];
    const isCorrect = expectedNote && note === expectedNote.name;

    const noteEvent: NoteEvent = {
      note,
      time: Date.now(),
      correct: isCorrect,
    };

    setPlayedNotes(prev => [...prev, noteEvent]);
    setCurrentNote(note);

    if (isCorrect) {
      // Correct note
      setScore(prev => ({
        ...prev,
        correct: prev.correct + 1,
      }));
      setCombo(prev => {
        const newCombo = prev + 1;
        setMaxCombo(current => Math.max(current, newCombo));
        return newCombo;
      });
      setFeedback('✓ Correto!');
      currentNoteIndex.current++;
    } else {
      // Incorrect note
      setScore(prev => ({
        ...prev,
        incorrect: prev.incorrect + 1,
      }));
      setCombo(0);
      setFeedback('✗ Incorreto');
    }

    // Clear feedback after delay
    setTimeout(() => setFeedback(''), 1000);

    // Update parent
    const totalNotes = score.correct + score.incorrect + 1;
    const accuracy = ((score.correct + (isCorrect ? 1 : 0)) / totalNotes) * 100;
    onScoreChange?.(accuracy);
  };

  const handlePlayerNotePlay = (note: string, _velocity: number) => {
    // Visual feedback for player notes
    setCurrentNote(note);
    setTimeout(() => setCurrentNote(null), 100);
  };

  const startPractice = () => {
    setIsActive(true);
    setPlayedNotes([]);
    setScore({ correct: 0, incorrect: 0, missed: 0 });
    setCombo(0);
    setMaxCombo(0);
    currentNoteIndex.current = 0;
  };

  const stopPractice = () => {
    setIsActive(false);
  };

  const resetPractice = () => {
    stopPractice();
    setPlayedNotes([]);
    setScore({ correct: 0, incorrect: 0, missed: 0 });
    setCombo(0);
    setMaxCombo(0);
    currentNoteIndex.current = 0;
    setFeedback('');
  };

  const getAccuracy = () => {
    const total = score.correct + score.incorrect;
    if (total === 0) return '0';
    return ((score.correct / total) * 100).toFixed(1);
  };

  const getGrade = () => {
    const accuracy = parseFloat(getAccuracy());
    if (accuracy >= 95) return { grade: 'S', color: '#fbbf24' };
    if (accuracy >= 85) return { grade: 'A', color: '#10b981' };
    if (accuracy >= 75) return { grade: 'B', color: '#3b82f6' };
    if (accuracy >= 65) return { grade: 'C', color: '#6b7280' };
    return { grade: 'D', color: '#ef4444' };
  };

  return (
    <div className="practice-mode">
      <div className="practice-header">
        <h2>🎯 Modo Prática</h2>
        <div className="practice-actions">
          <button
            onClick={isActive ? stopPractice : startPractice}
            className={`practice-btn ${isActive ? 'active' : ''}`}
          >
            {isActive ? '⏸️ Pausar' : '▶️ Iniciar Prática'}
          </button>
          <button onClick={resetPractice} className="reset-btn">
            🔄 Reiniciar
          </button>
        </div>
      </div>

      {/* Real-time Feedback */}
      <div className="feedback-section">
        <div className={`current-note ${currentNote ? 'active' : ''}`}>{currentNote || '—'}</div>
        {feedback && (
          <div className={`feedback-message ${feedback.includes('✓') ? 'correct' : 'incorrect'}`}>
            {feedback}
          </div>
        )}
      </div>

      {/* Score Display */}
      <div className="score-display">
        <div className="score-card">
          <div className="score-label">Corretas</div>
          <div className="score-value correct">{score.correct}</div>
        </div>
        <div className="score-card">
          <div className="score-label">Incorretas</div>
          <div className="score-value incorrect">{score.incorrect}</div>
        </div>
        <div className="score-card">
          <div className="score-label">Precisão</div>
          <div className="score-value accuracy">{getAccuracy()}%</div>
        </div>
        <div className="score-card">
          <div className="score-label">Combo</div>
          <div className="score-value combo">{combo} 🔥</div>
        </div>
      </div>

      {/* Grade Display */}
      {score.correct + score.incorrect > 0 && (
        <div className="grade-display">
          <div className="grade-badge" style={{ backgroundColor: getGrade().color }}>
            {getGrade().grade}
          </div>
          <div className="grade-info">
            <p>Máximo Combo: {maxCombo}</p>
            <p>Total de Notas: {score.correct + score.incorrect}</p>
          </div>
        </div>
      )}

      {/* MIDI Player */}
      <MidiPlayer
        midiUrl={midiUrl}
        midiData={midiData}
        onNotePlay={handlePlayerNotePlay}
        autoPlay={false}
      />

      {/* Recent Notes */}
      <div className="recent-notes">
        <h4>Últimas Notas Tocadas</h4>
        <div className="notes-list">
          {playedNotes
            .slice(-10)
            .reverse()
            .map((noteEvent, index) => (
              <div
                key={index}
                className={`note-item ${noteEvent.correct ? 'correct' : 'incorrect'}`}
              >
                <span className="note-name">{noteEvent.note}</span>
                <span className="note-status">{noteEvent.correct ? '✓' : '✗'}</span>
              </div>
            ))}
        </div>
      </div>

      {/* Instructions */}
      {!isActive && (
        <div className="instructions">
          <h4>📋 Instruções</h4>
          <ol>
            <li>Conecte seu teclado MIDI ou use o teclado virtual</li>
            <li>Clique em "Iniciar Prática" para começar</li>
            <li>Toque as notas indicadas na partitura</li>
            <li>Receba feedback instantâneo sobre sua performance</li>
            <li>Tente alcançar a maior precisão possível!</li>
          </ol>
        </div>
      )}
    </div>
  );
};

export default PracticeMode;
