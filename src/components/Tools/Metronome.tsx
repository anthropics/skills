import React, { useState, useEffect, useRef } from 'react';
import './Tools.css';

interface MetronomeProps {
  initialBpm?: number;
  onBpmChange?: (bpm: number) => void;
}

const Metronome: React.FC<MetronomeProps> = ({ initialBpm = 120, onBpmChange }) => {
  const [isPlaying, setIsPlaying] = useState(false);
  const [bpm, setBpm] = useState(initialBpm);
  const [beat, setBeat] = useState(0);
  const [beatsPerMeasure, setBeatsPerMeasure] = useState(4);

  const audioContextRef = useRef<AudioContext | null>(null);
  const intervalRef = useRef<NodeJS.Timeout | null>(null);
  const startTimeRef = useRef<number>(0);

  const createOscillator = (frequency: number, duration: number) => {
    if (!audioContextRef.current) return;

    const osc = audioContextRef.current.createOscillator();
    const gainNode = audioContextRef.current.createGain();

    osc.connect(gainNode);
    gainNode.connect(audioContextRef.current.destination);

    osc.frequency.value = frequency;
    osc.type = 'sine';

    gainNode.gain.setValueAtTime(0.3, audioContextRef.current.currentTime);
    gainNode.gain.exponentialRampToValueAtTime(
      0.01,
      audioContextRef.current.currentTime + duration
    );

    osc.start(audioContextRef.current.currentTime);
    osc.stop(audioContextRef.current.currentTime + duration);
  };

  const playClick = (isAccented: boolean) => {
    const frequency = isAccented ? 1000 : 800;
    createOscillator(frequency, 0.05);
  };

  const startMetronome = () => {
    if (!audioContextRef.current) {
      audioContextRef.current = new (window.AudioContext || (window as any).webkitAudioContext)();
    }

    setIsPlaying(true);
    startTimeRef.current = performance.now();
    setBeat(0);

    const interval = 60000 / bpm;

    intervalRef.current = setInterval(() => {
      setBeat(prevBeat => {
        const newBeat = (prevBeat + 1) % beatsPerMeasure;
        playClick(newBeat === 0);
        return newBeat;
      });
    }, interval);
  };

  const stopMetronome = () => {
    setIsPlaying(false);
    if (intervalRef.current) {
      clearInterval(intervalRef.current);
      intervalRef.current = null;
    }
  };

  const handleBpmChange = (newBpm: number) => {
    setBpm(newBpm);
    onBpmChange?.(newBpm);

    if (isPlaying) {
      stopMetronome();
      setTimeout(() => startMetronome(), 100);
    }
  };

  useEffect(() => {
    return () => {
      stopMetronome();
      audioContextRef.current?.close();
    };
  }, []);

  return (
    <div className="metronome">
      <div className="metronome-header">
        <h3>🎵 Metrônomo</h3>
        <div className={`metronome-status ${isPlaying ? 'playing' : 'paused'}`}>
          {isPlaying ? 'Tocando' : 'Pausado'}
        </div>
      </div>

      <div className="metronome-controls">
        <div className="bpm-control">
          <label>BPM: {bpm}</label>
          <input
            type="range"
            min="40"
            max="240"
            value={bpm}
            onChange={e => handleBpmChange(Number(e.target.value))}
            className="bpm-slider"
          />
          <div className="bpm-presets">
            <button onClick={() => handleBpmChange(60)}>Largo</button>
            <button onClick={() => handleBpmChange(90)}>Andante</button>
            <button onClick={() => handleBpmChange(120)}>Allegro</button>
            <button onClick={() => handleBpmChange(180)}>Presto</button>
          </div>
        </div>

        <div className="time-signature">
          <label htmlFor="time-signature">Compasso:</label>
          <select
            value={beatsPerMeasure}
            onChange={e => setBeatsPerMeasure(Number(e.target.value))}
          >
            <option value={2}>2/4</option>
            <option value={3}>3/4</option>
            <option value={4}>4/4</option>
            <option value={6}>6/8</option>
          </select>
        </div>

        <button
          className={`metronome-toggle ${isPlaying ? 'stop' : 'start'}`}
          onClick={isPlaying ? stopMetronome : startMetronome}
        >
          {isPlaying ? '⏹️ Parar' : '▶️ Iniciar'}
        </button>
      </div>

      <div className="beat-indicator">
        {Array.from({ length: beatsPerMeasure }, (_, index) => (
          <div
            key={index}
            className={`beat ${index === beat ? 'active' : ''} ${index === 0 ? 'accented' : ''}`}
          ></div>
        ))}
      </div>

      <div className="tap-tempo">
        <button
          className="tap-button"
          onClick={() => {
            const now = performance.now();
            if (startTimeRef.current) {
              const elapsed = now - startTimeRef.current;
              const tappedBpm = Math.round(60000 / elapsed);
              if (tappedBpm >= 40 && tappedBpm <= 240) {
                handleBpmChange(tappedBpm);
              }
            }
            startTimeRef.current = now;
          }}
        >
          👆 Toque para o Tempo
        </button>
        <small>Toque no ritmo para definir o BPM</small>
      </div>
    </div>
  );
};

export default Metronome;
