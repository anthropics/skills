import React, { useState, useEffect, useRef } from 'react';
import * as Tone from 'tone';
import { Midi } from '@tonejs/midi';
import './MidiPlayer.css';

interface MidiPlayerProps {
  midiUrl?: string;
  midiData?: ArrayBuffer;
  onProgress?: (progress: number) => void;
  onNotePlay?: (note: string, velocity: number) => void;
  autoPlay?: boolean;
}

const MidiPlayer: React.FC<MidiPlayerProps> = ({
  midiUrl,
  midiData,
  onProgress,
  onNotePlay,
  autoPlay = false,
}) => {
  const [isPlaying, setIsPlaying] = useState(false);
  const [isLoading, setIsLoading] = useState(false);
  const [progress, setProgress] = useState(0);
  const [duration, setDuration] = useState(0);
  const [speed, setSpeed] = useState(1.0);
  const [volume, setVolume] = useState(-10);

  const synthRef = useRef<Tone.PolySynth | null>(null);
  const midiRef = useRef<Midi | null>(null);
  const eventsRef = useRef<number[]>([]);

  useEffect(() => {
    // Initialize synthesizer
    synthRef.current = new Tone.PolySynth(Tone.Synth, {
      envelope: {
        attack: 0.02,
        decay: 0.1,
        sustain: 0.3,
        release: 1,
      },
    }).toDestination();

    synthRef.current.volume.value = volume;

    return () => {
      stop();
      synthRef.current?.dispose();
    };
  }, []);

  useEffect(() => {
    if (midiUrl) {
      loadMidiFromUrl(midiUrl);
    } else if (midiData) {
      loadMidiFromData(midiData);
    }
  }, [midiUrl, midiData]);

  useEffect(() => {
    Tone.Transport.bpm.value = 120 * speed;
  }, [speed]);

  useEffect(() => {
    if (synthRef.current) {
      synthRef.current.volume.value = volume;
    }
  }, [volume]);

  const loadMidiFromUrl = async (url: string) => {
    setIsLoading(true);
    try {
      const midi = await Midi.fromUrl(url);
      midiRef.current = midi;
      setDuration(midi.duration);
      scheduleMidi(midi);
      setIsLoading(false);

      if (autoPlay) {
        play();
      }
    } catch (error) {
      console.error('Error loading MIDI:', error);
      setIsLoading(false);
    }
  };

  const loadMidiFromData = async (data: ArrayBuffer) => {
    setIsLoading(true);
    try {
      const midi = new Midi(data);
      midiRef.current = midi;
      setDuration(midi.duration);
      scheduleMidi(midi);
      setIsLoading(false);

      if (autoPlay) {
        play();
      }
    } catch (error) {
      console.error('Error loading MIDI data:', error);
      setIsLoading(false);
    }
  };

  const scheduleMidi = (midi: Midi) => {
    // Clear previous events
    eventsRef.current.forEach(id => Tone.Transport.clear(id));
    eventsRef.current = [];

    // Schedule all notes
    midi.tracks.forEach(track => {
      track.notes.forEach(note => {
        const eventId = Tone.Transport.schedule(time => {
          if (synthRef.current) {
            synthRef.current.triggerAttackRelease(note.name, note.duration, time, note.velocity);

            // Notify parent component
            onNotePlay?.(note.name, note.velocity);
          }
        }, note.time);

        eventsRef.current.push(eventId);
      });
    });
  };

  const play = async () => {
    await Tone.start();
    Tone.Transport.start();
    setIsPlaying(true);

    // Update progress
    const updateProgress = () => {
      if (Tone.Transport.state === 'started') {
        const currentProgress = Tone.Transport.seconds / duration;
        setProgress(currentProgress);
        onProgress?.(currentProgress);
        requestAnimationFrame(updateProgress);
      }
    };
    updateProgress();
  };

  const pause = () => {
    Tone.Transport.pause();
    setIsPlaying(false);
  };

  const stop = () => {
    Tone.Transport.stop();
    Tone.Transport.seconds = 0;
    setIsPlaying(false);
    setProgress(0);
  };

  const seek = (position: number) => {
    const newTime = position * duration;
    Tone.Transport.seconds = newTime;
    setProgress(position);
  };

  const formatTime = (seconds: number) => {
    const mins = Math.floor(seconds / 60);
    const secs = Math.floor(seconds % 60);
    return `${mins}:${secs.toString().padStart(2, '0')}`;
  };

  return (
    <div className="midi-player">
      <div className="player-header">
        <h3>🎹 MIDI Player</h3>
        {isLoading && <span className="loading">Carregando...</span>}
      </div>

      <div className="player-controls">
        <div className="transport-controls">
          <button
            onClick={stop}
            disabled={!midiRef.current || isLoading}
            className="control-btn stop"
          >
            ⏹️
          </button>
          <button
            onClick={isPlaying ? pause : play}
            disabled={!midiRef.current || isLoading}
            className="control-btn play-pause"
          >
            {isPlaying ? '⏸️' : '▶️'}
          </button>
        </div>

        <div className="progress-bar-container">
          <span className="time-display">{formatTime(progress * duration)}</span>
          <input
            type="range"
            min="0"
            max="1"
            step="0.001"
            value={progress}
            onChange={e => seek(parseFloat(e.target.value))}
            className="progress-bar"
            disabled={!midiRef.current}
          />
          <span className="time-display">{formatTime(duration)}</span>
        </div>
      </div>

      <div className="player-settings">
        <div className="setting">
          <label>Velocidade: {speed.toFixed(1)}x</label>
          <input
            type="range"
            min="0.25"
            max="2"
            step="0.05"
            value={speed}
            onChange={e => setSpeed(parseFloat(e.target.value))}
            className="setting-slider"
          />
          <div className="speed-presets">
            <button onClick={() => setSpeed(0.5)}>0.5x</button>
            <button onClick={() => setSpeed(0.75)}>0.75x</button>
            <button onClick={() => setSpeed(1.0)}>1x</button>
            <button onClick={() => setSpeed(1.25)}>1.25x</button>
          </div>
        </div>

        <div className="setting">
          <label>Volume: {volume}dB</label>
          <input
            type="range"
            min="-30"
            max="0"
            step="1"
            value={volume}
            onChange={e => setVolume(parseInt(e.target.value))}
            className="setting-slider"
          />
        </div>
      </div>

      {!midiRef.current && !isLoading && (
        <div className="no-midi">
          <p>Nenhum arquivo MIDI carregado</p>
          <small>Forneça uma URL ou dados MIDI para começar</small>
        </div>
      )}
    </div>
  );
};

export default MidiPlayer;
