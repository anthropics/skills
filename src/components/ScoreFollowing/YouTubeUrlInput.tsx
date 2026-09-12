import React, { useState } from 'react';
import './YouTubeUrlInput.css';

interface YouTubeUrlInputProps {
  onUrlSubmit: (url: string, videoId: string) => void;
  isProcessing?: boolean;
}

const YouTubeUrlInput: React.FC<YouTubeUrlInputProps> = ({ onUrlSubmit, isProcessing = false }) => {
  const [url, setUrl] = useState('');
  const [error, setError] = useState('');
  const [videoPreview, setVideoPreview] = useState<string | null>(null);

  const extractVideoId = (url: string): string | null => {
    // Support various YouTube URL formats
    const patterns = [
      /(?:youtube\.com\/watch\?v=|youtu\.be\/|youtube\.com\/embed\/)([^&\n?#]+)/,
      /^([a-zA-Z0-9_-]{11})$/, // Direct video ID
    ];

    for (const pattern of patterns) {
      const match = url.match(pattern);
      if (match && match[1]) {
        return match[1];
      }
    }

    return null;
  };

  const handleUrlChange = (value: string) => {
    setUrl(value);
    setError('');

    if (value.trim()) {
      const videoId = extractVideoId(value.trim());
      if (videoId) {
        setVideoPreview(videoId);
        setError('');
      } else {
        setVideoPreview(null);
        setError('');
      }
    } else {
      setVideoPreview(null);
    }
  };

  const handleSubmit = (e: React.FormEvent) => {
    e.preventDefault();

    if (!url.trim()) {
      setError('Por favor, insira uma URL do YouTube');
      return;
    }

    const videoId = extractVideoId(url.trim());

    if (!videoId) {
      setError('URL inválida. Use um link do YouTube como youtube.com/watch?v=... ou youtu.be/...');
      return;
    }

    onUrlSubmit(url.trim(), videoId);
  };

  const exampleUrls = [
    'https://www.youtube.com/watch?v=dQw4w9WgXcQ',
    'https://youtu.be/dQw4w9WgXcQ',
    'dQw4w9WgXcQ',
  ];

  return (
    <div className="youtube-url-input">
      <div className="input-header">
        <h2>📺 YouTube → Piano Tutorial</h2>
        <p>Converta qualquer música do YouTube em um tutorial de piano interativo</p>
      </div>

      <form onSubmit={handleSubmit} className="url-form">
        <div className="input-group">
          <input
            type="text"
            value={url}
            onChange={e => handleUrlChange(e.target.value)}
            placeholder="Cole a URL do YouTube aqui..."
            className={`url-input ${error ? 'error' : ''} ${videoPreview ? 'valid' : ''}`}
            disabled={isProcessing}
          />
          <button type="submit" className="submit-btn" disabled={isProcessing || !url.trim()}>
            {isProcessing ? (
              <>
                <span className="spinner"></span>
                Processando...
              </>
            ) : (
              <>🎹 Converter</>
            )}
          </button>
        </div>

        {error && <div className="error-message">{error}</div>}
      </form>

      {videoPreview && !error && (
        <div className="video-preview">
          <h4>Pré-visualização:</h4>
          <div className="preview-container">
            <img
              src={`https://img.youtube.com/vi/${videoPreview}/mqdefault.jpg`}
              alt="Video preview"
              className="preview-thumbnail"
            />
            <div className="preview-info">
              <p>ID do vídeo: {videoPreview}</p>
              <small>Clique em &quot;Converter&quot; para gerar o tutorial de piano</small>
            </div>
          </div>
        </div>
      )}

      <div className="examples">
        <h4>Formatos suportados:</h4>
        <div className="example-urls">
          {exampleUrls.map((example, index) => (
            <button
              key={index}
              type="button"
              onClick={() => handleUrlChange(example)}
              className="example-url"
            >
              <code>{example}</code>
            </button>
          ))}
        </div>
      </div>

      <div className="features-info">
        <h4>O que você receberá:</h4>
        <ul>
          <li>🎵 Notas identificadas automaticamente com IA</li>
          <li>
            🎨 Cores por nível de dificuldade (Verde = Fácil, Amarelo = Médio, Vermelho = Difícil)
          </li>
          <li>🎹 Player MIDI interativo com controle de velocidade</li>
          <li>📊 Análise de dificuldade da música</li>
          <li>🔄 Loop de estudo para seções específicas</li>
        </ul>
      </div>
    </div>
  );
};

export default YouTubeUrlInput;
