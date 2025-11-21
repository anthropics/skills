"""
FastAPI TTS Server using MeloTTS
Provides streaming text-to-speech API for LiveKit integration
"""
import io
import os
import asyncio
import tempfile
import threading
from typing import Optional, Dict
from contextlib import asynccontextmanager

from fastapi import FastAPI, HTTPException, Query
from fastapi.responses import StreamingResponse
from pydantic import BaseModel, Field
import uvicorn

# MeloTTS imports
try:
    from melo.api import TTS as MeloTTS
except ImportError:
    raise ImportError(
        "MeloTTS not installed. Install with: pip install git+https://github.com/myshell-ai/MeloTTS.git"
    )


# Supported languages
SUPPORTED_LANGUAGES = ['EN', 'ES', 'FR', 'ZH', 'JP', 'KR']


class TTSRequest(BaseModel):
    """Request model for TTS synthesis"""
    text: str = Field(..., description="Text to synthesize", min_length=1, max_length=5000)
    language: str = Field(default="EN", description="Language code (EN, ES, FR, ZH, JP, KR)")
    speaker: Optional[str] = Field(default=None, description="Speaker ID (e.g., EN-US, EN-BR, EN-AU, EN-IN)")
    speed: float = Field(default=1.0, description="Speech speed", ge=0.5, le=2.0)


class TTSModels:
    """Thread-safe singleton to manage TTS models"""
    def __init__(self):
        self.models: Dict[str, MeloTTS] = {}
        self.device = "auto"  # Will use GPU if available
        self._lock = threading.Lock()

    def get_model(self, language: str) -> MeloTTS:
        """Get or create a TTS model for the specified language (thread-safe)"""
        # Validate language before attempting to load
        if language not in SUPPORTED_LANGUAGES:
            raise HTTPException(
                status_code=400,
                detail=f"Unsupported language '{language}'. Supported: {SUPPORTED_LANGUAGES}"
            )

        # Double-checked locking pattern for performance
        if language in self.models:
            return self.models[language]

        with self._lock:
            # Check again inside lock to prevent race condition
            if language not in self.models:
                try:
                    self.models[language] = MeloTTS(language=language, device=self.device)
                except Exception as e:
                    raise HTTPException(
                        status_code=500,
                        detail=f"Failed to load TTS model for language {language}: {str(e)}"
                    )
            return self.models[language]

    def get_speaker_id(self, model: MeloTTS, language: str, speaker: Optional[str]) -> int:
        """Get speaker ID from model"""
        speaker_ids = model.hps.data.spk2id

        # If no speaker specified, use first available
        if not speaker:
            return list(speaker_ids.values())[0]

        # Try to find exact match
        if speaker in speaker_ids:
            return speaker_ids[speaker]

        # Try uppercase
        speaker_upper = speaker.upper()
        if speaker_upper in speaker_ids:
            return speaker_ids[speaker_upper]

        raise HTTPException(
            status_code=400,
            detail=f"Speaker '{speaker}' not found. Available speakers: {list(speaker_ids.keys())}"
        )

    def cleanup(self):
        """Clean up all loaded models"""
        with self._lock:
            self.models.clear()


# Global models instance
tts_models = TTSModels()


@asynccontextmanager
async def lifespan(app: FastAPI):
    """Lifecycle manager for the FastAPI app"""
    # Startup: Initialize default models
    print("Initializing TTS models...")
    try:
        # Pre-load English model
        tts_models.get_model("EN")
        print("TTS models initialized successfully")
    except Exception as e:
        print(f"Warning: Failed to pre-load models: {e}")

    yield

    # Shutdown: Clean up resources
    print("Shutting down TTS server...")
    try:
        tts_models.cleanup()
        print("TTS models cleaned up successfully")
    except Exception as e:
        print(f"Warning: Error during cleanup: {e}")


app = FastAPI(
    title="MeloTTS API Server",
    description="Self-hosted Text-to-Speech API using MeloTTS for LiveKit integration",
    version="1.0.0",
    lifespan=lifespan
)


@app.get("/")
async def root():
    """Health check endpoint"""
    return {
        "status": "ok",
        "service": "MeloTTS API",
        "version": "1.0.0"
    }


@app.get("/voices")
async def list_voices(language: str = Query(default="EN", description="Language code")):
    """List available voices for a language"""
    try:
        model = tts_models.get_model(language)
        speakers = model.hps.data.spk2id
        return {
            "language": language,
            "voices": list(speakers.keys())
        }
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


async def generate_audio_chunks(
    text: str,
    language: str,
    speaker: Optional[str],
    speed: float,
    chunk_size: int = 8192
):
    """Generate audio in chunks for streaming"""
    tmp_path = None
    try:
        # Get model and speaker ID
        model = tts_models.get_model(language)
        speaker_id = tts_models.get_speaker_id(model, language, speaker)

        # Generate audio to temporary file
        # MeloTTS requires a file path, not a buffer
        with tempfile.NamedTemporaryFile(suffix='.wav', delete=False) as tmp_file:
            tmp_path = tmp_file.name

        # Run synthesis in thread pool to avoid blocking (Python 3.10+ compatible)
        loop = asyncio.get_running_loop()
        await loop.run_in_executor(
            None,
            lambda: model.tts_to_file(
                text,
                speaker_id,
                tmp_path,
                speed=speed
            )
        )

        # Read audio data from file
        with open(tmp_path, 'rb') as f:
            audio_data = f.read()

        # Stream in chunks
        for i in range(0, len(audio_data), chunk_size):
            chunk = audio_data[i:i + chunk_size]
            yield chunk
            # Small delay to simulate streaming and avoid overwhelming client
            await asyncio.sleep(0.01)

    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(
            status_code=500,
            detail=f"Audio generation failed: {str(e)}"
        )
    finally:
        # Clean up temporary file
        if tmp_path and os.path.exists(tmp_path):
            try:
                os.unlink(tmp_path)
            except Exception as e:
                print(f"Warning: Failed to delete temp file {tmp_path}: {e}")


@app.post("/synthesize/stream")
async def synthesize_stream(request: TTSRequest):
    """
    Stream TTS audio in chunks
    This endpoint is optimized for LiveKit integration
    """
    return StreamingResponse(
        generate_audio_chunks(
            text=request.text,
            language=request.language,
            speaker=request.speaker,
            speed=request.speed
        ),
        media_type="audio/wav",
        headers={
            "Content-Disposition": "attachment; filename=speech.wav",
            "Cache-Control": "no-cache"
        }
    )


@app.post("/synthesize")
async def synthesize(request: TTSRequest):
    """
    Generate complete TTS audio
    Returns full audio file (non-streaming)
    """
    tmp_path = None
    try:
        # Get model and speaker ID
        model = tts_models.get_model(request.language)
        speaker_id = tts_models.get_speaker_id(model, request.language, request.speaker)

        # Generate audio to temporary file
        with tempfile.NamedTemporaryFile(suffix='.wav', delete=False) as tmp_file:
            tmp_path = tmp_file.name

        # Run synthesis in thread pool (Python 3.10+ compatible)
        loop = asyncio.get_running_loop()
        await loop.run_in_executor(
            None,
            lambda: model.tts_to_file(
                request.text,
                speaker_id,
                tmp_path,
                speed=request.speed
            )
        )

        # Read audio data from file
        with open(tmp_path, 'rb') as f:
            audio_data = f.read()

        return StreamingResponse(
            io.BytesIO(audio_data),
            media_type="audio/wav",
            headers={
                "Content-Disposition": "attachment; filename=speech.wav",
                "Content-Length": str(len(audio_data))
            }
        )

    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(
            status_code=500,
            detail=f"Audio generation failed: {str(e)}"
        )
    finally:
        # Clean up temporary file
        if tmp_path and os.path.exists(tmp_path):
            try:
                os.unlink(tmp_path)
            except Exception as e:
                print(f"Warning: Failed to delete temp file {tmp_path}: {e}")


if __name__ == "__main__":
    uvicorn.run(
        "server:app",
        host="0.0.0.0",
        port=8000,
        reload=True,
        log_level="info"
    )
