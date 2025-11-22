"""
FastAPI TTS Server using MeloTTS
Provides streaming text-to-speech API for LiveKit integration
"""
import io
import os
import asyncio
import tempfile
import threading
import logging
import signal
import sys
from typing import Optional, Dict
from contextlib import asynccontextmanager
from datetime import datetime

from fastapi import FastAPI, HTTPException, Query, Request
from fastapi.responses import StreamingResponse
from pydantic import BaseModel, Field
import uvicorn

# Configure structured logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    stream=sys.stdout
)
logger = logging.getLogger(__name__)

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
        self._metrics = {"requests": 0, "errors": 0, "models_loaded": 0}

    def get_model(self, language: str) -> MeloTTS:
        """Get or create a TTS model for the specified language (thread-safe)"""
        # Validate language before attempting to load
        if language not in SUPPORTED_LANGUAGES:
            logger.warning(f"Unsupported language requested: {language}")
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
                    logger.info(f"Loading TTS model for language: {language}")
                    start_time = datetime.now()
                    self.models[language] = MeloTTS(language=language, device=self.device)
                    load_time = (datetime.now() - start_time).total_seconds()
                    self._metrics["models_loaded"] += 1
                    logger.info(f"TTS model loaded for {language} in {load_time:.2f}s")
                except Exception as e:
                    logger.error(f"Failed to load TTS model for {language}: {e}", exc_info=True)
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

        logger.warning(f"Speaker not found: {speaker}. Available: {list(speaker_ids.keys())}")
        raise HTTPException(
            status_code=400,
            detail=f"Speaker '{speaker}' not found. Available speakers: {list(speaker_ids.keys())}"
        )

    def increment_requests(self):
        """Increment request counter"""
        with self._lock:
            self._metrics["requests"] += 1

    def increment_errors(self):
        """Increment error counter"""
        with self._lock:
            self._metrics["errors"] += 1

    def get_metrics(self) -> Dict:
        """Get metrics snapshot"""
        with self._lock:
            return self._metrics.copy()

    def cleanup(self):
        """Clean up all loaded models"""
        with self._lock:
            logger.info(f"Cleaning up {len(self.models)} loaded models")
            self.models.clear()


# Global models instance
tts_models = TTSModels()

# Shutdown event
shutdown_event = asyncio.Event()


def signal_handler(signum, frame):
    """Handle shutdown signals gracefully"""
    logger.info(f"Received signal {signum}, initiating graceful shutdown...")
    shutdown_event.set()


# Register signal handlers
signal.signal(signal.SIGINT, signal_handler)
signal.signal(signal.SIGTERM, signal_handler)


@asynccontextmanager
async def lifespan(app: FastAPI):
    """Lifecycle manager for the FastAPI app"""
    # Startup: Initialize default models
    logger.info("Starting MeloTTS API server...")
    try:
        # Pre-load English model
        tts_models.get_model("EN")
        logger.info("TTS models initialized successfully")
    except Exception as e:
        logger.warning(f"Failed to pre-load models: {e}")

    yield

    # Shutdown: Clean up resources
    logger.info("Shutting down TTS server...")
    try:
        metrics = tts_models.get_metrics()
        logger.info(f"Server metrics: {metrics}")
        tts_models.cleanup()
        logger.info("TTS models cleaned up successfully")
    except Exception as e:
        logger.error(f"Error during cleanup: {e}", exc_info=True)


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


@app.get("/health")
async def health():
    """Detailed health check with metrics"""
    metrics = tts_models.get_metrics()
    return {
        "status": "healthy",
        "metrics": metrics,
        "models_loaded": list(tts_models.models.keys())
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
        logger.error(f"Error listing voices: {e}", exc_info=True)
        raise HTTPException(status_code=500, detail=str(e))


async def generate_audio_chunks(
    text: str,
    language: str,
    speaker: Optional[str],
    speed: float,
    chunk_size: int = 8192,
    request_id: str = "unknown"
):
    """Generate audio in chunks for streaming"""
    tmp_path = None
    try:
        start_time = datetime.now()
        logger.info(f"[{request_id}] Starting synthesis: {len(text)} chars, lang={language}, speaker={speaker}")

        # Get model and speaker ID (validates before starting stream)
        model = tts_models.get_model(language)
        speaker_id = tts_models.get_speaker_id(model, language, speaker)

        # Generate audio to temporary file
        with tempfile.NamedTemporaryFile(suffix='.wav', delete=False) as tmp_file:
            tmp_path = tmp_file.name

        # Run synthesis in thread pool (Python 3.10+ compatible)
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

        synthesis_time = (datetime.now() - start_time).total_seconds()
        logger.info(f"[{request_id}] Synthesis completed in {synthesis_time:.2f}s")

        # Read audio data from file
        with open(tmp_path, 'rb') as f:
            audio_data = f.read()

        logger.info(f"[{request_id}] Streaming {len(audio_data)} bytes in chunks")

        # Stream in chunks
        bytes_sent = 0
        for i in range(0, len(audio_data), chunk_size):
            chunk = audio_data[i:i + chunk_size]
            yield chunk
            bytes_sent += len(chunk)
            # Small delay to prevent overwhelming client
            await asyncio.sleep(0.01)

        total_time = (datetime.now() - start_time).total_seconds()
        logger.info(f"[{request_id}] Completed: {bytes_sent} bytes in {total_time:.2f}s")

    except HTTPException:
        tts_models.increment_errors()
        raise
    except Exception as e:
        tts_models.increment_errors()
        logger.error(f"[{request_id}] Audio generation failed: {e}", exc_info=True)
        raise HTTPException(
            status_code=500,
            detail=f"Audio generation failed: {str(e)}"
        )
    finally:
        # Clean up temporary file
        if tmp_path and os.path.exists(tmp_path):
            try:
                os.unlink(tmp_path)
                logger.debug(f"[{request_id}] Cleaned up temp file: {tmp_path}")
            except Exception as e:
                logger.warning(f"[{request_id}] Failed to delete temp file {tmp_path}: {e}")


@app.post("/synthesize/stream")
async def synthesize_stream(request: TTSRequest, http_request: Request):
    """
    Stream TTS audio in chunks
    This endpoint is optimized for LiveKit integration
    """
    request_id = id(http_request)
    tts_models.increment_requests()

    # Validate inputs BEFORE starting streaming (critical for error handling)
    try:
        model = tts_models.get_model(request.language)
        tts_models.get_speaker_id(model, request.language, request.speaker)
    except HTTPException:
        raise

    return StreamingResponse(
        generate_audio_chunks(
            text=request.text,
            language=request.language,
            speaker=request.speaker,
            speed=request.speed,
            request_id=str(request_id)
        ),
        media_type="audio/wav",
        headers={
            "Content-Disposition": "attachment; filename=speech.wav",
            "Cache-Control": "no-cache",
            "X-Request-ID": str(request_id)
        }
    )


@app.post("/synthesize")
async def synthesize(request: TTSRequest, http_request: Request):
    """
    Generate complete TTS audio
    Returns full audio file (non-streaming)
    """
    request_id = id(http_request)
    tts_models.increment_requests()
    tmp_path = None

    try:
        start_time = datetime.now()
        logger.info(f"[{request_id}] Synthesizing: {len(request.text)} chars")

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

        total_time = (datetime.now() - start_time).total_seconds()
        logger.info(f"[{request_id}] Completed: {len(audio_data)} bytes in {total_time:.2f}s")

        return StreamingResponse(
            io.BytesIO(audio_data),
            media_type="audio/wav",
            headers={
                "Content-Disposition": "attachment; filename=speech.wav",
                "Content-Length": str(len(audio_data)),
                "X-Request-ID": str(request_id)
            }
        )

    except HTTPException:
        tts_models.increment_errors()
        raise
    except Exception as e:
        tts_models.increment_errors()
        logger.error(f"[{request_id}] Audio generation failed: {e}", exc_info=True)
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
                logger.warning(f"[{request_id}] Failed to delete temp file {tmp_path}: {e}")


if __name__ == "__main__":
    uvicorn.run(
        "server:app",
        host="0.0.0.0",
        port=8000,
        reload=True,
        log_level="info"
    )
