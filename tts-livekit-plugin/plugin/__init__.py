"""
MeloTTS LiveKit Plugin
Self-hosted TTS integration for LiveKit agents
"""
from .melotts_plugin import TTS, ChunkedStream

__all__ = ["TTS", "ChunkedStream"]
__version__ = "1.0.0"
