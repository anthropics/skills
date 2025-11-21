"""
LiveKit TTS Plugin for MeloTTS API
Integrates self-hosted MeloTTS with LiveKit agents
"""
import asyncio
import aiohttp
from typing import Optional
from dataclasses import dataclass

from livekit import agents
from livekit.agents import tts, utils


@dataclass
class _TTSOptions:
    """Configuration options for MeloTTS"""
    api_base_url: str
    language: str
    speaker: Optional[str]
    speed: float
    timeout: float


class TTS(tts.TTS):
    """
    LiveKit TTS plugin for MeloTTS API

    This plugin connects to a self-hosted MeloTTS API server
    and streams audio back to LiveKit agents.
    """

    def __init__(
        self,
        *,
        api_base_url: str = "http://localhost:8000",
        language: str = "EN",
        speaker: Optional[str] = "EN-US",
        speed: float = 1.0,
        timeout: float = 30.0,
        sample_rate: int = 44100,
        num_channels: int = 1,
    ) -> None:
        """
        Initialize MeloTTS plugin

        Args:
            api_base_url: Base URL of the MeloTTS API server
            language: Language code (EN, ES, FR, ZH, JP, KR)
            speaker: Speaker ID (e.g., EN-US, EN-BR, EN-AU, EN-IN)
            speed: Speech speed (0.5 to 2.0)
            timeout: Request timeout in seconds
            sample_rate: Audio sample rate (MeloTTS outputs 44100)
            num_channels: Number of audio channels (1 for mono)
        """
        super().__init__(
            capabilities=tts.TTSCapabilities(
                streaming=True,  # We support streaming via chunked HTTP
            ),
            sample_rate=sample_rate,
            num_channels=num_channels,
        )

        self._opts = _TTSOptions(
            api_base_url=api_base_url.rstrip("/"),
            language=language,
            speaker=speaker,
            speed=speed,
            timeout=timeout,
        )
        self._session: Optional[aiohttp.ClientSession] = None

    def _ensure_session(self) -> aiohttp.ClientSession:
        """Ensure aiohttp session exists"""
        if self._session is None:
            self._session = aiohttp.ClientSession()
        return self._session

    async def aclose(self) -> None:
        """Close the aiohttp session"""
        if self._session is not None:
            await self._session.close()
            self._session = None

    def synthesize(
        self,
        text: str,
        *,
        conn_options: agents.APIConnectOptions = agents.DEFAULT_API_CONNECT_OPTIONS,
    ) -> "ChunkedStream":
        """
        Synthesize text to speech

        Args:
            text: Text to synthesize
            conn_options: API connection options

        Returns:
            ChunkedStream that yields audio data
        """
        return ChunkedStream(
            tts=self,
            input_text=text,
            conn_options=conn_options,
            opts=self._opts,
        )

    @property
    def model(self) -> str:
        """Return the model identifier"""
        return "melotts"

    @property
    def provider(self) -> str:
        """Return the provider name"""
        return "custom-melotts"


class ChunkedStream(tts.ChunkedStream):
    """
    Handles streaming audio from MeloTTS API
    """

    def __init__(
        self,
        *,
        tts: TTS,
        input_text: str,
        conn_options: agents.APIConnectOptions,
        opts: _TTSOptions,
    ) -> None:
        super().__init__(tts=tts, input_text=input_text, conn_options=conn_options)
        self._opts = opts
        self._tts = tts

    async def _run(self, output_emitter: tts.AudioEmitter) -> None:
        """
        Execute the TTS synthesis and stream audio chunks

        Args:
            output_emitter: Emitter to push audio data to LiveKit
        """
        request_id = utils.shortuuid()
        segment_id = utils.shortuuid()

        try:
            # Prepare request payload
            payload = {
                "text": self._input_text,
                "language": self._opts.language,
                "speaker": self._opts.speaker,
                "speed": self._opts.speed,
            }

            url = f"{self._opts.api_base_url}/synthesize/stream"

            # Make HTTP request to TTS API
            session = self._tts._ensure_session()

            async with session.post(
                url,
                json=payload,
                timeout=aiohttp.ClientTimeout(total=self._opts.timeout),
            ) as resp:
                # Check response status
                if resp.status != 200:
                    error_text = await resp.text()
                    raise agents.APIStatusError(
                        message=f"TTS API returned status {resp.status}: {error_text}",
                        status_code=resp.status,
                        request_id=request_id,
                        body=error_text,
                    )

                # Verify content type
                content_type = resp.headers.get("Content-Type", "")
                if not content_type.startswith("audio/"):
                    raise agents.APIStatusError(
                        message=f"Unexpected content type: {content_type}",
                        status_code=resp.status,
                        request_id=request_id,
                        body=None,
                    )

                # Initialize the output emitter
                # MeloTTS outputs WAV format
                output_emitter.initialize(
                    mime_type="audio/wav",
                    sample_rate=self._tts.sample_rate,
                    num_channels=self._tts.num_channels,
                )

                # Start audio segment
                output_emitter.start_segment(segment_id)

                # Stream audio chunks
                chunk_count = 0
                async for chunk, _ in resp.content.iter_chunks():
                    if chunk:
                        output_emitter.push(chunk)
                        chunk_count += 1

                # End segment and flush
                output_emitter.end_segment(segment_id)
                output_emitter.flush()

        except asyncio.TimeoutError as e:
            raise agents.APITimeoutError() from e

        except aiohttp.ClientError as e:
            raise agents.APIConnectionError(
                message=f"Failed to connect to TTS API: {str(e)}"
            ) from e

        except agents.APIError:
            # Re-raise API errors as-is
            raise

        except Exception as e:
            # Wrap unexpected errors
            raise agents.APIConnectionError(
                message=f"Unexpected error during TTS synthesis: {str(e)}"
            ) from e
