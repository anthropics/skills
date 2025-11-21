"""
Voice Assistant Example using MeloTTS Plugin
This example demonstrates a more complete voice assistant with:
- Speech-to-Text (using LiveKit's STT)
- LLM for response generation
- Text-to-Speech (using MeloTTS plugin)
"""
import asyncio
import logging
from typing import AsyncIterable
from dotenv import load_dotenv

from livekit import agents, rtc
from livekit.agents import JobContext, WorkerOptions, cli, llm
from livekit.agents import stt, tokenize

# Import the MeloTTS plugin
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'plugin'))
from melotts_plugin import TTS as MeloTTS


# Load environment variables
load_dotenv()

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class VoiceAssistant:
    """Voice Assistant using MeloTTS for TTS"""

    def __init__(
        self,
        *,
        tts: MeloTTS,
        llm_instance: llm.LLM,
        stt_instance: stt.STT,
    ):
        self.tts = tts
        self.llm = llm_instance
        self.stt = stt_instance
        self.chat_context = llm.ChatContext()
        self.chat_context.append(
            role="system",
            text="You are a helpful voice assistant. Keep your responses concise and conversational."
        )

    async def say(self, text: str, room: rtc.Room):
        """
        Speak text using TTS and publish to room
        """
        logger.info(f"Speaking: {text}")

        try:
            # Synthesize speech
            stream = self.tts.synthesize(text)

            # Create audio track
            audio_source = rtc.AudioSource(
                sample_rate=self.tts.sample_rate,
                num_channels=self.tts.num_channels
            )

            track = rtc.LocalAudioTrack.create_audio_track("assistant_voice", audio_source)
            publication = await room.local_participant.publish_track(track)

            logger.info("Audio track published")

            # Stream audio
            class RoomAudioEmitter:
                def __init__(self, audio_source):
                    self.audio_source = audio_source
                    self.frames = []

                def initialize(self, mime_type, sample_rate, num_channels):
                    logger.info(f"Initialized: {mime_type}")

                def start_segment(self, segment_id):
                    pass

                def push(self, audio_data):
                    # Convert to AudioFrame and publish
                    self.frames.append(audio_data)

                def end_segment(self, segment_id):
                    pass

                def flush(self):
                    pass

            emitter = RoomAudioEmitter(audio_source)
            await stream._run(emitter)

            # Unpublish track after speaking
            await room.local_participant.unpublish_track(track.sid)

        except Exception as e:
            logger.error(f"Error in say(): {e}", exc_info=True)

    async def handle_speech(self, text: str, room: rtc.Room):
        """
        Handle user speech input
        """
        logger.info(f"User said: {text}")

        # Add user message to context
        self.chat_context.append(role="user", text=text)

        # Generate response using LLM
        response_text = ""
        async for chunk in self.llm.chat(self.chat_context):
            if isinstance(chunk, llm.ChatChunk):
                response_text += chunk.delta

        logger.info(f"Assistant response: {response_text}")

        # Add assistant response to context
        self.chat_context.append(role="assistant", text=response_text)

        # Speak the response
        await self.say(response_text, room)


async def entrypoint(ctx: JobContext):
    """
    Entry point for the voice assistant agent
    """
    logger.info(f"Starting voice assistant for room: {ctx.room.name}")

    # Initialize components
    # Note: You need to configure your own STT and LLM providers
    # For example, using OpenAI:
    # from livekit.plugins import openai
    # stt_instance = openai.STT()
    # llm_instance = openai.LLM(model="gpt-4")

    # For this example, we'll use placeholders
    # In production, replace with actual implementations
    logger.warning("STT and LLM need to be configured with actual providers")

    tts = MeloTTS(
        api_base_url="http://localhost:8000",
        language="EN",
        speaker="EN-US",
        speed=1.0,
    )

    # Connect to room
    await ctx.connect()
    logger.info("Voice assistant connected")

    # Greet the user
    greeting = "Hello! I'm your voice assistant. How can I help you today?"
    await tts.synthesize(greeting)

    try:
        # Main loop would handle:
        # 1. Listen for user speech (STT)
        # 2. Process with LLM
        # 3. Respond with TTS

        # This is a simplified example
        # In production, you would:
        # - Subscribe to audio tracks
        # - Process audio with STT
        # - Use LLM for responses
        # - Use TTS for output

        # Keep the agent running
        await asyncio.Future()  # Run forever

    finally:
        await tts.aclose()
        logger.info("Voice assistant stopped")


def main():
    """
    Main function to start the LiveKit worker
    """
    cli.run_app(
        WorkerOptions(
            entrypoint_fnc=entrypoint,
        )
    )


if __name__ == "__main__":
    main()
