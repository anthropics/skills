"""
Simple LiveKit Agent Example using MeloTTS Plugin
This example demonstrates basic usage of the MeloTTS plugin with a LiveKit agent
"""
import asyncio
import logging
from dotenv import load_dotenv

from livekit import agents
from livekit.agents import JobContext, WorkerOptions, cli

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


async def entrypoint(ctx: JobContext):
    """
    Entry point for the LiveKit agent
    This function is called when a new participant joins
    """
    logger.info(f"Starting agent for room: {ctx.room.name}")

    # Initialize the MeloTTS plugin
    tts = MeloTTS(
        api_base_url="http://localhost:8000",
        language="EN",
        speaker="EN-US",
        speed=1.0,
    )

    # Connect to the room
    await ctx.connect()
    logger.info("Agent connected to room")

    # Example: Synthesize welcome message
    welcome_text = "Hello! I am a voice agent powered by MeloTTS and LiveKit."

    try:
        logger.info(f"Synthesizing: {welcome_text}")

        # Synthesize text to speech
        stream = tts.synthesize(welcome_text)

        # Create audio source
        audio_source = agents.AudioSource(
            sample_rate=tts.sample_rate,
            num_channels=tts.num_channels
        )

        # Create audio emitter
        class SimpleAudioEmitter:
            def __init__(self, audio_source):
                self.audio_source = audio_source
                self.segment_id = None

            def initialize(self, mime_type, sample_rate, num_channels):
                logger.info(f"Audio initialized: {mime_type}, {sample_rate}Hz, {num_channels} channels")

            def start_segment(self, segment_id):
                self.segment_id = segment_id
                logger.info(f"Started segment: {segment_id}")

            def push(self, audio_data):
                # In a real implementation, push to LiveKit audio track
                logger.debug(f"Received audio chunk: {len(audio_data)} bytes")

            def end_segment(self, segment_id):
                logger.info(f"Ended segment: {segment_id}")

            def flush(self):
                logger.info("Audio flushed")

        emitter = SimpleAudioEmitter(audio_source)

        # Run the synthesis
        await stream._run(emitter)

        logger.info("Synthesis completed successfully")

    except Exception as e:
        logger.error(f"Error during synthesis: {e}", exc_info=True)

    finally:
        # Clean up
        await tts.aclose()
        logger.info("Agent finished")


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
