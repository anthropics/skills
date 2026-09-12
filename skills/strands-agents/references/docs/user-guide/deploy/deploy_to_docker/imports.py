# --8<-- [start: imports]
from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
from typing import Dict, Any
from datetime import datetime, timezone
from strands import Agent
from strands.models.openai import OpenAIModel

# --8<-- [end: imports]
