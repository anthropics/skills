from pydantic import BaseModel, Field
from typing import Optional, List, Dict, Any
from datetime import datetime
from enum import Enum

class AnalysisStatus(str, Enum):
    PENDING = "pending"
    PROCESSING = "processing"
    COMPLETED = "completed"
    FAILED = "failed"

class AnalysisRequest(BaseModel):
    score_midi_url: str = Field(..., description="URL of the score MIDI file")
    performance_midi_url: str = Field(..., description="URL of the performance MIDI file")
    user_id: Optional[str] = Field(None, description="User ID for tracking")
    session_id: Optional[str] = Field(None, description="Training session ID")
    analysis_type: str = Field("full", description="Type of analysis: full, basic, measures")

class AnalysisResponse(BaseModel):
    job_id: str = Field(..., description="Unique job identifier")
    status: AnalysisStatus = Field(..., description="Current job status")
    message: str = Field(..., description="Status message")
    created_at: datetime = Field(..., description="Job creation timestamp")

class MeasureMetrics(BaseModel):
    measure: int = Field(..., description="Measure number")
    accuracy: float = Field(..., description="Note accuracy (0-1)")
    notes_played: int = Field(..., description="Number of notes played")
    notes_expected: int = Field(..., description="Number of expected notes")
    timing_deviation: float = Field(..., description="Average timing deviation")
    pitch_accuracy: float = Field(..., description="Pitch accuracy (0-1)")
    completeness: float = Field(..., description="Measure completeness (0-1)")
    issues: List[str] = Field(default_factory=list, description="Identified issues")
    suggestions: List[str] = Field(default_factory=list, description="Practice suggestions")

class PerformanceMetrics(BaseModel):
    overall_score: float = Field(..., description="Overall performance score (0-1)")
    performance_level: str = Field(..., description="Performance assessment level")

    # Detailed metrics
    onset_metrics: Dict[str, float] = Field(..., description="Onset detection metrics")
    pitch_metrics: Dict[str, float] = Field(..., description="Pitch accuracy metrics")
    rhythm_metrics: Dict[str, float] = Field(..., description="Rhythm and timing metrics")
    expressivity_metrics: Dict[str, float] = Field(..., description="Expressivity metrics")

    # Note statistics
    note_count: Dict[str, int] = Field(..., description="Note count statistics")

class AnalysisResult(BaseModel):
    job_id: str = Field(..., description="Unique job identifier")
    status: AnalysisStatus = Field(..., description="Final job status")
    performance_metrics: Optional[PerformanceMetrics] = Field(None, description="Performance metrics")
    measure_metrics: Optional[Dict[int, MeasureMetrics]] = Field(None, description="Measure-level metrics")
    problem_measures: Optional[List[Dict[str, Any]]] = Field(None, description="Measures needing improvement")
    alignment_data: Optional[List[Dict[str, Any]]] = Field(None, description="Score-performance alignment")
    error_message: Optional[str] = Field(None, description="Error message if failed")
    processing_time: Optional[float] = Field(None, description="Processing time in seconds")
    created_at: datetime = Field(..., description="Job creation timestamp")
    completed_at: Optional[datetime] = Field(None, description="Job completion timestamp")

class RealTimeUpdate(BaseModel):
    current_measure: int = Field(..., description="Current measure in performance")
    confidence: float = Field(..., description="Alignment confidence (0-1)")
    expected_notes: List[int] = Field(..., description="Expected pitches in current position")
    played_notes: List[int] = Field(..., description="Recently played pitches")
    timing_deviation: float = Field(..., description="Current timing deviation")
    position: float = Field(..., description="Current position in score (seconds)")
