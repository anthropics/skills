from fastapi import APIRouter, HTTPException, BackgroundTasks, WebSocket, WebSocketDisconnect
import uuid
from datetime import datetime
import json
import asyncio
from typing import Dict

from app.schemas.analysis import (
    AnalysisRequest, AnalysisResponse, AnalysisResult, AnalysisStatus, RealTimeUpdate
)
from app.analysis.score_following import ScoreFollower
from app.analysis.metrics import PerformanceMetrics
from app.analysis.measure_analysis import MeasureAnalyzer

router = APIRouter()

# In-memory store for analysis jobs and real-time sessions
analysis_jobs: Dict[str, Dict] = {}
real_time_sessions: Dict[str, ScoreFollower] = {}

@router.post("/analyze", response_model=AnalysisResponse)
async def create_analysis(
    request: AnalysisRequest,
    background_tasks: BackgroundTasks
):
    """Create a new performance analysis job"""

    job_id = str(uuid.uuid4())

    # Store job metadata
    analysis_jobs[job_id] = {
        "status": AnalysisStatus.PENDING,
        "created_at": datetime.utcnow(),
        "request": request.dict(),
        "result": None
    }

    # TODO: Start Celery task when available
    # For now, mark as pending
    # analyze_performance_task.delay(
    #     job_id=job_id,
    #     score_midi_url=request.score_midi_url,
    #     performance_midi_url=request.performance_midi_url,
    #     user_id=request.user_id,
    #     session_id=request.session_id,
    #     analysis_type=request.analysis_type
    # )

    return AnalysisResponse(
        job_id=job_id,
        status=AnalysisStatus.PENDING,
        message="Analysis job started",
        created_at=datetime.utcnow()
    )

@router.get("/analyze/{job_id}", response_model=AnalysisResult)
async def get_analysis_status(job_id: str):
    """Get analysis job status and result"""

    job = analysis_jobs.get(job_id)
    if not job:
        raise HTTPException(status_code=404, detail="Job not found")

    if job["status"] == AnalysisStatus.COMPLETED and job["result"]:
        return AnalysisResult(
            job_id=job_id,
            status=job["status"],
            performance_metrics=job["result"].get("performance_metrics"),
            measure_metrics=job["result"].get("measure_metrics"),
            problem_measures=job["result"].get("problem_measures"),
            alignment_data=job["result"].get("alignment_data"),
            processing_time=job["result"].get("processing_time"),
            created_at=job["created_at"],
            completed_at=datetime.utcnow()
        )
    else:
        return AnalysisResult(
            job_id=job_id,
            status=job["status"],
            created_at=job["created_at"]
        )

@router.websocket("/ws/realtime/{session_id}")
async def websocket_realtime_analysis(websocket: WebSocket, session_id: str):
    """WebSocket for real-time score following and analysis"""
    await websocket.accept()

    try:
        # Initialize score follower for this session
        score_follower = None

        while True:
            # Receive performance data from client
            data = await websocket.receive_text()
            message = json.loads(data)

            if message["type"] == "initialize":
                # Initialize score follower with provided MIDI
                score_url = message["score_url"]
                score_follower = ScoreFollower(score_midi_path=score_url)
                real_time_sessions[session_id] = score_follower

                await websocket.send_text(json.dumps({
                    "type": "initialized",
                    "message": "Score follower initialized"
                }))

            elif message["type"] == "performance_notes" and score_follower:
                # Update with new performance notes
                current_notes = message["notes"]
                update = score_follower.update_real_time(current_notes)

                # Send real-time update to client
                realtime_update = RealTimeUpdate(
                    current_measure=update.get('measure', 0),
                    confidence=update.get('confidence', 0.0),
                    expected_notes=update.get('expected_notes', []),
                    played_notes=update.get('played_notes', []),
                    timing_deviation=update.get('timing_deviation', 0.0),
                    position=update.get('position', 0.0)
                )

                await websocket.send_text(json.dumps({
                    "type": "realtime_update",
                    "data": realtime_update.dict()
                }))

            elif message["type"] == "alignment_request" and score_follower:
                # Perform full alignment analysis
                performance_notes = message["performance_notes"]
                alignment_result = score_follower.align_performance(performance_notes)

                if alignment_result["success"]:
                    # Compute comprehensive metrics
                    metrics_calculator = PerformanceMetrics(
                        score_follower.score_notes,
                        performance_notes
                    )
                    assessment = metrics_calculator.compute_overall_assessment(
                        alignment_result["alignment"]
                    )

                    await websocket.send_text(json.dumps({
                        "type": "alignment_result",
                        "data": {
                            "alignment": alignment_result,
                            "assessment": assessment
                        }
                    }))

            await asyncio.sleep(0.1)  # Prevent overwhelming the client

    except WebSocketDisconnect:
        # Clean up session
        if session_id in real_time_sessions:
            del real_time_sessions[session_id]
    except Exception as e:
        await websocket.send_text(json.dumps({
            "type": "error",
            "message": str(e)
        }))

@router.post("/analyze/batch")
async def batch_analysis(requests: list[AnalysisRequest]):
    """Batch analysis of multiple performances"""
    job_ids = []

    for request in requests:
        job_id = str(uuid.uuid4())
        analysis_jobs[job_id] = {
            "status": AnalysisStatus.PENDING,
            "created_at": datetime.utcnow(),
            "request": request.dict(),
            "result": None
        }

        # TODO: Start Celery task when available
        # analyze_performance_task.delay(...)

        job_ids.append(job_id)

    return {"job_ids": job_ids, "message": f"Started {len(job_ids)} analysis jobs"}

@router.get("/sessions/{session_id}/measures")
async def get_session_measures(session_id: str):
    """Get measure-level analysis for a session"""
    if session_id not in real_time_sessions:
        raise HTTPException(status_code=404, detail="Session not found")

    score_follower = real_time_sessions[session_id]
    analyzer = MeasureAnalyzer(score_follower.score_notes)

    # This would typically use stored performance data
    # For now, return measure structure
    measures = {}
    for measure in analyzer.measure_notes.keys():
        measures[measure] = {
            "note_count": len(analyzer.measure_notes[measure]),
            "expected_notes": [note['pitch'] for note in analyzer.measure_notes[measure]]
        }

    return {"measures": measures}
