from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from contextlib import asynccontextmanager

from app.api.endpoints import analysis, health

# Configuration
API_V1_STR = "/api/v1"

# Application lifespan
@asynccontextmanager
async def lifespan(app: FastAPI):
    # Startup
    print("Starting Music Training Platform API...")
    yield
    # Shutdown
    print("Shutting down Music Training Platform API...")

# Create FastAPI application
app = FastAPI(
    title="Music Training Platform API",
    description="Backend API for Score Following & Performance Analysis",
    version="0.1.0",
    lifespan=lifespan
)

# CORS middleware
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # Configure appropriately for production
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Include routers
app.include_router(
    analysis.router,
    prefix=f"{API_V1_STR}/analysis",
    tags=["analysis"]
)

# Include health check router (no prefix for root-level health endpoints)
app.include_router(
    health.router,
    tags=["health"]
)

# Root endpoint
@app.get("/")
async def root():
    """Root endpoint with API information"""
    return {
        "message": "Music Training Platform API",
        "version": "0.1.0",
        "docs": "/docs",
        "health": "/health"
    }

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(
        "app.main:app",
        host="0.0.0.0",
        port=8000,
        reload=True
    )
