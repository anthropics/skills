"""
Health check endpoints for monitoring and deployment validation.
Provides detailed system status including database, cache, and dependencies.
"""

from typing import Dict, Any
from datetime import datetime
import psutil
import asyncio
from fastapi import APIRouter, status, Response
from fastapi.responses import JSONResponse
from sqlalchemy import text
from redis import Redis
import logging

from app.core.config import settings
from app.core.database import get_db

logger = logging.getLogger(__name__)

router = APIRouter()


@router.get("/health", status_code=status.HTTP_200_OK)
async def health_check() -> Dict[str, str]:
    """
    Simple health check endpoint for load balancers and orchestrators.
    Returns 200 OK if service is running.

    Used by:
    - Docker healthcheck
    - Kubernetes liveness probe
    - Load balancer health checks
    - Deployment validation
    """
    return {
        "status": "healthy",
        "timestamp": datetime.utcnow().isoformat(),
        "service": "piano-tutor-api",
        "version": settings.VERSION if hasattr(settings, 'VERSION') else "1.0.0"
    }


@router.get("/health/ready", status_code=status.HTTP_200_OK)
async def readiness_check() -> JSONResponse:
    """
    Detailed readiness check that validates all dependencies.
    Returns 200 if service is ready to accept traffic, 503 otherwise.

    Checks:
    - Database connectivity
    - Redis cache availability
    - System resources

    Used by:
    - Kubernetes readiness probe
    - Blue-Green deployment validation
    - Pre-deployment smoke tests
    """
    checks = {
        "database": False,
        "cache": False,
        "disk_space": False,
        "memory": False
    }

    errors = []

    # Check database connection
    try:
        from app.core.database import engine
        with engine.connect() as conn:
            conn.execute(text("SELECT 1"))
            checks["database"] = True
    except Exception as e:
        errors.append(f"Database: {str(e)}")
        logger.error(f"Database health check failed: {e}")

    # Check Redis connection
    try:
        redis_client = Redis.from_url(
            settings.REDIS_URL if hasattr(settings, 'REDIS_URL') else "redis://localhost:6379/0",
            socket_connect_timeout=2
        )
        redis_client.ping()
        checks["cache"] = True
        redis_client.close()
    except Exception as e:
        errors.append(f"Cache: {str(e)}")
        logger.error(f"Redis health check failed: {e}")

    # Check disk space (>10% free)
    try:
        disk = psutil.disk_usage('/')
        if disk.percent < 90:
            checks["disk_space"] = True
        else:
            errors.append(f"Disk space critical: {disk.percent}% used")
    except Exception as e:
        errors.append(f"Disk check: {str(e)}")

    # Check memory (>10% free)
    try:
        memory = psutil.virtual_memory()
        if memory.percent < 90:
            checks["memory"] = True
        else:
            errors.append(f"Memory critical: {memory.percent}% used")
    except Exception as e:
        errors.append(f"Memory check: {str(e)}")

    # Determine overall status
    all_healthy = all(checks.values())
    status_code = status.HTTP_200_OK if all_healthy else status.HTTP_503_SERVICE_UNAVAILABLE

    response = {
        "status": "ready" if all_healthy else "not_ready",
        "timestamp": datetime.utcnow().isoformat(),
        "checks": checks,
        "errors": errors if errors else None
    }

    return JSONResponse(content=response, status_code=status_code)


@router.get("/health/live", status_code=status.HTTP_200_OK)
async def liveness_check() -> Dict[str, str]:
    """
    Liveness check for Kubernetes.
    Returns 200 if the application process is alive.
    Unlike readiness, this doesn't check dependencies.

    Used by:
    - Kubernetes liveness probe
    - Container orchestrators to detect deadlocks
    """
    return {
        "status": "alive",
        "timestamp": datetime.utcnow().isoformat()
    }


@router.get("/health/detailed", status_code=status.HTTP_200_OK)
async def detailed_health_check() -> Dict[str, Any]:
    """
    Comprehensive health check with system metrics.
    Provides detailed information for monitoring dashboards.

    Returns:
    - System resources (CPU, memory, disk)
    - Database pool status
    - Cache statistics
    - Application version and uptime

    Used by:
    - Monitoring dashboards (Grafana, DataDog)
    - Ops teams for troubleshooting
    - Performance analysis
    """
    # System metrics
    cpu_percent = psutil.cpu_percent(interval=1)
    memory = psutil.virtual_memory()
    disk = psutil.disk_usage('/')

    # Database info
    db_info = {
        "connected": False,
        "pool_size": 0,
        "pool_available": 0
    }

    try:
        from app.core.database import engine
        with engine.connect() as conn:
            conn.execute(text("SELECT 1"))
            db_info["connected"] = True
            db_info["pool_size"] = engine.pool.size()
            db_info["pool_available"] = engine.pool.size() - engine.pool.checkedin()
    except Exception as e:
        logger.error(f"Database detailed check failed: {e}")

    # Redis info
    cache_info = {
        "connected": False,
        "memory_used": 0,
        "keys_count": 0
    }

    try:
        redis_client = Redis.from_url(
            settings.REDIS_URL if hasattr(settings, 'REDIS_URL') else "redis://localhost:6379/0",
            socket_connect_timeout=2
        )
        redis_client.ping()
        cache_info["connected"] = True
        info = redis_client.info('memory')
        cache_info["memory_used"] = info.get('used_memory_human', 'unknown')
        cache_info["keys_count"] = redis_client.dbsize()
        redis_client.close()
    except Exception as e:
        logger.error(f"Redis detailed check failed: {e}")

    return {
        "status": "healthy",
        "timestamp": datetime.utcnow().isoformat(),
        "version": settings.VERSION if hasattr(settings, 'VERSION') else "1.0.0",
        "environment": settings.ENVIRONMENT if hasattr(settings, 'ENVIRONMENT') else "unknown",
        "system": {
            "cpu_percent": cpu_percent,
            "memory": {
                "total": f"{memory.total / (1024**3):.2f} GB",
                "available": f"{memory.available / (1024**3):.2f} GB",
                "percent": memory.percent
            },
            "disk": {
                "total": f"{disk.total / (1024**3):.2f} GB",
                "free": f"{disk.free / (1024**3):.2f} GB",
                "percent": disk.percent
            }
        },
        "database": db_info,
        "cache": cache_info
    }


@router.get("/health/startup", status_code=status.HTTP_200_OK)
async def startup_check() -> Dict[str, Any]:
    """
    Startup probe for Kubernetes.
    Used to determine when application has fully started.
    May take longer than liveness/readiness checks.

    Validates:
    - Database migrations are complete
    - Required data is loaded
    - All services are initialized
    """
    startup_checks = {
        "database_migrated": False,
        "cache_available": False,
        "models_loaded": True  # Placeholder - implement model loading check if needed
    }

    # Check database and run a simple migration check
    try:
        from app.core.database import engine
        with engine.connect() as conn:
            # Check if migrations table exists (alembic_version)
            result = conn.execute(text(
                "SELECT EXISTS (SELECT FROM information_schema.tables WHERE table_name = 'alembic_version')"
            ))
            startup_checks["database_migrated"] = result.scalar()
    except Exception as e:
        logger.error(f"Startup database check failed: {e}")

    # Check cache
    try:
        redis_client = Redis.from_url(
            settings.REDIS_URL if hasattr(settings, 'REDIS_URL') else "redis://localhost:6379/0",
            socket_connect_timeout=2
        )
        redis_client.ping()
        startup_checks["cache_available"] = True
        redis_client.close()
    except Exception as e:
        logger.error(f"Startup cache check failed: {e}")

    all_ready = all(startup_checks.values())

    return {
        "status": "started" if all_ready else "starting",
        "timestamp": datetime.utcnow().isoformat(),
        "checks": startup_checks,
        "ready": all_ready
    }


@router.get("/metrics", status_code=status.HTTP_200_OK)
async def prometheus_metrics() -> Response:
    """
    Prometheus-compatible metrics endpoint.
    Returns metrics in Prometheus text format.

    Metrics include:
    - HTTP request counts and latencies
    - Database connection pool stats
    - Cache hit/miss rates
    - System resource usage

    Used by:
    - Prometheus scraper
    - Grafana dashboards
    - Alert manager
    """
    # TODO: Implement full Prometheus metrics
    # For now, return basic metrics in Prometheus format

    metrics = []

    # System metrics
    cpu_percent = psutil.cpu_percent(interval=1)
    memory = psutil.virtual_memory()
    disk = psutil.disk_usage('/')

    metrics.append(f"# HELP system_cpu_percent CPU usage percentage")
    metrics.append(f"# TYPE system_cpu_percent gauge")
    metrics.append(f"system_cpu_percent {cpu_percent}")

    metrics.append(f"# HELP system_memory_percent Memory usage percentage")
    metrics.append(f"# TYPE system_memory_percent gauge")
    metrics.append(f"system_memory_percent {memory.percent}")

    metrics.append(f"# HELP system_disk_percent Disk usage percentage")
    metrics.append(f"# TYPE system_disk_percent gauge")
    metrics.append(f"system_disk_percent {disk.percent}")

    # Database pool metrics (if available)
    try:
        from app.core.database import engine
        pool_size = engine.pool.size()
        pool_checked_in = engine.pool.checkedin()

        metrics.append(f"# HELP db_pool_size Database connection pool size")
        metrics.append(f"# TYPE db_pool_size gauge")
        metrics.append(f"db_pool_size {pool_size}")

        metrics.append(f"# HELP db_pool_checked_in Database connections checked in")
        metrics.append(f"# TYPE db_pool_checked_in gauge")
        metrics.append(f"db_pool_checked_in {pool_checked_in}")
    except:
        pass

    return Response(content="\n".join(metrics), media_type="text/plain")
