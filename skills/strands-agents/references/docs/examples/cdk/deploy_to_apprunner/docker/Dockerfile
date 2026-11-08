FROM public.ecr.aws/docker/library/python:3.12-slim

WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y \
    git \
    && rm -rf /var/lib/apt/lists/*

# Install Python dependencies
# Copy requirements file
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy application code
COPY app/ .

# Create a non-root user to run the application
RUN useradd -m appuser
USER appuser

# Expose the port the app runs on
EXPOSE 8000

# Command to run the application with Uvicorn
# - workers: 2 worker processes (adjust based on container resources)
# - host: Listen on all interfaces
# - port: 8000
CMD ["uvicorn", "app:app", "--host", "0.0.0.0", "--port", "8000", "--workers", "2"]
