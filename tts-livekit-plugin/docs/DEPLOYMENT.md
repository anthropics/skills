# Deployment Guide

Guide for deploying the MeloTTS API server and LiveKit plugin in production.

## Table of Contents

1. [Development Setup](#development-setup)
2. [Production Deployment](#production-deployment)
3. [Docker Deployment](#docker-deployment)
4. [Cloud Deployment](#cloud-deployment)
5. [Monitoring](#monitoring)
6. [Security](#security)
7. [Scaling](#scaling)
8. [Troubleshooting](#troubleshooting)

---

## Development Setup

### Local Development

1. **Start API Server:**
```bash
cd api
pip install -r requirements.txt
python -m unidic download
python server.py
```

2. **Install Plugin:**
```bash
cd plugin
pip install -r requirements.txt
```

3. **Run Tests:**
```bash
cd examples
python test_api_client.py
```

---

## Production Deployment

### API Server Production Setup

#### 1. Install Dependencies

```bash
# Create virtual environment
python3 -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate

# Install dependencies
cd api
pip install -r requirements.txt
python -m unidic download
```

#### 2. Configure Server

Create `config.py`:

```python
import os

# Server configuration
HOST = os.getenv("TTS_HOST", "0.0.0.0")
PORT = int(os.getenv("TTS_PORT", "8000"))
WORKERS = int(os.getenv("TTS_WORKERS", "4"))
LOG_LEVEL = os.getenv("TTS_LOG_LEVEL", "info")

# TTS configuration
DEVICE = os.getenv("TTS_DEVICE", "auto")  # auto, cpu, cuda
```

#### 3. Create Production Server Script

Create `production_server.py`:

```python
import uvicorn
from config import HOST, PORT, WORKERS, LOG_LEVEL

if __name__ == "__main__":
    uvicorn.run(
        "server:app",
        host=HOST,
        port=PORT,
        workers=WORKERS,
        log_level=LOG_LEVEL,
        access_log=True,
        proxy_headers=True,
        forwarded_allow_ips="*"
    )
```

#### 4. Run with Gunicorn (Recommended)

```bash
pip install gunicorn

gunicorn server:app \
    --bind 0.0.0.0:8000 \
    --workers 4 \
    --worker-class uvicorn.workers.UvicornWorker \
    --timeout 120 \
    --access-logfile /var/log/tts/access.log \
    --error-logfile /var/log/tts/error.log
```

#### 5. Create Systemd Service

Create `/etc/systemd/system/tts-api.service`:

```ini
[Unit]
Description=MeloTTS API Server
After=network.target

[Service]
Type=notify
User=tts
Group=tts
WorkingDirectory=/opt/tts-api
Environment="PATH=/opt/tts-api/venv/bin"
ExecStart=/opt/tts-api/venv/bin/gunicorn server:app \
    --bind 0.0.0.0:8000 \
    --workers 4 \
    --worker-class uvicorn.workers.UvicornWorker \
    --timeout 120

Restart=always
RestartSec=10

[Install]
WantedBy=multi-user.target
```

Enable and start:

```bash
sudo systemctl daemon-reload
sudo systemctl enable tts-api
sudo systemctl start tts-api
sudo systemctl status tts-api
```

---

## Docker Deployment

### API Server Dockerfile

Create `api/Dockerfile`:

```dockerfile
FROM python:3.11-slim

# Install system dependencies
RUN apt-get update && apt-get install -y \
    build-essential \
    git \
    && rm -rf /var/lib/apt/lists/*

# Set working directory
WORKDIR /app

# Copy requirements
COPY requirements.txt .

# Install Python dependencies
RUN pip install --no-cache-dir -r requirements.txt

# Download unidic
RUN python -m unidic download

# Copy application
COPY server.py .

# Expose port
EXPOSE 8000

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=40s --retries=3 \
    CMD python -c "import requests; requests.get('http://localhost:8000/')"

# Run server
CMD ["python", "-m", "uvicorn", "server:app", "--host", "0.0.0.0", "--port", "8000"]
```

### Build and Run

```bash
# Build image
cd api
docker build -t melotts-api:latest .

# Run container
docker run -d \
    --name melotts-api \
    -p 8000:8000 \
    --restart unless-stopped \
    melotts-api:latest
```

### Docker Compose

Create `docker-compose.yml`:

```yaml
version: '3.8'

services:
  tts-api:
    build:
      context: ./api
      dockerfile: Dockerfile
    image: melotts-api:latest
    container_name: melotts-api
    ports:
      - "8000:8000"
    environment:
      - TTS_DEVICE=cpu
      - TTS_WORKERS=4
    volumes:
      - tts-cache:/root/.cache
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8000/"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 40s
    deploy:
      resources:
        limits:
          cpus: '4'
          memory: 4G
        reservations:
          cpus: '2'
          memory: 2G

volumes:
  tts-cache:
```

Run with:

```bash
docker-compose up -d
```

### Docker with GPU Support

Update `docker-compose.yml`:

```yaml
services:
  tts-api:
    # ... other configuration ...
    runtime: nvidia
    environment:
      - TTS_DEVICE=cuda
      - NVIDIA_VISIBLE_DEVICES=all
    deploy:
      resources:
        reservations:
          devices:
            - driver: nvidia
              count: 1
              capabilities: [gpu]
```

---

## Cloud Deployment

### AWS Deployment

#### Using EC2

1. **Launch EC2 Instance:**
   - Instance type: `t3.medium` (CPU) or `g4dn.xlarge` (GPU)
   - AMI: Ubuntu 22.04 LTS
   - Storage: 20GB minimum

2. **Setup:**
```bash
# Update system
sudo apt update && sudo apt upgrade -y

# Install Docker
curl -fsSL https://get.docker.com -o get-docker.sh
sudo sh get-docker.sh

# Clone repository
git clone <your-repo>
cd tts-livekit-plugin

# Deploy
docker-compose up -d
```

3. **Configure Security Group:**
   - Allow inbound TCP 8000 from your LiveKit agents

#### Using ECS (Elastic Container Service)

1. **Push Image to ECR:**
```bash
aws ecr create-repository --repository-name melotts-api

docker tag melotts-api:latest <account-id>.dkr.ecr.<region>.amazonaws.com/melotts-api:latest

docker push <account-id>.dkr.ecr.<region>.amazonaws.com/melotts-api:latest
```

2. **Create ECS Task Definition**
3. **Create ECS Service**
4. **Configure Application Load Balancer**

### Google Cloud Platform

#### Using Compute Engine

Similar to AWS EC2 - use Docker deployment.

#### Using Cloud Run

```bash
# Build and push
gcloud builds submit --tag gcr.io/PROJECT_ID/melotts-api

# Deploy
gcloud run deploy melotts-api \
    --image gcr.io/PROJECT_ID/melotts-api \
    --platform managed \
    --region us-central1 \
    --memory 4Gi \
    --cpu 2 \
    --timeout 300 \
    --allow-unauthenticated
```

### Azure

#### Using Container Instances

```bash
# Create resource group
az group create --name tts-rg --location eastus

# Create container
az container create \
    --resource-group tts-rg \
    --name melotts-api \
    --image melotts-api:latest \
    --dns-name-label melotts-api \
    --ports 8000 \
    --cpu 2 \
    --memory 4
```

### Kubernetes

Create `k8s/deployment.yaml`:

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: melotts-api
spec:
  replicas: 3
  selector:
    matchLabels:
      app: melotts-api
  template:
    metadata:
      labels:
        app: melotts-api
    spec:
      containers:
      - name: melotts-api
        image: melotts-api:latest
        ports:
        - containerPort: 8000
        resources:
          requests:
            memory: "2Gi"
            cpu: "1000m"
          limits:
            memory: "4Gi"
            cpu: "2000m"
        livenessProbe:
          httpGet:
            path: /
            port: 8000
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /
            port: 8000
          initialDelaySeconds: 10
          periodSeconds: 5
---
apiVersion: v1
kind: Service
metadata:
  name: melotts-api
spec:
  selector:
    app: melotts-api
  ports:
  - protocol: TCP
    port: 80
    targetPort: 8000
  type: LoadBalancer
```

Deploy:

```bash
kubectl apply -f k8s/deployment.yaml
```

---

## Monitoring

### Logging

Configure structured logging in `server.py`:

```python
import logging
import json

class JSONFormatter(logging.Formatter):
    def format(self, record):
        return json.dumps({
            'timestamp': self.formatTime(record),
            'level': record.levelname,
            'message': record.getMessage(),
            'module': record.module,
        })

handler = logging.StreamHandler()
handler.setFormatter(JSONFormatter())
logging.getLogger().addHandler(handler)
```

### Metrics

Add Prometheus metrics:

```bash
pip install prometheus-fastapi-instrumentator
```

```python
from prometheus_fastapi_instrumentator import Instrumentator

app = FastAPI()
Instrumentator().instrument(app).expose(app)
```

Access metrics at `/metrics`.

### Health Checks

The server provides health check at `/`.

Configure monitoring:

```bash
# Simple check
curl http://localhost:8000/

# With alerting (example with UptimeRobot, Pingdom, etc.)
```

### Application Performance Monitoring (APM)

#### Using New Relic

```bash
pip install newrelic

# Run with New Relic
NEW_RELIC_CONFIG_FILE=newrelic.ini newrelic-admin run-program python server.py
```

#### Using DataDog

```bash
pip install ddtrace

# Run with DataDog
ddtrace-run python server.py
```

---

## Security

### API Authentication

Add API key authentication:

```python
from fastapi import Security, HTTPException
from fastapi.security import APIKeyHeader

API_KEY = os.getenv("API_KEY", "your-secret-key")
api_key_header = APIKeyHeader(name="X-API-Key")

def verify_api_key(api_key: str = Security(api_key_header)):
    if api_key != API_KEY:
        raise HTTPException(status_code=403, detail="Invalid API key")
    return api_key

@app.post("/synthesize")
async def synthesize(request: TTSRequest, api_key: str = Security(verify_api_key)):
    # ... synthesis logic
```

### HTTPS/TLS

#### Using Nginx Reverse Proxy

```nginx
server {
    listen 443 ssl http2;
    server_name tts.example.com;

    ssl_certificate /etc/ssl/certs/tts.crt;
    ssl_certificate_key /etc/ssl/private/tts.key;

    location / {
        proxy_pass http://localhost:8000;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto $scheme;
    }
}
```

#### Using Let's Encrypt

```bash
sudo apt install certbot python3-certbot-nginx
sudo certbot --nginx -d tts.example.com
```

### Rate Limiting

Add rate limiting:

```bash
pip install slowapi
```

```python
from slowapi import Limiter, _rate_limit_exceeded_handler
from slowapi.util import get_remote_address
from slowapi.errors import RateLimitExceeded

limiter = Limiter(key_func=get_remote_address)
app.state.limiter = limiter
app.add_exception_handler(RateLimitExceeded, _rate_limit_exceeded_handler)

@app.post("/synthesize")
@limiter.limit("10/minute")
async def synthesize(request: Request, tts_request: TTSRequest):
    # ... synthesis logic
```

### CORS Configuration

```python
from fastapi.middleware.cors import CORSMiddleware

app.add_middleware(
    CORSMiddleware,
    allow_origins=["https://your-livekit-domain.com"],
    allow_credentials=True,
    allow_methods=["POST", "GET"],
    allow_headers=["*"],
)
```

---

## Scaling

### Horizontal Scaling

#### Load Balancer Configuration

Using Nginx:

```nginx
upstream tts_backend {
    least_conn;
    server tts1.example.com:8000;
    server tts2.example.com:8000;
    server tts3.example.com:8000;
}

server {
    listen 80;
    server_name tts.example.com;

    location / {
        proxy_pass http://tts_backend;
    }
}
```

#### Auto-Scaling (Kubernetes)

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: melotts-api-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: melotts-api
  minReplicas: 2
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
```

### Vertical Scaling

Increase resources:
- More CPU cores
- More RAM
- GPU acceleration

### Caching

Implement Redis caching:

```python
import redis
import hashlib

redis_client = redis.Redis(host='localhost', port=6379, db=0)

def get_cache_key(text, language, speaker, speed):
    data = f"{text}:{language}:{speaker}:{speed}"
    return hashlib.md5(data.encode()).hexdigest()

@app.post("/synthesize")
async def synthesize(request: TTSRequest):
    cache_key = get_cache_key(
        request.text, request.language,
        request.speaker, request.speed
    )

    # Check cache
    cached = redis_client.get(cache_key)
    if cached:
        return Response(content=cached, media_type="audio/wav")

    # Generate audio
    audio_data = await generate_audio(request)

    # Cache result (expire after 1 hour)
    redis_client.setex(cache_key, 3600, audio_data)

    return Response(content=audio_data, media_type="audio/wav")
```

---

## Troubleshooting

### High Memory Usage

**Solutions:**
- Reduce worker count
- Implement request queuing
- Use CPU mode instead of loading models in memory
- Add swap space

### Slow Response Times

**Checks:**
- CPU/GPU utilization
- Network latency
- Concurrent request count

**Solutions:**
- Add more workers
- Enable GPU acceleration
- Scale horizontally
- Implement caching

### Connection Refused

**Checks:**
- Server is running: `systemctl status tts-api`
- Port is open: `netstat -tulpn | grep 8000`
- Firewall rules: `sudo ufw status`

### Out of Disk Space

**Solutions:**
- Clear logs: `sudo journalctl --vacuum-time=7d`
- Monitor disk usage: `df -h`
- Implement log rotation

---

## Backup and Recovery

### Backup Configuration

```bash
# Backup configuration files
tar -czf tts-config-backup.tar.gz /opt/tts-api/config.py

# Backup logs
tar -czf tts-logs-backup.tar.gz /var/log/tts/
```

### Disaster Recovery

1. **Document Configuration:** Keep infrastructure as code
2. **Automate Deployment:** Use CI/CD pipelines
3. **Monitor Health:** Set up alerts
4. **Test Recovery:** Regularly test deployment from scratch

---

## Maintenance

### Updates

```bash
# Update dependencies
pip install --upgrade -r requirements.txt

# Restart service
sudo systemctl restart tts-api
```

### Log Rotation

Configure `/etc/logrotate.d/tts-api`:

```
/var/log/tts/*.log {
    daily
    missingok
    rotate 14
    compress
    delaycompress
    notifempty
    create 0640 tts tts
    sharedscripts
    postrotate
        systemctl reload tts-api > /dev/null 2>&1 || true
    endscript
}
```

---

## Performance Tuning

### System Tuning

```bash
# Increase file descriptors
echo "* soft nofile 65536" >> /etc/security/limits.conf
echo "* hard nofile 65536" >> /etc/security/limits.conf

# Optimize network
echo "net.core.somaxconn = 65536" >> /etc/sysctl.conf
echo "net.ipv4.tcp_max_syn_backlog = 65536" >> /etc/sysctl.conf
sysctl -p
```

### Application Tuning

- Adjust worker count based on CPU cores
- Enable keep-alive connections
- Tune timeout values
- Use HTTP/2

---

## Cost Optimization

1. **Right-Size Instances:** Start small, scale as needed
2. **Use Spot/Preemptible Instances:** For non-critical workloads
3. **Implement Caching:** Reduce computation costs
4. **Auto-Scaling:** Scale down during low usage
5. **Reserved Instances:** For predictable workloads

---

## Compliance

### GDPR Considerations

- Don't log sensitive user data
- Implement data retention policies
- Provide data deletion mechanisms
- Document data processing

### Security Best Practices

- Keep dependencies updated
- Use secrets management
- Enable audit logging
- Regular security scans

---

## Support Resources

- [FastAPI Documentation](https://fastapi.tiangolo.com/)
- [MeloTTS GitHub](https://github.com/myshell-ai/MeloTTS)
- [LiveKit Documentation](https://docs.livekit.io/)
- [Docker Documentation](https://docs.docker.com/)
