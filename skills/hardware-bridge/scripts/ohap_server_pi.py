#!/usr/bin/env python3
"""OHAP Server — Reference implementation for Raspberry Pi.

Implements the Open Hardware Agent Protocol (5 endpoints).
Run on any Pi with: python3 ohap_server_pi.py

Optional sensors: DHT22 (pip install adafruit-circuitpython-dht)
"""

import json
import time
import socket
import psutil
from http.server import HTTPServer, BaseHTTPRequestHandler
from datetime import datetime, timezone

# ── Configuration ────────────────────────────────────────────
DEVICE_NAME = "My Raspberry Pi"
DEVICE_TYPE = "environmental"
DEVICE_LOCATION = "Home"
PORT = 8421
TOKEN = None  # Set to a string to require auth, e.g. "my-secret-token"
START_TIME = time.time()

# ── Sensor Registry ──────────────────────────────────────────
SENSORS = [
    {"id": "cpu_temp", "name": "CPU Temperature", "type": "temperature", "unit": "celsius"},
    {"id": "cpu_usage", "name": "CPU Usage", "type": "percent", "unit": "percent"},
    {"id": "memory", "name": "Memory Usage", "type": "percent", "unit": "percent"},
    {"id": "disk", "name": "Disk Usage", "type": "percent", "unit": "percent"},
]

# Try to import DHT sensor
try:
    import adafruit_dht
    import board
    dht = adafruit_dht.DHT22(board.D4)
    SENSORS.append({"id": "dht_temp", "name": "Room Temperature", "type": "temperature",
                    "unit": "celsius", "precision": 0.1})
    SENSORS.append({"id": "dht_humidity", "name": "Room Humidity", "type": "humidity",
                    "unit": "percent", "precision": 1})
    HAS_DHT = True
except (ImportError, Exception):
    HAS_DHT = False
    dht = None

# Try to import GPIO
try:
    import RPi.GPIO as GPIO
    GPIO.setmode(GPIO.BCM)
    HAS_GPIO = True
except ImportError:
    HAS_GPIO = False


def read_sensor(sensor_id: str) -> dict:
    ts = datetime.now(timezone.utc).isoformat()
    try:
        if sensor_id == "cpu_temp":
            temp = psutil.sensors_temperatures()
            val = temp["cpu_thermal"][0].current if "cpu_thermal" in temp else 0
            return {"sensor_id": sensor_id, "value": round(val, 1), "unit": "celsius",
                    "timestamp": ts, "quality": "good"}
        elif sensor_id == "cpu_usage":
            return {"sensor_id": sensor_id, "value": psutil.cpu_percent(interval=0.5),
                    "unit": "percent", "timestamp": ts, "quality": "good"}
        elif sensor_id == "memory":
            return {"sensor_id": sensor_id, "value": round(psutil.virtual_memory().percent, 1),
                    "unit": "percent", "timestamp": ts, "quality": "good"}
        elif sensor_id == "disk":
            return {"sensor_id": sensor_id, "value": round(psutil.disk_usage("/").percent, 1),
                    "unit": "percent", "timestamp": ts, "quality": "good"}
        elif sensor_id == "dht_temp" and HAS_DHT:
            return {"sensor_id": sensor_id, "value": round(dht.temperature, 1),
                    "unit": "celsius", "timestamp": ts, "quality": "good"}
        elif sensor_id == "dht_humidity" and HAS_DHT:
            return {"sensor_id": sensor_id, "value": round(dht.humidity, 1),
                    "unit": "percent", "timestamp": ts, "quality": "good"}
        else:
            return {"sensor_id": sensor_id, "error": "unknown sensor", "quality": "error"}
    except Exception as e:
        return {"sensor_id": sensor_id, "error": str(e), "quality": "error"}


class OHAPHandler(BaseHTTPRequestHandler):
    def log_message(self, format, *args): pass  # Suppress default logging

    def _auth_ok(self):
        if not TOKEN:
            return True
        auth = self.headers.get("Authorization", "")
        return auth == f"Bearer {TOKEN}"

    def _json(self, data, code=200):
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(json.dumps(data).encode())

    def do_GET(self):
        if not self._auth_ok():
            return self._json({"error": "unauthorized"}, 401)

        if self.path == "/agent/info":
            self._json({
                "name": DEVICE_NAME,
                "type": DEVICE_TYPE,
                "version": "1.0",
                "protocol": "ohap",
                "capabilities": [s["type"] for s in SENSORS],
                "description": f"Raspberry Pi running OHAP server",
                "location": DEVICE_LOCATION,
                "uptime_seconds": int(time.time() - START_TIME),
            })

        elif self.path == "/agent/sensors":
            self._json({"sensors": SENSORS})

        elif self.path == "/agent/read/all":
            readings = [read_sensor(s["id"]) for s in SENSORS]
            self._json({"readings": readings,
                        "timestamp": datetime.now(timezone.utc).isoformat()})

        elif self.path.startswith("/agent/read/"):
            sensor_id = self.path.split("/")[-1]
            self._json(read_sensor(sensor_id))

        elif self.path == "/agent/health":
            self._json({
                "status": "healthy",
                "uptime_seconds": int(time.time() - START_TIME),
                "cpu_percent": psutil.cpu_percent(interval=0.5),
                "memory_percent": round(psutil.virtual_memory().percent, 1),
                "disk_percent": round(psutil.disk_usage("/").percent, 1),
                "hostname": socket.gethostname(),
                "ip": socket.gethostbyname(socket.gethostname()),
                "errors": [],
            })
        else:
            self._json({"error": "not found"}, 404)

    def do_POST(self):
        if not self._auth_ok():
            return self._json({"error": "unauthorized"}, 401)

        if self.path == "/agent/command":
            length = int(self.headers.get("Content-Length", 0))
            body = json.loads(self.rfile.read(length)) if length else {}
            cmd = body.get("command", "")
            params = body.get("params", {})

            if cmd == "set_gpio" and HAS_GPIO:
                pin = params.get("pin")
                state = params.get("state", "low")
                GPIO.setup(pin, GPIO.OUT)
                GPIO.output(pin, GPIO.HIGH if state == "high" else GPIO.LOW)
                self._json({"status": "ok", "result": f"GPIO {pin} set to {state.upper()}"})
            elif cmd == "read_gpio" and HAS_GPIO:
                pin = params.get("pin")
                GPIO.setup(pin, GPIO.IN)
                val = GPIO.input(pin)
                self._json({"status": "ok", "result": {"pin": pin, "value": val}})
            elif cmd == "reboot":
                self._json({"status": "ok", "result": "Rebooting in 5 seconds"})
                import subprocess
                subprocess.Popen(["sudo", "shutdown", "-r", "+0.1"])
            else:
                self._json({"status": "error", "result": f"Unknown command: {cmd}"}, 400)
        else:
            self._json({"error": "not found"}, 404)


def register_mdns():
    """Announce this device via mDNS so clients can discover it."""
    try:
        from zeroconf import ServiceInfo, Zeroconf
        import socket
        ip = socket.gethostbyname(socket.gethostname())
        info = ServiceInfo(
            "_ohap._tcp.local.",
            f"{DEVICE_NAME}._ohap._tcp.local.",
            addresses=[socket.inet_aton(ip)],
            port=PORT,
            properties={"type": DEVICE_TYPE, "version": "1.0"},
        )
        zc = Zeroconf()
        zc.register_service(info)
        return zc
    except ImportError:
        return None


if __name__ == "__main__":
    zc = register_mdns()
    server = HTTPServer(("0.0.0.0", PORT), OHAPHandler)
    hostname = socket.gethostname()
    ip = socket.gethostbyname(hostname)
    print(f"OHAP server running on http://{ip}:{PORT}")
    print(f"Device: {DEVICE_NAME} ({DEVICE_TYPE})")
    print(f"Sensors: {len(SENSORS)}")
    print(f"Auth: {'enabled' if TOKEN else 'disabled'}")
    print(f"mDNS: {'registered' if zc else 'unavailable (pip install zeroconf)'}")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        if zc:
            zc.close()
        print("\nShutdown.")
