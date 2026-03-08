"""OHAP Server — Minimal implementation for ESP32/ESP8266 (MicroPython).

Upload to your ESP32 and run. Implements the full OHAP protocol in <80 lines.

Dependencies: None (uses MicroPython builtins)
Hardware: Any ESP32 or ESP8266 board with WiFi
Optional: DHT22 on GPIO4, LED on GPIO2
"""

import json
import time
import machine
import network
import socket

# ── Configuration ────────────────────────────────────────────
DEVICE_NAME = "ESP32 Sensor"
DEVICE_TYPE = "environmental"
PORT = 8421
SSID = "YOUR_WIFI_SSID"
PASSWORD = "YOUR_WIFI_PASSWORD"
START = time.time()

# ── Sensors ──────────────────────────────────────────────────
try:
    import dht
    d = dht.DHT22(machine.Pin(4))
    HAS_DHT = True
except Exception:
    HAS_DHT = False

SENSORS = [{"id": "hall", "name": "Hall Effect", "type": "magnetic", "unit": "raw"}]
if HAS_DHT:
    SENSORS += [
        {"id": "temp", "name": "Temperature", "type": "temperature", "unit": "celsius"},
        {"id": "hum", "name": "Humidity", "type": "humidity", "unit": "percent"},
    ]


def read_sensor(sid):
    if sid == "hall":
        return {"sensor_id": sid, "value": machine.Pin(0).value(), "quality": "good"}
    if sid == "temp" and HAS_DHT:
        d.measure()
        return {"sensor_id": sid, "value": d.temperature(), "unit": "celsius", "quality": "good"}
    if sid == "hum" and HAS_DHT:
        d.measure()
        return {"sensor_id": sid, "value": d.humidity(), "unit": "percent", "quality": "good"}
    return {"sensor_id": sid, "error": "unknown", "quality": "error"}


def handle(conn):
    req = conn.recv(1024).decode()
    path = req.split(" ")[1] if " " in req else "/"

    if path == "/agent/info":
        data = {"name": DEVICE_NAME, "type": DEVICE_TYPE, "version": "1.0",
                "protocol": "ohap", "uptime_seconds": int(time.time() - START)}
    elif path == "/agent/sensors":
        data = {"sensors": SENSORS}
    elif path == "/agent/read/all":
        data = {"readings": [read_sensor(s["id"]) for s in SENSORS]}
    elif path.startswith("/agent/read/"):
        data = read_sensor(path.split("/")[-1])
    elif path == "/agent/health":
        import gc; gc.collect()
        data = {"status": "healthy", "uptime_seconds": int(time.time() - START),
                "free_memory": gc.mem_free()}
    elif path == "/agent/command":
        # Simple LED toggle example
        led = machine.Pin(2, machine.Pin.OUT)
        led.value(not led.value())
        data = {"status": "ok", "result": f"LED {'on' if led.value() else 'off'}"}
    else:
        data = {"error": "not found"}

    body = json.dumps(data)
    conn.send("HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n"
              f"Content-Length: {len(body)}\r\n\r\n{body}")
    conn.close()


# ── WiFi Connect ─────────────────────────────────────────────
wlan = network.WLAN(network.STA_IF)
wlan.active(True)
wlan.connect(SSID, PASSWORD)
while not wlan.isconnected():
    time.sleep(0.5)
ip = wlan.ifconfig()[0]
print(f"OHAP server: http://{ip}:{PORT}")

# ── Main Loop ────────────────────────────────────────────────
s = socket.socket()
s.bind(("0.0.0.0", PORT))
s.listen(2)
while True:
    conn, addr = s.accept()
    try:
        handle(conn)
    except Exception as e:
        print(f"Error: {e}")
        conn.close()
