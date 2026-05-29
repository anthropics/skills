#!/usr/bin/env python3
"""
Simple HTTP server for Chat GUI integration
Monitors GUI directory for messages and serves responses
"""

import os
import time
import json
from http.server import HTTPServer, BaseHTTPRequestHandler
from pathlib import Path

# Configuration
SCRIPT_DIR = Path(__file__).parent
GUI_DIR = SCRIPT_DIR / "data" / "gui"
GUI_DIR.mkdir(parents=True, exist_ok=True)

PORT = 8888

class GUIHandler(BaseHTTPRequestHandler):
    """Handler for GUI requests"""
    
    def do_GET(self):
        """Handle GET requests - serve latest message"""
        if self.path == '/latest':
            latest_file = GUI_DIR / "latest.txt"
            
            if latest_file.exists():
                timestamp = latest_file.read_text().strip()
                message_file = GUI_DIR / f"chat_{timestamp}.txt"
                
                if message_file.exists():
                    content = message_file.read_text()
                    
                    self.send_response(200)
                    self.send_header('Content-type', 'application/json')
                    self.send_header('Access-Control-Allow-Origin', '*')
                    self.end_headers()
                    
                    response = {
                        "timestamp": timestamp,
                        "message": content,
                        "status": "success"
                    }
                    
                    self.wfile.write(json.dumps(response).encode())
                    return
            
            # No message available
            self.send_response(204)
            self.end_headers()
            
        elif self.path == '/status':
            self.send_response(200)
            self.send_header('Content-type', 'application/json')
            self.send_header('Access-Control-Allow-Origin', '*')
            self.end_headers()
            
            response = {
                "status": "running",
                "port": PORT,
                "gui_dir": str(GUI_DIR)
            }
            
            self.wfile.write(json.dumps(response).encode())
            
        else:
            self.send_response(404)
            self.end_headers()
    
    def do_POST(self):
        """Handle POST requests - receive user responses"""
        if self.path == '/respond':
            content_length = int(self.headers['Content-Length'])
            post_data = self.rfile.read(content_length)
            
            try:
                data = json.loads(post_data.decode())
                timestamp = data.get('timestamp')
                response_text = data.get('response', '')
                
                if timestamp and response_text:
                    response_file = GUI_DIR / f"response_{timestamp}.txt"
                    response_file.write_text(response_text)
                    
                    self.send_response(200)
                    self.send_header('Content-type', 'application/json')
                    self.send_header('Access-Control-Allow-Origin', '*')
                    self.end_headers()
                    
                    result = {"status": "success", "message": "Response saved"}
                    self.wfile.write(json.dumps(result).encode())
                    return
            
            except Exception as e:
                self.send_response(400)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                
                result = {"status": "error", "message": str(e)}
                self.wfile.write(json.dumps(result).encode())
                return
        
        self.send_response(404)
        self.end_headers()
    
    def do_OPTIONS(self):
        """Handle OPTIONS for CORS"""
        self.send_response(200)
        self.send_header('Access-Control-Allow-Origin', '*')
        self.send_header('Access-Control-Allow-Methods', 'GET, POST, OPTIONS')
        self.send_header('Access-Control-Allow-Headers', 'Content-Type')
        self.end_headers()
    
    def log_message(self, format, *args):
        """Suppress default logging"""
        pass


def run_server():
    """Start the HTTP server"""
    server_address = ('', PORT)
    httpd = HTTPServer(server_address, GUIHandler)
    
    print(f"GUI Server running on http://localhost:{PORT}")
    print(f"GUI Directory: {GUI_DIR}")
    print("")
    print("Endpoints:")
    print("  GET  /latest   - Get latest message")
    print("  POST /respond  - Send response")
    print("  GET  /status   - Server status")
    print("")
    
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down GUI server...")
        httpd.shutdown()


if __name__ == '__main__':
    run_server()
