#!/usr/bin/env python3
"""
Simple HTTP server for AI Voice Chat app
Run this to serve the app locally and access from your iPhone
"""

import http.server
import socketserver
import socket
import sys

PORT = 8080

class MyHTTPRequestHandler(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        # Add CORS headers for local development
        self.send_header('Access-Control-Allow-Origin', '*')
        self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate')
        super().end_headers()

def get_local_ip():
    """Get the local IP address"""
    try:
        # Create a socket to get local IP
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        local_ip = s.getsockname()[0]
        s.close()
        return local_ip
    except:
        return "localhost"

if __name__ == "__main__":
    local_ip = get_local_ip()

    with socketserver.TCPServer(("", PORT), MyHTTPRequestHandler) as httpd:
        print("\n" + "="*60)
        print("AI Voice Chat Server Running")
        print("="*60)
        print(f"\nOn this computer: http://localhost:{PORT}")
        print(f"On your iPhone:   http://{local_ip}:{PORT}")
        print("\nMake sure your iPhone is on the same WiFi network!")
        print("\nPress Ctrl+C to stop the server")
        print("="*60 + "\n")

        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\n\nServer stopped.")
            sys.exit(0)
