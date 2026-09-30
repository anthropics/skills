#!/usr/bin/env python3
"""
Socket-based Notification Hub
Receives notification requests via TCP socket and handles popup display
"""

import socket
import json
import subprocess
import sys
from datetime import datetime
from pathlib import Path

# Configuration
HOST = 'localhost'
PORT = 9999
BUFFER_SIZE = 4096

SCRIPT_DIR = Path(__file__).parent
NOTIFY_DIR = SCRIPT_DIR / "data" / "notifications"
NOTIFY_DIR.mkdir(parents=True, exist_ok=True)


def show_notification(title, message):
    """
    Display notification using available system tools
    Tries multiple methods for cross-platform support
    """
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_file = NOTIFY_DIR / f"notification_{timestamp}.log"
    
    # Log notification
    with open(log_file, 'w') as f:
        f.write(f"Title: {title}\n")
        f.write(f"Message: {message}\n")
        f.write(f"Timestamp: {timestamp}\n")
    
    # Try different notification methods
    
    # Method 1: notify-send (Linux)
    try:
        subprocess.run(['notify-send', title, message], 
                      check=False, 
                      stderr=subprocess.DEVNULL)
        return True
    except FileNotFoundError:
        pass
    
    # Method 2: osascript (macOS)
    try:
        script = f'display notification "{message}" with title "{title}"'
        subprocess.run(['osascript', '-e', script], 
                      check=False,
                      stderr=subprocess.DEVNULL)
        return True
    except FileNotFoundError:
        pass
    
    # Method 3: PowerShell (Windows)
    try:
        ps_script = f'''
        [Windows.UI.Notifications.ToastNotificationManager, Windows.UI.Notifications, ContentType = WindowsRuntime] > $null
        $template = [Windows.UI.Notifications.ToastNotificationManager]::GetTemplateContent([Windows.UI.Notifications.ToastTemplateType]::ToastText02)
        $toastXml = [xml] $template.GetXml()
        $toastXml.GetElementsByTagName("text")[0].AppendChild($toastXml.CreateTextNode("{title}")) > $null
        $toastXml.GetElementsByTagName("text")[1].AppendChild($toastXml.CreateTextNode("{message}")) > $null
        $toast = [Windows.UI.Notifications.ToastNotification]::new($toastXml)
        [Windows.UI.Notifications.ToastNotificationManager]::CreateToastNotifier("Ollama Router").Show($toast)
        '''
        subprocess.run(['powershell', '-Command', ps_script],
                      check=False,
                      stderr=subprocess.DEVNULL)
        return True
    except FileNotFoundError:
        pass
    
    # Fallback: Print to console
    print(f"\n{'='*50}")
    print(f"NOTIFICATION: {title}")
    print(f"{message}")
    print(f"{'='*50}\n")
    
    return True


def handle_notification(data):
    """Parse and display notification from JSON data"""
    try:
        notification = json.loads(data)
        title = notification.get('title', 'Notification')
        message = notification.get('message', '')
        
        if message:
            show_notification(title, message)
            return True
        else:
            print(f"Error: Empty message in notification")
            return False
            
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON - {e}")
        return False
    except Exception as e:
        print(f"Error: Failed to handle notification - {e}")
        return False


def run_server():
    """Start the notification socket server"""
    server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    
    try:
        server_socket.bind((HOST, PORT))
        server_socket.listen(5)
        
        print(f"Notification Hub running on {HOST}:{PORT}")
        print(f"Notification log directory: {NOTIFY_DIR}")
        print("Waiting for notifications...\n")
        
        while True:
            try:
                client_socket, address = server_socket.accept()
                
                # Receive data
                data = client_socket.recv(BUFFER_SIZE).decode('utf-8')
                
                if data:
                    # Handle notification
                    success = handle_notification(data)
                    
                    # Send response
                    response = json.dumps({"status": "success" if success else "error"})
                    client_socket.send(response.encode())
                
                client_socket.close()
                
            except KeyboardInterrupt:
                print("\nShutting down notification hub...")
                break
            except Exception as e:
                print(f"Error handling connection: {e}")
                continue
    
    finally:
        server_socket.close()


if __name__ == '__main__':
    try:
        run_server()
    except Exception as e:
        print(f"Fatal error: {e}")
        sys.exit(1)
