#!/bin/bash

# Master Control Script for Ollama Router System

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/router.config"

PID_DIR="${SCRIPT_DIR}/.pids"
mkdir -p "$PID_DIR"

GUI_PID_FILE="${PID_DIR}/gui_server.pid"
NOTIFY_PID_FILE="${PID_DIR}/notification_hub.pid"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Check if service is running
is_running() {
    local pid_file="$1"
    if [ -f "$pid_file" ]; then
        local pid=$(cat "$pid_file")
        if ps -p "$pid" > /dev/null 2>&1; then
            return 0
        else
            rm "$pid_file"
            return 1
        fi
    fi
    return 1
}

# Start GUI server
start_gui() {
    if is_running "$GUI_PID_FILE"; then
        echo -e "${YELLOW}GUI server already running${NC}"
        return 0
    fi
    
    echo -n "Starting GUI server... "
    python3 "${SCRIPT_DIR}/gui_server.py" > /dev/null 2>&1 &
    echo $! > "$GUI_PID_FILE"
    sleep 1
    
    if is_running "$GUI_PID_FILE"; then
        echo -e "${GREEN}✓${NC}"
        return 0
    else
        echo -e "${RED}✗${NC}"
        return 1
    fi
}

# Start notification hub
start_notify() {
    if is_running "$NOTIFY_PID_FILE"; then
        echo -e "${YELLOW}Notification hub already running${NC}"
        return 0
    fi
    
    echo -n "Starting notification hub... "
    python3 "${SCRIPT_DIR}/notification_hub.py" > /dev/null 2>&1 &
    echo $! > "$NOTIFY_PID_FILE"
    sleep 1
    
    if is_running "$NOTIFY_PID_FILE"; then
        echo -e "${GREEN}✓${NC}"
        return 0
    else
        echo -e "${RED}✗${NC}"
        return 1
    fi
}

# Stop service
stop_service() {
    local pid_file="$1"
    local service_name="$2"
    
    if is_running "$pid_file"; then
        local pid=$(cat "$pid_file")
        echo -n "Stopping ${service_name}... "
        kill "$pid" 2>/dev/null
        sleep 1
        
        if ps -p "$pid" > /dev/null 2>&1; then
            kill -9 "$pid" 2>/dev/null
        fi
        
        rm "$pid_file"
        echo -e "${GREEN}✓${NC}"
    else
        echo -e "${YELLOW}${service_name} not running${NC}"
    fi
}

# Start all services
start_all() {
    echo "===================================="
    echo "  Starting Ollama Router System"
    echo "===================================="
    echo ""
    
    start_gui
    start_notify
    
    echo ""
    echo -e "${GREEN}System started!${NC}"
    echo ""
    echo "Services running:"
    echo "  • GUI Server: http://localhost:8888"
    echo "  • Notification Hub: localhost:9999"
    echo ""
    echo "Use './control.sh run' to start interactive mode"
}

# Stop all services
stop_all() {
    echo "===================================="
    echo "  Stopping Ollama Router System"
    echo "===================================="
    echo ""
    
    stop_service "$GUI_PID_FILE" "GUI server"
    stop_service "$NOTIFY_PID_FILE" "Notification hub"
    
    echo ""
    echo -e "${GREEN}System stopped!${NC}"
}

# Show status
show_status() {
    echo "===================================="
    echo "  Ollama Router System Status"
    echo "===================================="
    echo ""
    
    echo -n "GUI Server (8888): "
    if is_running "$GUI_PID_FILE"; then
        echo -e "${GREEN}Running${NC} (PID: $(cat $GUI_PID_FILE))"
    else
        echo -e "${RED}Stopped${NC}"
    fi
    
    echo -n "Notification Hub (9999): "
    if is_running "$NOTIFY_PID_FILE"; then
        echo -e "${GREEN}Running${NC} (PID: $(cat $NOTIFY_PID_FILE))"
    else
        echo -e "${RED}Stopped${NC}"
    fi
    
    echo ""
    echo -n "Ollama Service: "
    if curl -s http://localhost:11434/api/tags > /dev/null 2>&1; then
        echo -e "${GREEN}Running${NC}"
    else
        echo -e "${RED}Not accessible${NC}"
    fi
    
    echo ""
}

# Run interactive mode
run_interactive() {
    echo "Checking services..."
    
    if ! is_running "$GUI_PID_FILE"; then
        start_gui
    fi
    
    if ! is_running "$NOTIFY_PID_FILE"; then
        start_notify
    fi
    
    echo ""
    bash "${SCRIPT_DIR}/ollama_runner.sh"
}

# Run batch mode
run_batch() {
    local prompt="$1"
    
    if ! is_running "$GUI_PID_FILE"; then
        start_gui > /dev/null 2>&1
    fi
    
    if ! is_running "$NOTIFY_PID_FILE"; then
        start_notify > /dev/null 2>&1
    fi
    
    bash "${SCRIPT_DIR}/ollama_runner.sh" "$prompt"
}

# Show logs
show_logs() {
    local log_type="$1"
    
    case "$log_type" in
        csv)
            echo "Recent CSV logs:"
            echo ""
            ls -lt "$LOG_DIR"/*.csv 2>/dev/null | head -5 | while read line; do
                echo "$line"
            done
            echo ""
            echo "View a log file:"
            echo "  cat $LOG_DIR/routing_<timestamp>.csv"
            ;;
        latest)
            local latest_log=$(ls -t "$LOG_DIR"/*.csv 2>/dev/null | head -1)
            if [ -f "$latest_log" ]; then
                echo "Latest log: $latest_log"
                echo ""
                cat "$latest_log"
            else
                echo "No logs found"
            fi
            ;;
        *)
            echo "Available log commands:"
            echo "  ./control.sh logs csv     - List recent CSV logs"
            echo "  ./control.sh logs latest  - Show latest log file"
            ;;
    esac
}

# Test system
test_system() {
    echo "Running system tests..."
    bash "${SCRIPT_DIR}/test_routes.sh"
}

# Main command handler
case "$1" in
    start)
        start_all
        ;;
    stop)
        stop_all
        ;;
    restart)
        stop_all
        sleep 2
        start_all
        ;;
    status)
        show_status
        ;;
    run)
        run_interactive
        ;;
    batch)
        if [ -z "$2" ]; then
            echo "Usage: $0 batch \"your prompt here\""
            exit 1
        fi
        run_batch "$2"
        ;;
    logs)
        show_logs "$2"
        ;;
    test)
        test_system
        ;;
    *)
        echo "Ollama Router System Control"
        echo ""
        echo "Usage: $0 {start|stop|restart|status|run|batch|logs|test}"
        echo ""
        echo "Commands:"
        echo "  start       - Start all services (GUI + Notification Hub)"
        echo "  stop        - Stop all services"
        echo "  restart     - Restart all services"
        echo "  status      - Show service status"
        echo "  run         - Run interactive mode"
        echo "  batch       - Run batch mode with prompt"
        echo "  logs        - View logs (csv|latest)"
        echo "  test        - Run system tests"
        echo ""
        exit 1
        ;;
esac
