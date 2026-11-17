#!/bin/bash

# Ollama Model Router - Main Engine
# Routes model outputs to 6 destinations based on JSON schema

# Load config
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/router.config"

# CSV log file with epoch timestamp key
LOG_FILE="${LOG_DIR}/routing_$(date +%s).csv"
mkdir -p "$LOG_DIR" "$GOALS_DIR" "$NOTEPAD_DIR" "$JSON_DIR" "$TERMINAL_DIR" "$GUI_DIR" "$NOTIFY_DIR"

# Initialize CSV log
if [ ! -f "$LOG_FILE" ]; then
    echo "epoch_ms,route,action,content_preview,metadata,status" > "$LOG_FILE"
fi

# Function to log to CSV
log_activity() {
    local route="$1"
    local action="$2"
    local content_preview="$3"
    local metadata="$4"
    local status="$5"
    
    local epoch_ms=$(date +%s%3N)
    # Escape commas and quotes for CSV
    content_preview=$(echo "$content_preview" | head -c 100 | tr ',' ';' | tr '"' "'")
    metadata=$(echo "$metadata" | tr ',' ';' | tr '"' "'")
    
    echo "${epoch_ms},${route},${action},\"${content_preview}\",\"${metadata}\",${status}" >> "$LOG_FILE"
}

# Function to call Ollama with JSON schema
call_ollama() {
    local prompt="$1"
    local system_prompt="You must respond with valid JSON only. Your response must follow this schema:
{
  \"route\": 1-6,
  \"content\": \"your response content\",
  \"metadata\": {
    \"file_number\": 1-3 (for route 3 only),
    \"execute\": \"command\" (for route 4 only),
    \"title\": \"optional title\"
  }
}

Routes:
1 = Save to goals file
2 = Save to notepad
3 = Read JSON file (specify file_number: 1, 2, or 3)
4 = Execute terminal command (specify execute: \"command\")
5 = Send to chat GUI
6 = Send notification popup

Choose the appropriate route for this request: $prompt"

    local response=$(curl -s http://localhost:11434/api/generate -d "{
        \"model\": \"${OLLAMA_MODEL}\",
        \"prompt\": \"${system_prompt}\",
        \"stream\": false,
        \"format\": \"json\"
    }")
    
    echo "$response" | jq -r '.response'
}

# Route 1: Goals File
route_goals() {
    local content="$1"
    local timestamp=$(date +%s)
    local goal_file="${GOALS_DIR}/goal_${timestamp}.txt"
    
    echo "$content" > "$goal_file"
    log_activity "1" "save_goal" "$content" "{}" "success"
    echo "✓ Saved to goals: $goal_file"
}

# Route 2: Notepad
route_notepad() {
    local content="$1"
    local timestamp=$(date +%s)
    local note_file="${NOTEPAD_DIR}/note_${timestamp}.txt"
    
    echo "$content" > "$note_file"
    log_activity "2" "save_note" "$content" "{}" "success"
    echo "✓ Saved to notepad: $note_file"
}

# Route 3: JSON File Reading (returns to model)
route_json_read() {
    local file_number="$1"
    local json_file="${JSON_DIR}/data_${file_number}.json"
    
    if [ ! -f "$json_file" ]; then
        echo "{}" > "$json_file"
    fi
    
    local json_content=$(cat "$json_file")
    log_activity "3" "read_json" "file_${file_number}" "{\"file\":\"$json_file\"}" "success"
    echo "✓ Read JSON file #${file_number}"
    
    # Return content to model
    echo "$json_content"
}

# Route 4: Terminal Execution (returns to model)
route_terminal() {
    local command="$1"
    
    echo "→ Executing: $command"
    local output=$(eval "$command" 2>&1)
    local exit_code=$?
    
    log_activity "4" "execute_terminal" "$command" "{\"exit_code\":$exit_code}" "success"
    
    if [ $exit_code -eq 0 ]; then
        echo "✓ Command executed successfully"
    else
        echo "✗ Command failed (exit code: $exit_code)"
    fi
    
    # Return output to model
    echo "$output"
}

# Route 5: Chat GUI (returns to model)
route_gui() {
    local content="$1"
    local timestamp=$(date +%s)
    local gui_file="${GUI_DIR}/chat_${timestamp}.txt"
    
    echo "$content" > "$gui_file"
    echo "$timestamp" > "${GUI_DIR}/latest.txt"
    
    log_activity "5" "send_gui" "$content" "{}" "success"
    echo "✓ Sent to chat GUI: $gui_file"
    
    # Wait for GUI response
    local response_file="${GUI_DIR}/response_${timestamp}.txt"
    local wait_count=0
    
    while [ ! -f "$response_file" ] && [ $wait_count -lt 30 ]; do
        sleep 1
        ((wait_count++))
    done
    
    if [ -f "$response_file" ]; then
        local gui_response=$(cat "$response_file")
        rm "$response_file"
        echo "$gui_response"
    else
        echo "No response from GUI"
    fi
}

# Route 6: Notification Popup
route_notify() {
    local content="$1"
    local title="${2:-Ollama Notification}"
    
    # Send to notification hub via socket
    echo "{\"title\":\"$title\",\"message\":\"$content\"}" | nc localhost 9999
    
    log_activity "6" "send_notification" "$content" "{\"title\":\"$title\"}" "success"
    echo "✓ Notification sent: $title"
}

# Main routing function
route_response() {
    local json_response="$1"
    
    # Parse JSON
    local route=$(echo "$json_response" | jq -r '.route')
    local content=$(echo "$json_response" | jq -r '.content')
    local metadata=$(echo "$json_response" | jq -r '.metadata // {}')
    
    echo "→ Routing to destination $route"
    
    local return_data=""
    
    case $route in
        1)
            route_goals "$content"
            ;;
        2)
            route_notepad "$content"
            ;;
        3)
            local file_num=$(echo "$metadata" | jq -r '.file_number // 1')
            return_data=$(route_json_read "$file_num")
            ;;
        4)
            local cmd=$(echo "$metadata" | jq -r '.execute // "echo No command specified"')
            return_data=$(route_terminal "$cmd")
            ;;
        5)
            return_data=$(route_gui "$content")
            ;;
        6)
            local title=$(echo "$metadata" | jq -r '.title // "Notification"')
            route_notify "$content" "$title"
            ;;
        *)
            echo "✗ Unknown route: $route"
            log_activity "$route" "error" "unknown_route" "{}" "failed"
            ;;
    esac
    
    # Return data for routes 3, 4, 5
    if [ ! -z "$return_data" ]; then
        echo ""
        echo "← Return data:"
        echo "$return_data"
    fi
}

# Interactive mode
interactive_mode() {
    echo "===================================="
    echo "  Ollama Router - Interactive Mode"
    echo "===================================="
    echo ""
    echo "Type your prompts. Type 'exit' to quit."
    echo ""
    
    while true; do
        echo -n "You: "
        read -r user_input
        
        if [ "$user_input" = "exit" ]; then
            echo "Goodbye!"
            break
        fi
        
        if [ -z "$user_input" ]; then
            continue
        fi
        
        echo ""
        echo "Model: Processing..."
        
        local model_response=$(call_ollama "$user_input")
        
        if [ $? -eq 0 ] && [ ! -z "$model_response" ]; then
            echo ""
            echo "Response:"
            echo "$model_response" | jq '.'
            echo ""
            
            route_response "$model_response"
        else
            echo "✗ Failed to get response from Ollama"
            log_activity "0" "error" "ollama_failed" "{}" "failed"
        fi
        
        echo ""
        echo "---"
        echo ""
    done
}

# Batch mode
batch_mode() {
    local prompt="$1"
    
    echo "→ Processing batch request..."
    local model_response=$(call_ollama "$prompt")
    
    if [ $? -eq 0 ] && [ ! -z "$model_response" ]; then
        echo ""
        echo "Response:"
        echo "$model_response" | jq '.'
        echo ""
        
        route_response "$model_response"
    else
        echo "✗ Failed to get response from Ollama"
        log_activity "0" "error" "ollama_failed" "{}" "failed"
        exit 1
    fi
}

# Main entry point
main() {
    if [ $# -eq 0 ]; then
        interactive_mode
    else
        batch_mode "$@"
    fi
}

main "$@"
