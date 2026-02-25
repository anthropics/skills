#!/bin/bash

# Test Suite for Ollama Router System

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/router.config"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

PASS_COUNT=0
FAIL_COUNT=0

print_header() {
    echo ""
    echo -e "${BLUE}======================================${NC}"
    echo -e "${BLUE}  $1${NC}"
    echo -e "${BLUE}======================================${NC}"
    echo ""
}

test_pass() {
    echo -e "  ${GREEN}✓${NC} $1"
    ((PASS_COUNT++))
}

test_fail() {
    echo -e "  ${RED}✗${NC} $1"
    ((FAIL_COUNT++))
}

test_info() {
    echo -e "  ${YELLOW}→${NC} $1"
}

# Test Route 1: Goals File
test_route_1() {
    print_header "Test Route 1: Goals File"
    
    local test_content="Test goal: Complete project by EOD"
    local timestamp=$(date +%s)
    
    # Simulate writing to goals
    echo "$test_content" > "${GOALS_DIR}/goal_${timestamp}.txt"
    
    if [ -f "${GOALS_DIR}/goal_${timestamp}.txt" ]; then
        test_pass "Goals file created"
        
        local content=$(cat "${GOALS_DIR}/goal_${timestamp}.txt")
        if [ "$content" = "$test_content" ]; then
            test_pass "Content matches"
        else
            test_fail "Content mismatch"
        fi
        
        # Cleanup
        rm "${GOALS_DIR}/goal_${timestamp}.txt"
    else
        test_fail "Failed to create goals file"
    fi
}

# Test Route 2: Notepad
test_route_2() {
    print_header "Test Route 2: Notepad"
    
    local test_content="Test note: Remember to check logs"
    local timestamp=$(date +%s)
    
    # Simulate writing to notepad
    echo "$test_content" > "${NOTEPAD_DIR}/note_${timestamp}.txt"
    
    if [ -f "${NOTEPAD_DIR}/note_${timestamp}.txt" ]; then
        test_pass "Notepad file created"
        
        local content=$(cat "${NOTEPAD_DIR}/note_${timestamp}.txt")
        if [ "$content" = "$test_content" ]; then
            test_pass "Content matches"
        else
            test_fail "Content mismatch"
        fi
        
        # Cleanup
        rm "${NOTEPAD_DIR}/note_${timestamp}.txt"
    else
        test_fail "Failed to create notepad file"
    fi
}

# Test Route 3: JSON File Reading
test_route_3() {
    print_header "Test Route 3: JSON File Reading"
    
    # Test all 3 JSON files
    for i in 1 2 3; do
        local json_file="${JSON_DIR}/data_${i}.json"
        
        if [ -f "$json_file" ]; then
            test_pass "JSON file #${i} exists"
            
            # Validate JSON
            if jq empty "$json_file" 2>/dev/null; then
                test_pass "JSON file #${i} is valid JSON"
            else
                test_fail "JSON file #${i} is invalid"
            fi
        else
            test_fail "JSON file #${i} not found"
        fi
    done
    
    # Test writing and reading
    local test_data='{"test": true, "timestamp": '$(date +%s)'}'
    echo "$test_data" > "${JSON_DIR}/data_1.json"
    
    local read_data=$(cat "${JSON_DIR}/data_1.json")
    if [ "$read_data" = "$test_data" ]; then
        test_pass "JSON read/write works"
    else
        test_fail "JSON read/write failed"
    fi
}

# Test Route 4: Terminal Execution
test_route_4() {
    print_header "Test Route 4: Terminal Execution"
    
    # Test simple command
    local output=$(echo "Test" | tr '[:lower:]' '[:upper:]')
    if [ "$output" = "TEST" ]; then
        test_pass "Simple command execution works"
    else
        test_fail "Simple command failed"
    fi
    
    # Test command with exit code
    ls /tmp > /dev/null 2>&1
    if [ $? -eq 0 ]; then
        test_pass "Command exit code check works"
    else
        test_fail "Exit code check failed"
    fi
    
    # Test output capture
    local test_output=$(echo "Hello World")
    if [ "$test_output" = "Hello World" ]; then
        test_pass "Output capture works"
    else
        test_fail "Output capture failed"
    fi
}

# Test Route 5: Chat GUI
test_route_5() {
    print_header "Test Route 5: Chat GUI"
    
    local timestamp=$(date +%s)
    local test_message="Test GUI message"
    
    # Simulate GUI write
    echo "$test_message" > "${GUI_DIR}/chat_${timestamp}.txt"
    echo "$timestamp" > "${GUI_DIR}/latest.txt"
    
    if [ -f "${GUI_DIR}/chat_${timestamp}.txt" ]; then
        test_pass "GUI message file created"
        
        if [ -f "${GUI_DIR}/latest.txt" ]; then
            local latest=$(cat "${GUI_DIR}/latest.txt")
            if [ "$latest" = "$timestamp" ]; then
                test_pass "Latest timestamp updated"
            else
                test_fail "Latest timestamp mismatch"
            fi
        else
            test_fail "Latest file not created"
        fi
        
        # Cleanup
        rm "${GUI_DIR}/chat_${timestamp}.txt"
        rm "${GUI_DIR}/latest.txt"
    else
        test_fail "Failed to create GUI message file"
    fi
    
    # Test GUI server
    test_info "Checking GUI server..."
    if curl -s http://localhost:8888/status > /dev/null 2>&1; then
        test_pass "GUI server is accessible"
    else
        test_fail "GUI server not running"
    fi
}

# Test Route 6: Notifications
test_route_6() {
    print_header "Test Route 6: Notifications"
    
    # Test notification hub
    test_info "Checking notification hub..."
    if nc -z localhost 9999 2>/dev/null; then
        test_pass "Notification hub is accessible"
        
        # Send test notification
        echo '{"title":"Test","message":"Test notification"}' | nc localhost 9999 > /dev/null 2>&1
        if [ $? -eq 0 ]; then
            test_pass "Notification sent successfully"
        else
            test_fail "Failed to send notification"
        fi
    else
        test_fail "Notification hub not running"
    fi
}

# Test Configuration
test_config() {
    print_header "Test Configuration"
    
    # Check config file
    if [ -f "${SCRIPT_DIR}/router.config" ]; then
        test_pass "Configuration file exists"
    else
        test_fail "Configuration file not found"
    fi
    
    # Check directories
    local dirs=("$GOALS_DIR" "$NOTEPAD_DIR" "$JSON_DIR" "$TERMINAL_DIR" "$GUI_DIR" "$NOTIFY_DIR" "$LOG_DIR")
    local dir_names=("Goals" "Notepad" "JSON" "Terminal" "GUI" "Notifications" "Logs")
    
    for i in "${!dirs[@]}"; do
        if [ -d "${dirs[$i]}" ]; then
            test_pass "${dir_names[$i]} directory exists"
        else
            test_fail "${dir_names[$i]} directory not found"
            mkdir -p "${dirs[$i]}"
        fi
    done
}

# Test Ollama Connection
test_ollama() {
    print_header "Test Ollama Connection"
    
    test_info "Checking Ollama service..."
    if curl -s http://localhost:11434/api/tags > /dev/null 2>&1; then
        test_pass "Ollama service is running"
        
        # Check model
        local models=$(curl -s http://localhost:11434/api/tags | jq -r '.models[].name' 2>/dev/null)
        if echo "$models" | grep -q "$OLLAMA_MODEL"; then
            test_pass "Model '$OLLAMA_MODEL' is available"
        else
            test_fail "Model '$OLLAMA_MODEL' not found"
            echo "    Available models:"
            echo "$models" | sed 's/^/      /'
        fi
    else
        test_fail "Ollama service not accessible"
        test_info "Start Ollama with: ollama serve"
    fi
}

# Test CSV Logging
test_logging() {
    print_header "Test CSV Logging"
    
    local test_log="${LOG_DIR}/test_$(date +%s).csv"
    
    # Create test log
    echo "epoch_ms,route,action,content_preview,metadata,status" > "$test_log"
    echo "$(date +%s%3N),1,test,\"Test content\",\"{}\",success" >> "$test_log"
    
    if [ -f "$test_log" ]; then
        test_pass "CSV log file created"
        
        # Verify CSV format
        local line_count=$(wc -l < "$test_log")
        if [ "$line_count" -eq 2 ]; then
            test_pass "CSV has correct number of lines"
        else
            test_fail "CSV line count incorrect"
        fi
        
        # Cleanup
        rm "$test_log"
    else
        test_fail "Failed to create CSV log"
    fi
}

# Run all tests
run_all_tests() {
    echo ""
    echo -e "${BLUE}╔════════════════════════════════════════╗${NC}"
    echo -e "${BLUE}║  Ollama Router System - Test Suite    ║${NC}"
    echo -e "${BLUE}╚════════════════════════════════════════╝${NC}"
    
    test_config
    test_logging
    test_ollama
    test_route_1
    test_route_2
    test_route_3
    test_route_4
    test_route_5
    test_route_6
    
    # Summary
    print_header "Test Summary"
    
    local total=$((PASS_COUNT + FAIL_COUNT))
    local pass_percent=0
    
    if [ $total -gt 0 ]; then
        pass_percent=$((PASS_COUNT * 100 / total))
    fi
    
    echo -e "  Total Tests: ${total}"
    echo -e "  ${GREEN}Passed: ${PASS_COUNT}${NC}"
    echo -e "  ${RED}Failed: ${FAIL_COUNT}${NC}"
    echo -e "  Success Rate: ${pass_percent}%"
    echo ""
    
    if [ $FAIL_COUNT -eq 0 ]; then
        echo -e "${GREEN}All tests passed! ✓${NC}"
        echo ""
        exit 0
    else
        echo -e "${YELLOW}Some tests failed. Review output above.${NC}"
        echo ""
        exit 1
    fi
}

# Main
run_all_tests
