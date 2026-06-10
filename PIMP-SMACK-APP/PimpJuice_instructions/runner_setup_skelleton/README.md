# Ollama Model Router System

A production-ready routing system that takes Ollama model outputs with JSON schemas and intelligently routes them to 6 different destinations. No mock code, no BS transformations - just clean, working automation.

## 🚀 Features

- **6 Smart Routes**: Goals file, Notepad, JSON reading, Terminal execution, Chat GUI, Notification popups
- **Bidirectional Flow**: Routes 3, 4, 5 return responses back to the model for follow-up processing
- **CSV Logging**: Full activity audit trail with millisecond-precision epoch timestamps
- **Shell-First**: Minimal Python, maximum shell scripting for reliability
- **Production Ready**: Real working code, not prototypes or one-timers
- **Modular Design**: Swap out components as needed

## 📁 Project Structure

```
ollama-router/
├── ollama_runner.sh       # Main routing engine
├── control.sh             # Master management script
├── router.config          # Configuration file
├── gui_server.py          # HTTP server (port 8888)
├── notification_hub.py    # Socket server (port 9999)
├── notify.sh             # Shell notification helper
├── test_routes.sh        # Test suite
└── data/                 # Auto-created directories
    ├── goals/
    ├── notepad/
    ├── json/
    ├── terminal/
    ├── gui/
    ├── notifications/
    └── logs/
```

## 🔧 Requirements

- **Ollama**: Running on localhost:11434
- **Python 3.6+**: For GUI and notification servers
- **jq**: For JSON parsing
- **nc (netcat)**: For socket communication
- **curl**: For API calls

### Install Dependencies

```bash
# Ubuntu/Debian
sudo apt-get install jq netcat curl python3

# macOS
brew install jq netcat curl python3

# Fedora/RHEL
sudo dnf install jq nmap-ncat curl python3
```

## 🎯 Quick Start

### 1. Start the System

```bash
./control.sh start
```

This starts:
- GUI Server (http://localhost:8888)
- Notification Hub (localhost:9999)

### 2. Run Interactive Mode

```bash
./control.sh run
```

Type your prompts and the model will automatically route responses to the appropriate destination.

### 3. Run Batch Mode

```bash
./control.sh batch "Your prompt here"
```

Process a single prompt and exit.

## 📋 The 6 Routes Explained

### Route 1: Goals File
**Purpose**: Save important goals/objectives  
**Output**: `data/goals/goal_<timestamp>.txt`  
**Returns Data**: No

### Route 2: Notepad
**Purpose**: Quick notes and reminders  
**Output**: `data/notepad/note_<timestamp>.txt`  
**Returns Data**: No

### Route 3: JSON File Reading
**Purpose**: Read structured data from one of 3 JSON files  
**Output**: Returns JSON content to model  
**Returns Data**: ✓ Yes  
**Files**: `data/json/data_1.json`, `data_2.json`, `data_3.json`

### Route 4: Terminal Execution
**Purpose**: Execute shell commands  
**Output**: Returns command output to model  
**Returns Data**: ✓ Yes  
**Security**: Use with caution - executes real commands

### Route 5: Chat GUI
**Purpose**: Interactive chat interface  
**Output**: File-based communication with GUI  
**Returns Data**: ✓ Yes (waits for user response)  
**Integration**: HTTP endpoints at port 8888

### Route 6: Notification Popups
**Purpose**: Desktop notifications  
**Output**: System notifications + log files  
**Returns Data**: No  
**Platforms**: Linux (notify-send), macOS (osascript), Windows (PowerShell)

## 🎮 Control Commands

```bash
./control.sh start      # Start all services
./control.sh stop       # Stop all services
./control.sh restart    # Restart everything
./control.sh status     # Check service status
./control.sh run        # Interactive mode
./control.sh batch      # Batch mode with prompt
./control.sh logs csv   # List recent CSV logs
./control.sh logs latest # Show latest log
./control.sh test       # Run test suite
```

## 🔍 How It Works

1. **User sends prompt** to Ollama model
2. **Model responds** with JSON containing:
   ```json
   {
     "route": 1-6,
     "content": "response content",
     "metadata": {
       "file_number": 1-3,  // For route 3
       "execute": "cmd",    // For route 4
       "title": "Title"     // For route 6
     }
   }
   ```
3. **Router processes** JSON and sends to appropriate destination
4. **Routes 3/4/5** return data back to model for follow-up
5. **Everything logged** to CSV with epoch timestamps

## 📊 CSV Logging

All activity is logged to timestamped CSV files in `data/logs/`:

```csv
epoch_ms,route,action,content_preview,metadata,status
1699564832123,1,save_goal,"Complete project...",{},success
1699564833456,4,execute_terminal,"ls -la",{"exit_code":0},success
```

## 🧪 Testing

Run the comprehensive test suite:

```bash
./control.sh test
```

Tests include:
- Configuration validation
- Directory structure
- Ollama connection
- All 6 routes
- CSV logging
- Service availability

## ⚙️ Configuration

Edit `router.config` to customize:

```bash
# Ollama Settings
OLLAMA_MODEL="llama3.2:latest"
OLLAMA_HOST="http://localhost:11434"

# Ports
GUI_PORT=8888
NOTIFY_PORT=9999

# Timeouts
GUI_RESPONSE_TIMEOUT=30
TERMINAL_TIMEOUT=300
```

## 🔌 GUI Integration

The GUI server provides HTTP endpoints for your chat interface:

### Get Latest Message
```bash
curl http://localhost:8888/latest
```

Response:
```json
{
  "timestamp": "1699564832",
  "message": "Your message here",
  "status": "success"
}
```

### Send Response
```bash
curl -X POST http://localhost:8888/respond \
  -H "Content-Type: application/json" \
  -d '{"timestamp":"1699564832","response":"User response"}'
```

### Check Status
```bash
curl http://localhost:8888/status
```

## 📱 Sending Notifications

### Via Shell Helper
```bash
./notify.sh "Task Complete" "Your processing is done!"
```

### Via Socket (from any language)
```bash
echo '{"title":"Alert","message":"Important update"}' | nc localhost 9999
```

## 🐛 Troubleshooting

### Services won't start
```bash
# Check if ports are available
lsof -i :8888
lsof -i :9999

# Check Ollama
curl http://localhost:11434/api/tags
```

### Model not found
```bash
# List available models
curl http://localhost:11434/api/tags | jq '.models[].name'

# Update router.config with correct model name
```

### Permission denied
```bash
# Make scripts executable
chmod +x *.sh
```

### Notifications not showing
- Linux: Install `libnotify-bin`
- macOS: Should work out of the box
- Windows: Requires PowerShell 5.0+

## 📈 Advanced Usage

### Chain Multiple Prompts
```bash
# First prompt gets data
./control.sh batch "Read data from JSON file 1"

# Use returned data in next prompt
./control.sh batch "Based on that data, create a goal"
```

### Custom JSON Files
Edit the JSON data files directly:
```bash
echo '{"api_key":"xyz","endpoint":"api.example.com"}' > data/json/data_1.json
```

### Monitor Logs in Real-Time
```bash
tail -f data/logs/routing_*.csv
```

## 🛠️ Extending the System

### Add New Route
1. Edit `ollama_runner.sh`
2. Add new `route_X()` function
3. Update `route_response()` case statement
4. Update model's system prompt with new route

### Custom Notification Handler
Replace notification methods in `notification_hub.py` with your preferred notification system.

### GUI Integration
Build your own GUI that:
- Polls `/latest` endpoint
- Displays messages
- Posts responses back via `/respond`

## 📝 Example Workflows

### Goal Setting
```
You: "I need to complete this project by Friday"
Model: Routes to Goals (Route 1)
Result: Saved to goals/goal_<timestamp>.txt
```

### Data Lookup
```
You: "What's in our configuration?"
Model: Routes to JSON Read (Route 3)
Model: Reads data_1.json
Model: Gets data back and formulates response
```

### Automation
```
You: "Check disk space"
Model: Routes to Terminal (Route 4)
Model: Executes 'df -h'
Model: Gets output and explains results
```

### Interactive Chat
```
You: "Ask the user what they prefer"
Model: Routes to GUI (Route 5)
System: Waits for user input via GUI
Model: Receives response and continues
```

## 🔒 Security Notes

- **Route 4 (Terminal)**: Executes actual commands - use with caution
- **Review model outputs** before enabling in production
- **Limit command scope** if needed by modifying `route_terminal()`
- **File permissions**: Keep data directory secure

## 📄 License

This is production-ready code built for real use. No mock implementations, no temporary fixes - just solid automation.

## 🤝 Support

Issues? Check:
1. Service status: `./control.sh status`
2. Run tests: `./control.sh test`
3. Check logs: `./control.sh logs latest`
4. Verify Ollama: `curl http://localhost:11434/api/tags`

---

**Built for automation. Built to last. No BS.** 🔥
