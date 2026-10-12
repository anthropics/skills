# FSM Code Generation Templates

This file contains templates and examples for generating FSM implementations in various programming languages.

## Python Implementation

### Basic State Machine Class
```python
from enum import Enum, auto
from typing import Dict, Callable, Optional, Any, Set
from dataclasses import dataclass
import logging

# Generated State Enum
class State(Enum):
    IDLE = auto()
    RUNNING = auto()
    PAUSED = auto()
    ERROR = auto()
    COMPLETED = auto()

# Generated Event Enum
class Event(Enum):
    START = auto()
    PAUSE = auto()
    RESUME = auto()
    STOP = auto()
    ERROR_OCCURRED = auto()
    RESET = auto()

@dataclass
class Transition:
    from_state: State
    event: Event
    to_state: State
    action: Optional[Callable] = None
    guard: Optional[Callable] = None

class StateMachine:
    """Generated FSM implementation"""

    def __init__(self, initial_state: State = State.IDLE):
        self.current_state = initial_state
        self.previous_state: Optional[State] = None
        self.context: Dict[str, Any] = {}
        self._logger = logging.getLogger(__name__)
        self._transitions = self._setup_transitions()
        self._entry_actions: Dict[State, Callable] = {}
        self._exit_actions: Dict[State, Callable] = {}

    def _setup_transitions(self) -> Dict[tuple, Transition]:
        """Define all valid transitions"""
        transitions = [
            Transition(State.IDLE, Event.START, State.RUNNING, self._start_process),
            Transition(State.RUNNING, Event.PAUSE, State.PAUSED, self._pause_process),
            Transition(State.RUNNING, Event.STOP, State.IDLE, self._stop_process),
            Transition(State.RUNNING, Event.ERROR_OCCURRED, State.ERROR, self._handle_error),
            Transition(State.PAUSED, Event.RESUME, State.RUNNING, self._resume_process),
            Transition(State.PAUSED, Event.STOP, State.IDLE, self._stop_process),
            Transition(State.ERROR, Event.RESET, State.IDLE, self._reset_system),
        ]

        return {(t.from_state, t.event): t for t in transitions}

    def process_event(self, event: Event, **kwargs) -> bool:
        """Process an event and transition if valid"""
        key = (self.current_state, event)

        if key not in self._transitions:
            self._logger.warning(f"Invalid transition: {self.current_state} + {event}")
            return False

        transition = self._transitions[key]

        # Check guard condition if present
        if transition.guard and not transition.guard(**kwargs):
            self._logger.info(f"Guard condition failed for {transition}")
            return False

        # Execute exit action for current state
        if self.current_state in self._exit_actions:
            self._exit_actions[self.current_state]()

        # Store previous state
        self.previous_state = self.current_state

        # Execute transition action if present
        if transition.action:
            transition.action(**kwargs)

        # Change state
        self.current_state = transition.to_state
        self._logger.info(f"Transitioned: {self.previous_state} -> {self.current_state}")

        # Execute entry action for new state
        if self.current_state in self._entry_actions:
            self._entry_actions[self.current_state]()

        return True

    # Action methods (to be implemented)
    def _start_process(self, **kwargs):
        """Action: Start the process"""
        pass

    def _pause_process(self, **kwargs):
        """Action: Pause the process"""
        pass

    def _resume_process(self, **kwargs):
        """Action: Resume the process"""
        pass

    def _stop_process(self, **kwargs):
        """Action: Stop the process"""
        pass

    def _handle_error(self, **kwargs):
        """Action: Handle error occurrence"""
        pass

    def _reset_system(self, **kwargs):
        """Action: Reset the system"""
        pass
```

### Async State Machine (Python)
```python
import asyncio
from enum import Enum, auto
from typing import Dict, Callable, Optional

class AsyncStateMachine:
    """Asynchronous FSM implementation"""

    def __init__(self, initial_state: State):
        self.current_state = initial_state
        self._event_queue: asyncio.Queue = asyncio.Queue()
        self._running = False

    async def start(self):
        """Start processing events"""
        self._running = True
        while self._running:
            event = await self._event_queue.get()
            await self._process_event(event)

    async def send_event(self, event: Event, **kwargs):
        """Queue an event for processing"""
        await self._event_queue.put((event, kwargs))

    async def _process_event(self, event_data):
        """Process a single event"""
        event, kwargs = event_data
        # Transition logic here
        pass
```

## TypeScript Implementation

### Type-Safe State Machine
```typescript
// Generated State and Event types
enum State {
    Idle = "IDLE",
    Running = "RUNNING",
    Paused = "PAUSED",
    Error = "ERROR",
    Completed = "COMPLETED"
}

enum Event {
    Start = "START",
    Pause = "PAUSE",
    Resume = "RESUME",
    Stop = "STOP",
    ErrorOccurred = "ERROR_OCCURRED",
    Reset = "RESET"
}

interface StateContext {
    [key: string]: any;
}

interface Transition {
    from: State;
    event: Event;
    to: State;
    action?: (context: StateContext) => void | Promise<void>;
    guard?: (context: StateContext) => boolean;
}

class StateMachine {
    private currentState: State;
    private context: StateContext = {};
    private transitions: Map<string, Transition>;
    private entryActions: Map<State, () => void> = new Map();
    private exitActions: Map<State, () => void> = new Map();

    constructor(initialState: State = State.Idle) {
        this.currentState = initialState;
        this.transitions = this.setupTransitions();
    }

    private setupTransitions(): Map<string, Transition> {
        const transitions: Transition[] = [
            {
                from: State.Idle,
                event: Event.Start,
                to: State.Running,
                action: (ctx) => this.startProcess(ctx)
            },
            {
                from: State.Running,
                event: Event.Pause,
                to: State.Paused,
                action: (ctx) => this.pauseProcess(ctx)
            },
            {
                from: State.Running,
                event: Event.Stop,
                to: State.Idle,
                action: (ctx) => this.stopProcess(ctx)
            },
            {
                from: State.Running,
                event: Event.ErrorOccurred,
                to: State.Error,
                action: (ctx) => this.handleError(ctx)
            },
            {
                from: State.Paused,
                event: Event.Resume,
                to: State.Running,
                action: (ctx) => this.resumeProcess(ctx)
            },
            {
                from: State.Error,
                event: Event.Reset,
                to: State.Idle,
                action: (ctx) => this.resetSystem(ctx)
            }
        ];

        const map = new Map<string, Transition>();
        transitions.forEach(t => {
            map.set(`${t.from}:${t.event}`, t);
        });

        return map;
    }

    async processEvent(event: Event, data?: any): Promise<boolean> {
        const key = `${this.currentState}:${event}`;
        const transition = this.transitions.get(key);

        if (!transition) {
            console.warn(`Invalid transition: ${this.currentState} + ${event}`);
            return false;
        }

        // Check guard condition
        if (transition.guard && !transition.guard(this.context)) {
            console.info(`Guard condition failed for transition: ${key}`);
            return false;
        }

        // Execute exit action
        const exitAction = this.exitActions.get(this.currentState);
        if (exitAction) {
            exitAction();
        }

        // Execute transition action
        if (transition.action) {
            await transition.action({ ...this.context, data });
        }

        // Change state
        const previousState = this.currentState;
        this.currentState = transition.to;
        console.log(`Transitioned: ${previousState} -> ${this.currentState}`);

        // Execute entry action
        const entryAction = this.entryActions.get(this.currentState);
        if (entryAction) {
            entryAction();
        }

        return true;
    }

    getCurrentState(): State {
        return this.currentState;
    }

    // Action implementations
    private startProcess(context: StateContext): void {
        console.log("Starting process...");
    }

    private pauseProcess(context: StateContext): void {
        console.log("Pausing process...");
    }

    private resumeProcess(context: StateContext): void {
        console.log("Resuming process...");
    }

    private stopProcess(context: StateContext): void {
        console.log("Stopping process...");
    }

    private handleError(context: StateContext): void {
        console.error("Handling error...", context.data);
    }

    private resetSystem(context: StateContext): void {
        console.log("Resetting system...");
        this.context = {};
    }
}

// Usage example
const fsm = new StateMachine(State.Idle);
await fsm.processEvent(Event.Start);
await fsm.processEvent(Event.Pause);
await fsm.processEvent(Event.Resume);
```

## Go Implementation

### Interface-Based State Pattern
```go
package fsm

import (
    "fmt"
    "sync"
)

// State interface
type State interface {
    Name() string
    OnEnter(ctx *Context)
    OnExit(ctx *Context)
    HandleEvent(event Event, ctx *Context) (State, error)
}

// Event type
type Event string

const (
    EventStart   Event = "START"
    EventPause   Event = "PAUSE"
    EventResume  Event = "RESUME"
    EventStop    Event = "STOP"
    EventError   Event = "ERROR"
    EventReset   Event = "RESET"
)

// Context holds state machine data
type Context struct {
    Data map[string]interface{}
    mu   sync.RWMutex
}

// Base state implementation
type BaseState struct {
    name string
}

func (s *BaseState) Name() string {
    return s.name
}

func (s *BaseState) OnEnter(ctx *Context) {
    fmt.Printf("Entering state: %s\n", s.name)
}

func (s *BaseState) OnExit(ctx *Context) {
    fmt.Printf("Exiting state: %s\n", s.name)
}

// Concrete states
type IdleState struct {
    BaseState
}

func NewIdleState() *IdleState {
    return &IdleState{
        BaseState{name: "IDLE"},
    }
}

func (s *IdleState) HandleEvent(event Event, ctx *Context) (State, error) {
    switch event {
    case EventStart:
        return NewRunningState(), nil
    default:
        return nil, fmt.Errorf("invalid event %s for state %s", event, s.Name())
    }
}

type RunningState struct {
    BaseState
}

func NewRunningState() *RunningState {
    return &RunningState{
        BaseState{name: "RUNNING"},
    }
}

func (s *RunningState) HandleEvent(event Event, ctx *Context) (State, error) {
    switch event {
    case EventPause:
        return NewPausedState(), nil
    case EventStop:
        return NewIdleState(), nil
    case EventError:
        return NewErrorState(), nil
    default:
        return nil, fmt.Errorf("invalid event %s for state %s", event, s.Name())
    }
}

// StateMachine manages states and transitions
type StateMachine struct {
    currentState State
    context      *Context
    mu           sync.Mutex
}

func NewStateMachine(initialState State) *StateMachine {
    return &StateMachine{
        currentState: initialState,
        context:      &Context{Data: make(map[string]interface{})},
    }
}

func (sm *StateMachine) ProcessEvent(event Event) error {
    sm.mu.Lock()
    defer sm.mu.Unlock()

    newState, err := sm.currentState.HandleEvent(event, sm.context)
    if err != nil {
        return err
    }

    if newState != nil {
        sm.currentState.OnExit(sm.context)
        sm.currentState = newState
        sm.currentState.OnEnter(sm.context)
    }

    return nil
}

func (sm *StateMachine) CurrentState() string {
    sm.mu.Lock()
    defer sm.mu.Unlock()
    return sm.currentState.Name()
}
```

## Java Implementation

### Enum-Based State Pattern
```java
package com.example.fsm;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.BiPredicate;

// State enum with behavior
public enum State {
    IDLE {
        @Override
        public State processEvent(Event event, Context context) {
            if (event == Event.START) {
                return RUNNING;
            }
            return null;
        }
    },

    RUNNING {
        @Override
        public State processEvent(Event event, Context context) {
            switch (event) {
                case PAUSE:
                    return PAUSED;
                case STOP:
                    return IDLE;
                case ERROR_OCCURRED:
                    return ERROR;
                default:
                    return null;
            }
        }
    },

    PAUSED {
        @Override
        public State processEvent(Event event, Context context) {
            switch (event) {
                case RESUME:
                    return RUNNING;
                case STOP:
                    return IDLE;
                default:
                    return null;
            }
        }
    },

    ERROR {
        @Override
        public State processEvent(Event event, Context context) {
            if (event == Event.RESET) {
                return IDLE;
            }
            return null;
        }
    };

    public abstract State processEvent(Event event, Context context);
}

// Event enum
public enum Event {
    START,
    PAUSE,
    RESUME,
    STOP,
    ERROR_OCCURRED,
    RESET
}

// Context class
public class Context {
    private Map<String, Object> data = new HashMap<>();

    public void set(String key, Object value) {
        data.put(key, value);
    }

    public <T> T get(String key, Class<T> type) {
        return type.cast(data.get(key));
    }
}

// State Machine class
public class StateMachine {
    private State currentState;
    private Context context;
    private Map<State, Runnable> entryActions;
    private Map<State, Runnable> exitActions;
    private Map<String, BiConsumer<Event, Context>> transitionActions;

    public StateMachine(State initialState) {
        this.currentState = initialState;
        this.context = new Context();
        this.entryActions = new HashMap<>();
        this.exitActions = new HashMap<>();
        this.transitionActions = new HashMap<>();
        setupActions();
    }

    private void setupActions() {
        // Entry actions
        entryActions.put(State.RUNNING, () -> System.out.println("Starting process..."));
        entryActions.put(State.PAUSED, () -> System.out.println("Process paused"));
        entryActions.put(State.ERROR, () -> System.out.println("Error state entered"));

        // Exit actions
        exitActions.put(State.RUNNING, () -> System.out.println("Leaving running state"));

        // Transition actions
        transitionActions.put("IDLE:START", (e, c) -> initializeProcess());
        transitionActions.put("RUNNING:STOP", (e, c) -> cleanupProcess());
    }

    public boolean processEvent(Event event) {
        State newState = currentState.processEvent(event, context);

        if (newState == null) {
            System.out.println("Invalid transition: " + currentState + " + " + event);
            return false;
        }

        // Execute exit action
        Runnable exitAction = exitActions.get(currentState);
        if (exitAction != null) {
            exitAction.run();
        }

        // Execute transition action
        String transitionKey = currentState + ":" + event;
        BiConsumer<Event, Context> transitionAction = transitionActions.get(transitionKey);
        if (transitionAction != null) {
            transitionAction.accept(event, context);
        }

        // Change state
        State previousState = currentState;
        currentState = newState;
        System.out.println("Transitioned: " + previousState + " -> " + currentState);

        // Execute entry action
        Runnable entryAction = entryActions.get(currentState);
        if (entryAction != null) {
            entryAction.run();
        }

        return true;
    }

    public State getCurrentState() {
        return currentState;
    }

    private void initializeProcess() {
        System.out.println("Initializing process...");
    }

    private void cleanupProcess() {
        System.out.println("Cleaning up process...");
    }

    // Usage
    public static void main(String[] args) {
        StateMachine fsm = new StateMachine(State.IDLE);

        fsm.processEvent(Event.START);
        fsm.processEvent(Event.PAUSE);
        fsm.processEvent(Event.RESUME);
        fsm.processEvent(Event.STOP);
    }
}
```

## C Implementation

### Function Pointer Based FSM
```c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// State and Event enums
typedef enum {
    STATE_IDLE,
    STATE_RUNNING,
    STATE_PAUSED,
    STATE_ERROR,
    STATE_COUNT
} State;

typedef enum {
    EVENT_START,
    EVENT_PAUSE,
    EVENT_RESUME,
    EVENT_STOP,
    EVENT_ERROR,
    EVENT_RESET,
    EVENT_COUNT
} Event;

// Context structure
typedef struct {
    void* data;
    int error_code;
    char message[256];
} Context;

// State machine structure
typedef struct {
    State current_state;
    Context context;
    State (*transitions[STATE_COUNT][EVENT_COUNT])(Context*);
    void (*entry_actions[STATE_COUNT])(Context*);
    void (*exit_actions[STATE_COUNT])(Context*);
} StateMachine;

// State transition functions
State idle_to_running(Context* ctx) {
    printf("Starting process...\n");
    return STATE_RUNNING;
}

State running_to_paused(Context* ctx) {
    printf("Pausing process...\n");
    return STATE_PAUSED;
}

State running_to_idle(Context* ctx) {
    printf("Stopping process...\n");
    return STATE_IDLE;
}

State running_to_error(Context* ctx) {
    printf("Error occurred: %s\n", ctx->message);
    return STATE_ERROR;
}

State paused_to_running(Context* ctx) {
    printf("Resuming process...\n");
    return STATE_RUNNING;
}

State error_to_idle(Context* ctx) {
    printf("Resetting system...\n");
    ctx->error_code = 0;
    return STATE_IDLE;
}

// Initialize state machine
void init_state_machine(StateMachine* fsm) {
    // Initialize all transitions to NULL
    for (int i = 0; i < STATE_COUNT; i++) {
        for (int j = 0; j < EVENT_COUNT; j++) {
            fsm->transitions[i][j] = NULL;
        }
        fsm->entry_actions[i] = NULL;
        fsm->exit_actions[i] = NULL;
    }

    // Set up valid transitions
    fsm->transitions[STATE_IDLE][EVENT_START] = idle_to_running;
    fsm->transitions[STATE_RUNNING][EVENT_PAUSE] = running_to_paused;
    fsm->transitions[STATE_RUNNING][EVENT_STOP] = running_to_idle;
    fsm->transitions[STATE_RUNNING][EVENT_ERROR] = running_to_error;
    fsm->transitions[STATE_PAUSED][EVENT_RESUME] = paused_to_running;
    fsm->transitions[STATE_PAUSED][EVENT_STOP] = running_to_idle;
    fsm->transitions[STATE_ERROR][EVENT_RESET] = error_to_idle;

    // Initialize state
    fsm->current_state = STATE_IDLE;
    memset(&fsm->context, 0, sizeof(Context));
}

// Process event
int process_event(StateMachine* fsm, Event event) {
    State (*transition_func)(Context*) = fsm->transitions[fsm->current_state][event];

    if (transition_func == NULL) {
        printf("Invalid transition: State %d + Event %d\n", fsm->current_state, event);
        return 0;
    }

    // Execute exit action
    if (fsm->exit_actions[fsm->current_state] != NULL) {
        fsm->exit_actions[fsm->current_state](&fsm->context);
    }

    // Execute transition and get new state
    State new_state = transition_func(&fsm->context);

    // Update state
    State old_state = fsm->current_state;
    fsm->current_state = new_state;
    printf("Transitioned: %d -> %d\n", old_state, new_state);

    // Execute entry action
    if (fsm->entry_actions[fsm->current_state] != NULL) {
        fsm->entry_actions[fsm->current_state](&fsm->context);
    }

    return 1;
}

// Usage example
int main() {
    StateMachine fsm;
    init_state_machine(&fsm);

    process_event(&fsm, EVENT_START);
    process_event(&fsm, EVENT_PAUSE);
    process_event(&fsm, EVENT_RESUME);
    process_event(&fsm, EVENT_STOP);

    return 0;
}
```

## Test Generation Template

### Python Unit Tests
```python
import unittest
from unittest.mock import Mock, patch
from fsm import StateMachine, State, Event

class TestStateMachine(unittest.TestCase):
    def setUp(self):
        self.fsm = StateMachine(State.IDLE)

    def test_initial_state(self):
        self.assertEqual(self.fsm.current_state, State.IDLE)

    def test_valid_transition_idle_to_running(self):
        result = self.fsm.process_event(Event.START)
        self.assertTrue(result)
        self.assertEqual(self.fsm.current_state, State.RUNNING)

    def test_invalid_transition(self):
        result = self.fsm.process_event(Event.PAUSE)  # Can't pause from idle
        self.assertFalse(result)
        self.assertEqual(self.fsm.current_state, State.IDLE)

    def test_transition_sequence(self):
        transitions = [
            (Event.START, State.RUNNING),
            (Event.PAUSE, State.PAUSED),
            (Event.RESUME, State.RUNNING),
            (Event.STOP, State.IDLE),
        ]

        for event, expected_state in transitions:
            self.fsm.process_event(event)
            self.assertEqual(self.fsm.current_state, expected_state)

    def test_guard_condition(self):
        # Test with guard condition that fails
        self.fsm.context['battery_level'] = 10
        result = self.fsm.process_event(Event.START)
        self.assertFalse(result)  # Guard should prevent transition

    @patch('fsm.StateMachine._start_process')
    def test_action_execution(self, mock_action):
        self.fsm.process_event(Event.START)
        mock_action.assert_called_once()

if __name__ == '__main__':
    unittest.main()
```

## Documentation Generation

### Auto-generated Markdown Documentation
```markdown
# State Machine: ProcessController

## States
- **IDLE**: System is idle and ready to start
- **RUNNING**: Process is actively running
- **PAUSED**: Process is temporarily suspended
- **ERROR**: Error state requiring reset
- **COMPLETED**: Process finished successfully

## Events
- **START**: Begin process execution
- **PAUSE**: Temporarily suspend process
- **RESUME**: Continue suspended process
- **STOP**: Terminate process
- **ERROR_OCCURRED**: Error detected
- **RESET**: Clear error and return to idle

## Transitions

| From | Event | To | Guard | Action |
|------|-------|-----|-------|--------|
| IDLE | START | RUNNING | battery > 20% | initialize() |
| RUNNING | PAUSE | PAUSED | - | save_state() |
| RUNNING | STOP | IDLE | - | cleanup() |
| RUNNING | ERROR_OCCURRED | ERROR | - | log_error() |
| PAUSED | RESUME | RUNNING | - | restore_state() |
| PAUSED | STOP | IDLE | - | cleanup() |
| ERROR | RESET | IDLE | - | clear_error() |

## Usage Example
```python
fsm = ProcessController()
fsm.start()  # IDLE -> RUNNING
fsm.pause()  # RUNNING -> PAUSED
fsm.resume() # PAUSED -> RUNNING
fsm.stop()   # RUNNING -> IDLE
```
```