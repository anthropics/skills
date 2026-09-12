# FSM Visualization Examples

This file demonstrates different visualization formats for finite state machines.

## Mermaid Diagram Examples

### Simple State Machine
```mermaid
stateDiagram-v2
    [*] --> Idle
    Idle --> Working: start
    Working --> Idle: stop
    Working --> Error: error
    Error --> Idle: reset
    Idle --> [*]: shutdown
```

### Traffic Light with Styling
```mermaid
stateDiagram-v2
    direction LR

    [*] --> Red
    Red --> Green: timer
    Green --> Yellow: timer
    Yellow --> Red: timer

    Red --> [*]: power_off

    classDef redState fill:#ff0000,color:#fff
    classDef yellowState fill:#ffff00,color:#000
    classDef greenState fill:#00ff00,color:#000

    class Red redState
    class Yellow yellowState
    class Green greenState
```

### Hierarchical State Machine
```mermaid
stateDiagram-v2
    [*] --> Operational

    state Operational {
        [*] --> Idle
        Idle --> Processing
        Processing --> Idle
        Processing --> Paused
        Paused --> Processing
    }

    Operational --> Maintenance: maintenance_required

    state Maintenance {
        [*] --> Diagnostic
        Diagnostic --> Repair
        Repair --> Testing
        Testing --> [*]: complete
    }

    Maintenance --> Operational: maintenance_complete
    Operational --> [*]: shutdown
```

### Parallel Regions
```mermaid
stateDiagram-v2
    state System {
        state "Network Layer" as Network {
            [*] --> Disconnected
            Disconnected --> Connecting: connect
            Connecting --> Connected: success
            Connected --> Disconnected: disconnect
        }
        --
        state "Application Layer" as App {
            [*] --> Stopped
            Stopped --> Starting: start
            Starting --> Running: ready
            Running --> Stopped: stop
        }
    }
```

## GraphViz DOT Format Examples

### Basic State Machine
```dot
digraph BasicFSM {
    rankdir=LR;
    size="8,5"

    node [shape = doublecircle]; Start End;
    node [shape = circle];

    Start -> State1 [label = "initialize"];
    State1 -> State2 [label = "event1"];
    State2 -> State3 [label = "event2"];
    State3 -> State1 [label = "reset"];
    State3 -> End [label = "complete"];
}
```

### TCP Connection FSM
```dot
digraph TCP {
    rankdir=TB;
    size="10,8"

    node [shape = ellipse, style=filled, fillcolor=lightblue];
    edge [fontsize=10];

    // Initial state
    node [shape = doublecircle, fillcolor=lightgreen];
    CLOSED;

    // Normal states
    node [shape = ellipse];

    CLOSED -> LISTEN [label="passive\nopen"];
    CLOSED -> SYN_SENT [label="active\nopen"];

    LISTEN -> SYN_RCVD [label="SYN\nreceived"];
    LISTEN -> CLOSED [label="close"];

    SYN_SENT -> ESTABLISHED [label="SYN+ACK\nreceived"];
    SYN_SENT -> CLOSED [label="timeout"];

    SYN_RCVD -> ESTABLISHED [label="ACK\nreceived"];
    SYN_RCVD -> FIN_WAIT_1 [label="close"];

    ESTABLISHED -> FIN_WAIT_1 [label="close"];
    ESTABLISHED -> CLOSE_WAIT [label="FIN\nreceived"];

    FIN_WAIT_1 -> FIN_WAIT_2 [label="ACK\nreceived"];
    FIN_WAIT_1 -> CLOSING [label="FIN\nreceived"];
    FIN_WAIT_1 -> TIME_WAIT [label="FIN+ACK\nreceived"];

    FIN_WAIT_2 -> TIME_WAIT [label="FIN\nreceived"];

    CLOSE_WAIT -> LAST_ACK [label="close"];

    LAST_ACK -> CLOSED [label="ACK\nreceived"];

    CLOSING -> TIME_WAIT [label="ACK\nreceived"];

    TIME_WAIT -> CLOSED [label="timeout\n2MSL"];
}
```

### Hierarchical States with Subgraphs
```dot
digraph HierarchicalFSM {
    compound=true;
    rankdir=LR;

    subgraph cluster_operational {
        label="Operational";
        style=filled;
        fillcolor=lightgray;

        Idle -> Working [label="start"];
        Working -> Idle [label="stop"];
        Working -> Paused [label="pause"];
        Paused -> Working [label="resume"];
    }

    subgraph cluster_maintenance {
        label="Maintenance";
        style=filled;
        fillcolor=lightyellow;

        Checking -> Repairing [label="issue found"];
        Repairing -> Testing [label="repair done"];
        Testing -> Checking [label="test failed"];
    }

    Start [shape=doublecircle];
    Start -> Idle [lhead=cluster_operational];
    Working -> Checking [ltail=cluster_operational, lhead=cluster_maintenance, label="maintenance"];
    Testing -> Idle [ltail=cluster_maintenance, lhead=cluster_operational, label="complete"];
}
```

## ASCII Art Diagrams

### Simple Linear Flow
```
     ┌─────────┐  start   ┌─────────┐  process  ┌─────────┐  finish  ┌─────────┐
  ●──│  Init   │─────────>│  Ready  │──────────>│ Working │────────>│  Done   │──●
     └─────────┘          └─────────┘           └─────────┘         └─────────┘
```

### Cyclic State Machine
```
                    ┌──────────┐
                    │          │
                    ▼          │ reset
     ┌─────────┐  start  ┌─────────┐  error  ┌─────────┐
  ●──│  Idle   │────────>│ Running │────────>│  Error  │
     └─────────┘         └─────────┘         └─────────┘
          ▲                   │                    │
          │                   │ stop               │ fix
          └───────────────────┴────────────────────┘
```

### Branching State Machine
```
                         ┌─────────────┐
                    ┌───>│  Success    │───┐
                    │    └─────────────┘   │
                    │                       ▼
     ┌─────────┐  run   ┌─────────┐   ┌─────────┐
  ●──│  Start  │───────>│ Process │   │  Done   │──●
     └─────────┘        └─────────┘   └─────────┘
                             │              ▲
                             │              │
                             ▼              │
                        ┌─────────┐        │
                        │  Failed │────────┘
                        └─────────┘ retry
```

## State Transition Tables

### Simple Table Format
```markdown
| Current State | Event | Next State | Action |
|--------------|-------|------------|---------|
| Idle | start | Running | initialize() |
| Running | pause | Paused | save_state() |
| Running | stop | Idle | cleanup() |
| Running | error | Error | log_error() |
| Paused | resume | Running | restore_state() |
| Paused | stop | Idle | cleanup() |
| Error | reset | Idle | clear_error() |
```

### Extended Table with Guards
```markdown
| Current State | Event | Guard Condition | Next State | Action |
|--------------|-------|-----------------|------------|---------|
| Idle | start | battery > 20% | Running | start_motor() |
| Idle | start | battery <= 20% | LowPower | show_warning() |
| Running | speed_change | speed > limit | Warning | reduce_speed() |
| Running | speed_change | speed <= limit | Running | update_display() |
```

## PlantUML State Diagrams

### Basic PlantUML Example
```plantuml
@startuml
[*] --> Idle
Idle --> Active : start
Active --> Idle : stop
Active --> Suspended : suspend
Suspended --> Active : resume
Active --> [*] : terminate
@enduml
```

### PlantUML with Composite States
```plantuml
@startuml
state Active {
    [*] --> Working
    Working --> Waiting : wait
    Waiting --> Working : signal
    Working --> [*] : done
}

[*] --> Idle
Idle --> Active : start
Active --> Idle : complete
Active --> Error : error
Error --> Idle : reset
Idle --> [*] : shutdown
@enduml
```

## Code Generation Preview

### Generated from Mermaid
When you provide a Mermaid diagram, the FSM generator can produce:
- State enum/constants
- Transition mappings
- Event handlers
- State machine class

### Generated from YAML
YAML definitions produce:
- Complete implementation with guards
- Action methods
- State entry/exit handlers
- Hierarchical state support

### Generated from Tables
Transition tables generate:
- Lookup-based implementations
- Validation logic
- Test cases for each transition