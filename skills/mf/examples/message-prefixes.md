# z/OS Message Prefix Reference

Quick guide to z/OS message prefixes and their components.

## Common Prefixes

### TSO/ISPF

| Prefix | Component | Example |
|--------|-----------|---------|
| IKJ | TSO | IKJ56703I INVALID KEYWORD |
| ISP | ISPF | ISP004E UNABLE TO OPEN LIBRARY |
| ISR | ISPF Services | ISR001 MEMBER NOT FOUND |

### JES (Job Entry)

| Prefix | Component | Example |
|--------|-----------|---------|
| HASP | JES2 | HASP373 JOB NOT FOUND |
| IAT | JES3 | IAT6100 JOB QUEUED |
| IEF | Allocation/JCL | IEF285I DATASET DELETED |

### Security

| Prefix | Component | Example |
|--------|-----------|---------|
| ICH | RACF (Commands) | ICH408I USER NOT DEFINED |
| IRR | RACF (Server) | IRR012I VERIFICATION FAILED |

### Storage/SMS

| Prefix | Component | Example |
|--------|-----------|---------|
| IGD | SMS | IGD17101I DATASET ALLOCATED |
| IEC | I/O | IEC141I DATASET NOT FOUND |
| IDC | IDCAMS | IDC0014I LASTCC=8 |

### System

| Prefix | Component | Example |
|--------|-----------|---------|
| IEA | Supervisor | IEA995I SYMPTOM DUMP |
| IEE | Console | IEE136I JOB CANCELLED |
| IEW | Binder/Linkage | IEW2456E UNRESOLVED EXTERNAL |

### VTAM/Network

| Prefix | Component | Example |
|--------|-----------|---------|
| IST | VTAM | IST453I NODE ACTIVE |
| IKT | TCAS | IKT00300I LOGON RECONNECT |

### CICS

| Prefix | Component | Example |
|--------|-----------|---------|
| DFH | CICS | DFHAC2236 TRANSACTION ABENDED |

### DB2

| Prefix | Component | Example |
|--------|-----------|---------|
| DSN | DB2 | DSNC105I DB2 STARTED |
| DSNT | DB2 Trace | DSNT500I SQL ERROR |

### Language Environment

| Prefix | Component | Example |
|--------|-----------|---------|
| CEE | LE Runtime | CEE3201S ABEND S0C7 |
| EDC | C Runtime | EDC5129I OPEN FAILED |
| IGZ | COBOL | IGZ0035S INVALID DATA |

## Message Severity Codes

| Suffix | Meaning |
|--------|---------|
| I | Informational |
| W | Warning |
| E | Error |
| S | Severe |
| T | Terminal |

## Full Prefix List

| Prefix | Component |
|--------|-----------|
| ADR | DFDSS |
| ARC | DFHSM |
| ATB | APPC |
| BPX | USS/OMVS |
| CEE | Language Environment |
| CSV | Contents Supervisor |
| DFH | CICS |
| DMO | DFSMS |
| DSN | DB2 |
| EDC | C Runtime |
| EZB | TCP/IP |
| GIM | SMP/E |
| HASP | JES2 |
| IAT | JES3 |
| ICH | RACF |
| IDC | IDCAMS |
| IEA | Supervisor |
| IEB | Utilities |
| IEC | I/O |
| IEE | Console |
| IEF | Allocation |
| IEW | Binder |
| IGD | SMS |
| IGW | OAM |
| IGZ | COBOL |
| IKJ | TSO |
| IKT | TCAS |
| IRR | RACF Server |
| ISP | ISPF |
| ISR | ISPF Services |
| IST | VTAM |
| IXC | XCF |
| IXG | System Logger |

## Looking Up Messages

1. **IBM Knowledge Center**: Search "z/OS messages [PREFIX]"
2. **TSO HELP**: `HELP MSG(IEF285I)`
3. **SDSF**: Option "LOG" shows console messages
4. **Job Output**: Check JESMSGLG, JESJCL, JESYSMSG

## Common Message Examples

### Successful Job
```
IEF403I jobname - STARTED
IEF404I jobname - ENDED
```

### Dataset Allocation
```
IEF285I   dsname CATALOGED
IEF285I   dsname DELETED
IGD17101I dsname ALLOCATED TO VOLUME volser
```

### Security Messages
```
ICH408I USER userid NOT DEFINED TO RACF
ICH70001I userid LAST ACCESS datetime
IRR012I VERIFICATION FAILED
```

### ABEND Messages
```
IEA995I SYMPTOM DUMP OUTPUT
CEE3201S The system detected an operation exception
```
