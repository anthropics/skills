---
name: mf
description: Mainframe super power - AI assistant for IBM z/OS mainframes. Use when user asks about JCL, ABEND codes, 3270 screens, RACF security, COBOL, TSO/ISPF, CICS, datasets, or any mainframe topic. Provides JCL generation, ABEND decoding, message explanation, and educational guidance for mainframe beginners and experts.
---

# Mainframe Super Power

A comprehensive AI-powered mainframe assistant that helps anyone work with IBM mainframes - from beginners learning the basics to experts debugging production issues.

## Core Capabilities

### 1. JCL Forge
Generate JCL from natural language requests:
- Compile jobs (COBOL, PL/I, Assembler, C)
- Copy/move/delete datasets
- Run batch programs
- IDCAMS utilities (VSAM, GDG, catalog)
- Sort/merge operations
- Proper DD statements, DCB parameters, DISP handling

### 2. ABEND Doctor
Decode any abend code and provide actionable fixes:
- System abends (S0C1, S0C4, S0C7, S0CB, S106, S213, S322, S806, S913, SB37...)
- User abends (U0001-U4095)
- Root cause analysis
- Step-by-step resolution

### 3. Message Decoder
Explain any z/OS message code:
- IKJ (TSO), IEF (JES/Allocation), ICH/IRR (RACF)
- IGD (SMS), IEC (I/O), IST (VTAM), DFH (CICS)
- DSN (DB2), HASP/IAT (JES2/JES3)
- 50+ message prefixes covered

### 4. Screen Whisperer
Explain any 3270 terminal screen:
- Identify current application (VTAM, TSO, ISPF, CICS, JES)
- Available actions and navigation
- Field meanings and data displayed
- What to do next

### 5. Dataset Navigator
Understand z/OS dataset concepts:
- PDS vs sequential vs VSAM
- Dataset naming conventions (HLQ, qualifiers)
- Attributes (DSORG, RECFM, LRECL, BLKSIZE)
- GDG base and generations
- Catalog structure

## Usage

Invoke with `/mf` followed by your question or command:

```
/mf jcl compile cobol program PAYROLL from MY.SOURCE
/mf abend S0C7
/mf msg IKJ56703I
/mf what is a PDS?
/mf how do I submit a batch job?
```

Or just ask any mainframe question naturally.

## Guidelines

When responding to mainframe questions:

1. **Start with the answer** - Don't bury the lede
2. **Explain the why** - Help them understand concepts
3. **Provide examples** - Working JCL, commands, screens
4. **Warn about gotchas** - Common mistakes to avoid
5. **Suggest next steps** - What to do after

## ABEND Quick Reference

### Critical System Abends

| Code | Name | Cause | Fix |
|------|------|-------|-----|
| S0C1 | Operation Exception | Invalid instruction | Check compile options, load module |
| S0C4 | Protection Exception | Bad memory access | Check pointers, subscripts, linkage |
| S0C7 | Data Exception | Invalid packed decimal | Check COMP-3 fields, INITIALIZE |
| S0CB | Division by Zero | Divide by zero | Add zero check before DIVIDE |
| S106 | Module Not Found | LOAD failed | Check STEPLIB, linklist |
| S213 | Dataset Not Found | OPEN failed | Check DSN spelling, catalog |
| S322 | CPU Time Exceeded | Runaway job | Increase TIME=, check loops |
| S806 | Module Not Found | FETCH failed | Check STEPLIB, program name |
| S913 | Not Authorized | RACF denied | Request access via security admin |
| SB37 | Out of Space | Dataset full | Increase SPACE, compress PDS |

### S0C7 Diagnosis Checklist
1. Check WORKING-STORAGE COMP-3 fields are initialized
2. Check MOVE statements to packed fields
3. Look for uninitialized input data
4. Check REDEFINES of numeric fields
5. Verify file record alignment

### S0C4 Diagnosis Checklist
1. Check array subscripts (bounds)
2. Check pointer/address fields
3. Verify LINKAGE SECTION matches caller
4. Check BLL cells (CICS)
5. Look for wild branches

## JCL Templates

### Compile COBOL
```jcl
//COMPILE  JOB (ACCT),'COBOL COMPILE',CLASS=A,MSGCLASS=X,
//             MSGLEVEL=(1,1),NOTIFY=&SYSUID
//STEP1    EXEC IGYWCL
//COBOL.SYSIN DD DSN=&SYSUID..SOURCE(MYPROG),DISP=SHR
//LKED.SYSLMOD DD DSN=&SYSUID..LOAD(MYPROG),DISP=SHR
```

### Copy Dataset (IEBGENER)
```jcl
//COPY     JOB (ACCT),'COPY',CLASS=A,MSGCLASS=X,NOTIFY=&SYSUID
//STEP1    EXEC PGM=IEBGENER
//SYSUT1   DD DSN=INPUT.DATASET,DISP=SHR
//SYSUT2   DD DSN=OUTPUT.DATASET,DISP=(NEW,CATLG),
//            SPACE=(CYL,(10,5)),UNIT=SYSDA
//SYSPRINT DD SYSOUT=*
//SYSIN    DD DUMMY
```

### Delete Dataset (IDCAMS)
```jcl
//DELETE   JOB (ACCT),'DELETE',CLASS=A,MSGCLASS=X,NOTIFY=&SYSUID
//STEP1    EXEC PGM=IDCAMS
//SYSPRINT DD SYSOUT=*
//SYSIN    DD *
  DELETE MY.DATASET.NAME PURGE
  IF LASTCC = 8 THEN SET MAXCC = 0
/*
```

### Run Program with Input
```jcl
//RUN      JOB (ACCT),'RUN PGM',CLASS=A,MSGCLASS=X,NOTIFY=&SYSUID
//STEP1    EXEC PGM=MYPROG,PARM='OPTIONS'
//STEPLIB  DD DSN=MY.LOAD.LIBRARY,DISP=SHR
//INPUT    DD DSN=MY.INPUT.FILE,DISP=SHR
//OUTPUT   DD SYSOUT=*
//SYSUDUMP DD SYSOUT=*
```

### Allocate New Dataset
```jcl
//ALLOC    JOB (ACCT),'ALLOCATE',CLASS=A,MSGCLASS=X,NOTIFY=&SYSUID
//STEP1    EXEC PGM=IEFBR14
//NEWDS    DD DSN=MY.NEW.DATASET,DISP=(NEW,CATLG),
//            SPACE=(CYL,(10,5)),UNIT=SYSDA,
//            DCB=(RECFM=FB,LRECL=80,BLKSIZE=27920)
```

### Sort File
```jcl
//SORT     JOB (ACCT),'SORT',CLASS=A,MSGCLASS=X,NOTIFY=&SYSUID
//STEP1    EXEC PGM=SORT
//SORTIN   DD DSN=UNSORTED.FILE,DISP=SHR
//SORTOUT  DD DSN=SORTED.FILE,DISP=(NEW,CATLG),
//            SPACE=(CYL,(10,5)),UNIT=SYSDA
//SYSOUT   DD SYSOUT=*
//SYSIN    DD *
  SORT FIELDS=(1,10,CH,A)
/*
```

## Message Prefix Reference

| Prefix | Component | Description |
|--------|-----------|-------------|
| CEE | Language Environment | Runtime messages |
| DFH | CICS | Transaction processing |
| DSN | DB2 | Database messages |
| HASP | JES2 | Job entry subsystem |
| ICH/IRR | RACF | Security messages |
| IDC | IDCAMS | Catalog services |
| IEA | Supervisor | System control |
| IEB | Utilities | Data utilities |
| IEC | I/O | Input/output |
| IEF | Allocation | JCL processing |
| IEW | Binder | Link-edit |
| IGD | SMS | Storage management |
| IGZ | COBOL | COBOL runtime |
| IKJ | TSO | Time sharing |
| IST | VTAM | Network |

## Common Tasks

### How to submit a batch job
1. Create JCL in a PDS member
2. From TSO: `SUBMIT 'MY.JCL(JOBNAME)'`
3. From ISPF: Edit the JCL, type `SUBMIT` on command line
4. Check output: SDSF (=3.8 in ISPF) or `STATUS jobname`

### How to view job output
1. Enter SDSF: `=3.8` from ISPF or `SDSF` from TSO
2. Type `ST` for status display
3. Put `?` next to job to see DDs
4. Put `S` next to DD to view output

### How to copy a PDS member
```
From ISPF 3.3 (Move/Copy):
  From: 'SOURCE.PDS(MEMBER)'
  To:   'TARGET.PDS(MEMBER)'
```

### How to find a dataset
```
From ISPF 3.4 (DSLIST):
  Dsname Level: MY.DATA.*
```

## Beginner Concepts

**What is JCL?**
Job Control Language - tells z/OS what programs to run and what data they need. Like a shell script but for batch jobs.

**What is a dataset?**
A file on z/OS. Can be sequential (like a flat file) or partitioned (PDS - like a directory with members).

**What is TSO?**
Time Sharing Option - interactive command environment, like a shell. ISPF runs on top of TSO.

**What is ISPF?**
Interactive System Productivity Facility - menu-driven interface for editing, browsing, and managing datasets.

**What is a PDS?**
Partitioned Data Set - like a directory. Contains members (like files). Used for JCL libraries, source code, load modules.

**What is RACF?**
Resource Access Control Facility - z/OS security. Controls who can access what datasets and resources.

## Response Format

When answering questions, use this structure:

**Answer**: [Direct answer]

**Why**: [Explanation of the concept]

**Example**:
```
[Working JCL, command, or code]
```

**Watch out for**: [Common mistakes]

**Next**: [Suggested follow-up]
