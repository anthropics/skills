# ABEND Code Reference

Quick reference for common IBM z/OS abend codes.

## System Abends (Sxxx)

### Storage/Memory

| Code | Name | Cause | Fix |
|------|------|-------|-----|
| S0C1 | Operation Exception | Invalid instruction executed | Check compile options, load module integrity |
| S0C4 | Protection Exception | Invalid memory address | Check pointers, array bounds, linkage section |
| S0C5 | Addressing Exception | Address outside memory | Check BASE registers, DSECT alignment |
| S0C6 | Specification Exception | Invalid instruction operand | Check alignment, register usage |
| S0C7 | Data Exception | Invalid packed decimal | Check COMP-3 fields, MOVE statements, INITIALIZE |
| S0CB | Division by Zero | Divide by zero | Add zero-check before DIVIDE |

### Dataset/File

| Code | Name | Cause | Fix |
|------|------|-------|-----|
| S001 | I/O Error | Read/write failure | Check dataset, UNIT, DISP |
| S013 | DCB Conflict | DCB mismatch on open | Match RECFM/LRECL/BLKSIZE |
| S213 | Dataset Not Found | OPEN failed | Check DSN spelling, catalog |
| SB14 | Close Error | Close failed | Check for prior I/O errors |
| SB37 | Out of Space | No room to extend | Increase SPACE, compress PDS |
| SD37 | No Secondary | No secondary allocation | Add secondary space |
| SE37 | Max Extents | 16 extents reached | Reallocate with larger primary |

### Module/Program

| Code | Name | Cause | Fix |
|------|------|-------|-----|
| S106 | Module Not Found | LOAD/LINK failed | Check STEPLIB, linklist |
| S806 | Module Not Found | LOAD/FETCH failed | Check STEPLIB, spelling |
| S80A | Not Enough Storage | GETMAIN failed | Increase REGION |

### Time/Limits

| Code | Name | Cause | Fix |
|------|------|-------|-----|
| S122 | Operator Cancel | Job cancelled by operator | Check with operations |
| S222 | Operator Cancel | TIME exceeded | Increase TIME or check with ops |
| S322 | CPU Time Exceeded | Runaway or long job | Increase TIME=, check for loops |
| S522 | Wait Time Exceeded | Job waiting too long | Check for ENQ contention, tape mounts |
| S622 | SYSOUT Exceeded | Output limit reached | Increase OUTLIM |
| S722 | Lines Exceeded | Too many print lines | Increase LINES= or fix loop |

### Security

| Code | Name | Cause | Fix |
|------|------|-------|-----|
| S913 | RACF Not Authorized | Security violation | Request access via RACF admin |
| S913-38 | Dataset Protected | No READ access | Request READ permission |
| S913-3C | Dataset Protected | No UPDATE access | Request UPDATE permission |

## User Abends (Uxxx)

User abends are application-defined. Common ranges:

| Range | Typical Usage |
|-------|---------------|
| U0001-U0100 | Application validation errors |
| U0100-U0999 | Business logic errors |
| U1000-U1999 | File/database errors |
| U2000-U2999 | Communication errors |
| U3000-U3999 | System interface errors |
| U4038 | CICS transaction abend |
| U4093 | CICS resource unavailable |

## Quick Diagnosis

### S0C7 Checklist
1. Check WORKING-STORAGE COMP-3 fields are initialized
2. Check MOVE statements to packed fields
3. Look for uninitialized input data
4. Check REDEFINES of numeric fields
5. Verify file record alignment

### S0C4 Checklist
1. Check array subscripts (bounds)
2. Check pointer/address fields
3. Verify LINKAGE SECTION matches caller
4. Check BLL cells (CICS)
5. Look for wild branches

### S806/S106 Checklist
1. Check program name spelling
2. Verify STEPLIB/JOBLIB DD
3. Check if module exists in library
4. Verify library concatenation order
5. Check for ALIAS entries

## Reading Dumps

Key areas to examine:

1. **PSW** - Program Status Word shows failing instruction address
2. **Registers** - R14 = return address, R15 = entry point
3. **Save Area Trace** - Shows call chain
4. **Working Storage** - Check field values at time of failure
5. **TCB** - Task Control Block for system info

## ABEND Codes by Message Prefix

| Prefix | Component | Related Abends |
|--------|-----------|----------------|
| IEA | Supervisor | S0Cx, S1xx, S2xx |
| IEC | I/O | S001, S013, SB37 |
| IEF | Allocation | S213, S413, S613 |
| ICH | RACF | S913 |
| IGD | SMS | SB37, SD37, SE37 |
