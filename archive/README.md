# Archive

Historical and deprecated versions of the Riemann-Roch formalization.

**These files are NOT part of the build.** They are preserved for reference only.

## Files

### RR_v1_axiom_based.lean (Cycles 1-16)
- **Approach**: Axiom-based with `FunctionFieldData` structure
- **Status**: Complete but mathematically circular (RR is an axiom)
- **Lines**: ~1,320
- **Key structures**: `FunctionFieldData`, `RRData`, `RRDataWithRR`

### RR_v2_monolithic.lean (Cycles 17-39)
- **Approach**: Constructive Dedekind domain (HeightOneSpectrum R)
- **Status**: Archived after Cycle 40 modularization
- **Lines**: ~2,531
- **Note**: This was the monolithic file before splitting into modules

### LocalGapInstance.lean (Cycles 25-39)
- **Approach**: Local gap bound via DVR machinery
- **Status**: Superseded by adelic approach
- **Lines**: ~4,000+
- **Note**: Contains detailed DVR lemmas that may be useful for reference

### TestBlockerProofs.lean
- **Status**: Test file for debugging proof strategies
- **Note**: Contains isolated proof attempts for blocked lemmas

### random/
Miscellaneous archived files:
- `BUILD_PATH_SORRIES.md` - Old sorry tracking (superseded by ledger)
- `handoff_cycle68.md` - Historical handoff notes

### docs/
Old documentation:
- `for_humans.md` - Early human-readable explanation
- `index.html` - Generated documentation page

### problem/
Original problem statement:
- `problem.md` - Initial formalization goals

## Current Active Code

The active formalization is modular, located in `RrLean/RiemannRochV2/`.
See `state/ledger.md` for current status and next steps.
