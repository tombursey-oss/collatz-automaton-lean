# Lake Build Instructions for collatz_automaton

## Prerequisites

You need:
1. **Lean 4** (latest stable)
2. **Lake** (Lean's package manager, comes with Lean 4)
3. **git** (for cloning mathlib4)

### Windows Installation

#### Option 1: Using Lean4 Installer (Recommended)
1. Download from: https://github.com/leanprover/lean4/releases
2. Run the installer (e.g., `lean-4.X.X-windows.exe`)
3. Accept default paths (adds `lake` to PATH)

#### Option 2: Using elan (Lean version manager)
```powershell
# Install elan
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
irm https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex

# Then Lean 4 tools are automatically available
lake --version
```

## Build Instructions

Once Lake is installed:

```powershell
cd C:\collatz_automaton

# Update dependencies (fetches mathlib4 from GitHub)
lake update

# Build the project
lake build

# Optional: run the executable
lake run

# Optional: check specific file for errors
lake check
```

## Expected Output

```
Building CollatzAutomaton.Core
Building CollatzAutomaton.Data.BasinSummaryV2
Building CollatzAutomaton.Data.BasinVerificationV2
... (more data modules)
Building CollatzAutomaton.Graph
Building CollatzAutomaton.Lemma7_DriftInequality
Building CollatzAutomaton.Lemma8_DensityFloor
Building CollatzAutomaton.Lemma9_BasinCapture
Building CollatzAutomaton.MainTheorem
Building CollatzAutomaton
Finished CollatzAutomaton
```

## Troubleshooting

### "lake: not found"
- Lake is not in your PATH
- Try reinstalling Lean 4 or elan
- Or add Lean 4 to your PATH manually

### "Timeout downloading mathlib4"
- Network issue; try again after a few minutes
- Use `lake update` to retry

### "Type mismatch" or "Unknown identifier" errors
- Means there's a Lean syntax error in the files
- Report the full error message (line number, file name)

### "Tactic 'decide' failed"
- The `iterate_k` function for a row doesn't reduce to 1
- This would indicate an error in the basin verification data
- Check the stopping_time_steps value for that row

## File Structure

```
C:\collatz_automaton/
├── Lakefile.lean          # Lake configuration
├── src/
│   ├── Main.lean          # Executable entry point
│   ├── CollatzAutomaton.lean
│   ├── CollatzAutomaton/
│   │   ├── Core.lean      # Core types (State, Branch, etc.)
│   │   ├── Graph.lean     # Reachability and graph definitions
│   │   ├── Lemma7_DriftInequality.lean
│   │   ├── Lemma8_DensityFloor.lean
│   │   ├── Lemma9_BasinCapture.lean
│   │   ├── MainTheorem.lean
│   │   └── Data/          # Imported CSV data as Lean structures
│   │       ├── BasinSummaryV2.lean
│   │       ├── BasinVerificationV2.lean
│   │       ├── ExpandedEdgesV2.lean
│   │       ├── EdgeWeightsV0.lean
│   │       └── ... (more data files)
└── scripts/
    └── generate_basin_proofs.py  # Helper to generate proof lines
```

## Next Steps After Build Succeeds

1. **Check compilation**: If no errors, all proofs compile!
2. **Inspect proof details**: 
   ```powershell
   lake check CollatzAutomaton.MainTheorem
   ```
3. **Export results**:
   ```powershell
   # Optional: build documentation
   lake doc
   ```

---

**Questions or errors?** Report the full error message from `lake build` and I'll fix it.
