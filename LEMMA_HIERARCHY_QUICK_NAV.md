# Quick Navigation: Lemma Hierarchy Documentation

⚠️ **IMPORTANT:** Read [PROOF_AUDIT_CRITICAL_GAPS.md](PROOF_AUDIT_CRITICAL_GAPS.md) first for current critical issues.

**Status:** ⚠️ ARCHITECTURE SOLID, CRITICAL GAPS IDENTIFIED  
**Build:** ✅ PASSING  
**Date:** January 2, 2026

---

## What Was Created

A complete **hierarchical proof specification** organizing all lemmas in a structured, numbered format:

- **Lemmas 0.1–0.4:** Infrastructure (iterate_k, even reduction, odd step, 2-adic valuation)
- **Lemmas 1.1–1.3:** Odd-block semantics (definition, oddness preservation, affine formula)
- **Lemmas 2.1–2.3:** Automaton encoding (state mapping, edge semantics, path lifting)
- **Lemmas 3.1–3.3:** DP certificate layer (weight definitions, global bound, reachability)
- **Lemmas 4.1–4.2:** Universality (uniform window bounds, 64-window composition)
- **Lemmas 5.1–5.3:** Contraction and descent (affine contraction, strictness, strict descent)
- **Lemmas 6.1–6.3:** Basin and convergence (basin verification, basin capture, main theorem)

**Location:** [PROOF_SPECIFICATION_LEMMA_HIERARCHY.md](PROOF_SPECIFICATION_LEMMA_HIERARCHY.md)

---

## How to Use This Document

### For Understanding the Proof Structure
1. Open [PROOF_SPECIFICATION_LEMMA_HIERARCHY.md](PROOF_SPECIFICATION_LEMMA_HIERARCHY.md)
2. Read the **Overview** section (top of document)
3. Scan the **Proof Dependency Graph** (shows which lemmas depend on which)
4. Check your lemma of interest in PART A–G

### For Implementing a Specific Lemma
1. Find your lemma (e.g., Lemma 5.1)
2. Note its Status (✅ Complete / ⚠️ Needs Work / ❌ Not Started)
3. Read the Statement (exact Lean code)
4. Read the Purpose (what it accomplishes)
5. Check Location (where it should go in codebase)
6. See Current Evidence (what exists already)

### For Understanding Dependencies
1. Go to **Proof Dependency Graph** near end of document
2. Find your goal (e.g., collatz_converges)
3. Trace upward to see what must be proven first
4. See which lemmas are bottlenecks

### For Implementation Priority
1. See **Implementation Status Summary** section
2. Completed lemmas (✅): documented, ready to use
3. Partial (⚠️): may need verification or formalization
4. Not started (❌): need full implementation

---

## Key Reference Points

### Most Important Lemmas

| Lemma | Purpose | Status | Impact |
|-------|---------|--------|--------|
| 2.3 (Path Lifting) | Arithmetic ↔ Graph bridge | ✅ | **CRITICAL** |
| 3.2 (DP Coverage) | DP bound applies universally | ✅ | **CRITICAL** |
| 1.3 (Affine Formula) | Valuation sum ↔ descent | ⚠️ | High (blocks 5.1) |
| 5.1 (Contraction) | Numeric descent proof | ⚠️ | High (blocks 5.3) |

### Quick Status Check

```
Critical Path to Convergence
─────────────────────────────

Lemma 6.3 (Main Theorem)
  ↓ depends on
Lemma 5.3 (Strict Descent) ⚠️ — Needs implementation
  ↓ depends on
Lemma 5.1 (Contraction) ⚠️ — Needs affine formula
  ↓ depends on
Lemma 1.3 (Affine Formula) ⚠️ — Needs formalization
  ↓ depends on
Lemma 1.1 (OddBlock) ✅ — Complete

Bottleneck: Lemma 1.3 (Affine Formula)
Estimated time to clear: 2–3 hours
```

---

## Document Locations

### Proof Specification
- **Main:** [PROOF_SPECIFICATION_LEMMA_HIERARCHY.md](PROOF_SPECIFICATION_LEMMA_HIERARCHY.md) ← Start here
  - 600+ lines, comprehensive lemma-by-lemma specification
  - Includes statements, purposes, implementation guidance

### Bridge Lemma 3 (Recently Completed)
- **Summary:** [BRIDGE_LEMMA_3_COMPLETE_SUMMARY.md](BRIDGE_LEMMA_3_COMPLETE_SUMMARY.md)
- **Details:** [BRIDGE_LEMMA_3_IMPLEMENTATION.md](BRIDGE_LEMMA_3_IMPLEMENTATION.md)
- **Index:** [BRIDGE_LEMMA_3_INDEX.md](BRIDGE_LEMMA_3_INDEX.md)

### 🚨 CRITICAL AUDIT DOCUMENTS (READ FIRST)
- **[PROOF_AUDIT_CRITICAL_GAPS.md](PROOF_AUDIT_CRITICAL_GAPS.md)** ← **START HERE**
  - Identifies 5 critical checkpoints (A–E) that must be fixed
  - Documents fatal issue: `window_of_path` uses `residue % 10` instead of true valuations
  - Maps all critical gaps to lemmas
  - Provides 8-point action plan with time estimates
  - **Total work to completion:** 8–12 hours

- **[STRATEGY_TO_LEMMAS_MAPPING.md](STRATEGY_TO_LEMMAS_MAPPING.md)**
  - Cross-references user's 10-step strategy with Lemmas 0.1–6.3
  - Shows where each proof step should be formalized
  - Identifies which lemmas have unfinished work
  - Explains dependency chain and bottlenecks

### Remaining Work
- **[REMAINING_WORK_POST_BRIDGE_LEMMA_3.md](REMAINING_WORK_POST_BRIDGE_LEMMA_3.md)** — Detailed sketches for Lemmas 1.3, 5.1, 5.3, 6.3

- **Checklist:** [BRIDGE_LEMMA_3_CHECKLIST.md](BRIDGE_LEMMA_3_CHECKLIST.md)

### Remaining Work
- **Plan:** [REMAINING_WORK_POST_BRIDGE_LEMMA_3.md](REMAINING_WORK_POST_BRIDGE_LEMMA_3.md)
- **Action Steps:** [ACTION_COMPLETE_PROOF_NOW.md](ACTION_COMPLETE_PROOF_NOW.md)

---

## Reading Paths

### Path 1: Quick Overview (15 minutes)
1. Read this file (5 min)
2. Skim [PROOF_SPECIFICATION_LEMMA_HIERARCHY.md](PROOF_SPECIFICATION_LEMMA_HIERARCHY.md) Overview (5 min)
3. Check Proof Dependency Graph (5 min)

### Path 2: Understanding the Structure (1 hour)
1. Read this file (5 min)
2. Read [PROOF_SPECIFICATION_LEMMA_HIERARCHY.md](PROOF_SPECIFICATION_LEMMA_HIERARCHY.md) completely (45 min)
3. Review Dependency Graph and Status Summary (10 min)

### Path 3: Ready to Implement (2 hours)
1. Follow Path 2 above (1 hour)
2. Read [REMAINING_WORK_POST_BRIDGE_LEMMA_3.md](REMAINING_WORK_POST_BRIDGE_LEMMA_3.md) (30 min)
3. Open code files mentioned in PROOF_SPECIFICATION (30 min)

---

## How to Find a Specific Lemma

### By Number (e.g., "Where is Lemma 3.2?")
Search [PROOF_SPECIFICATION_LEMMA_HIERARCHY.md](PROOF_SPECIFICATION_LEMMA_HIERARCHY.md) for "Lemma 3.2" or "## Lemma 3.2"

Result: Shows status, statement, location, evidence

### By Name (e.g., "Where is DP Coverage?")
Search [PROOF_SPECIFICATION_LEMMA_HIERARCHY.md](PROOF_SPECIFICATION_LEMMA_HIERARCHY.md) for "DP Coverage" or "dp_coverage"

Result: Shows lemma number, status, full code

### By File (e.g., "What lemmas are in MainTheorem.lean?")
Scan the "Location:" field in PROOF_SPECIFICATION for each lemma

Or use grep:
```powershell
# Find all lemma statements in PROOF_SPECIFICATION
Select-String "Location:.*MainTheorem" PROOF_SPECIFICATION_LEMMA_HIERARCHY.md
```

---

## Implement Next

### Option 1: Continue from Bridge Lemma 3 (Recommended)
Current status: Lemmas 1–3 complete (4/8 done)

Next steps:
1. Fill trivial sorry in dp_coverage (1 min)
2. Implement Lemma 1.3 (Affine Formula) (2–3 hours)
3. Implement Lemma 5.1 (Contraction) (1–2 hours)
4. Implement Lemma 5.3 (Strict Descent) (1 hour)
5. Assemble Lemma 6.3 (Main Theorem) (30 min)

**Total:** 4–6 hours to completion

**See:** [ACTION_COMPLETE_PROOF_NOW.md](ACTION_COMPLETE_PROOF_NOW.md)

### Option 2: Verify Dependencies First
1. Open [PROOF_SPECIFICATION_LEMMA_HIERARCHY.md](PROOF_SPECIFICATION_LEMMA_HIERARCHY.md)
2. Check Proof Dependency Graph
3. Identify which lemma to implement first
4. Open [PROOF_SPECIFICATION_LEMMA_HIERARCHY.md](PROOF_SPECIFICATION_LEMMA_HIERARCHY.md) to that lemma
5. Use Statement + Purpose + Current Evidence to guide implementation

---

## Key Insights

### What the Numbering Means

```
Lemma X.Y

X = "part" (0–6)
    0 = Infrastructure
    1 = Odd-block semantics
    2 = Automaton encoding
    3 = DP layer
    4 = Universality
    5 = Descent
    6 = Basin + main

Y = lemma within that part
    .1 = first lemma in part
    .2 = second lemma in part
    .3 = third lemma in part
```

### Proof Architecture

```
All numbers reduce to finite graph (via state encoding)
         ↓
Every trajectory lifts to a graph path (path lifting)
         ↓
Every graph path is constrained by DP (DP certificate)
         ↓
Therefore all trajectories have bounded valuation sum (universality)
         ↓
Valuation sum bound implies numeric descent (affine formula)
         ↓
Descent + basin = convergence (strong induction)
```

---

## File Organization

```
c:\collatz_automaton\
├─ PROOF_SPECIFICATION_LEMMA_HIERARCHY.md      ← Main reference (START HERE)
├─ BRIDGE_LEMMA_3_COMPLETE_SUMMARY.md          ← What was just completed
├─ BRIDGE_LEMMA_3_IMPLEMENTATION.md            ← Detailed technical explanation
├─ REMAINING_WORK_POST_BRIDGE_LEMMA_3.md       ← What's left
├─ ACTION_COMPLETE_PROOF_NOW.md                ← Step-by-step execution
│
├─ src/CollatzAutomaton/
│  ├─ Core.lean                    (Lemmas 0.1–0.4)
│  ├─ MainTheorem.lean             (Lemmas 1.1–1.2, 6.3)
│  ├─ Graph.lean                   (Lemmas 2.1–2.2)
│  ├─ Lemma8_DensityFloor.lean      (Lemmas 2.3, 3.1–3.3) ← Updated
│  └─ Data/
│     ├─ BasinVerificationV2.lean   (Lemma 6.1)
│     └─ DPMinWindowsV2.lean        (DP data for Lemma 3.2)
```

---

## Success Criteria

After completing all lemmas, you'll have:

- ✅ **Lemma 0.x:** Infrastructure working (iteration, valuation)
- ✅ **Lemma 1.x:** Odd-block semantics (definition through affine formula)
- ✅ **Lemma 2.x:** State encoding and path lifting (arithmetic ↔ graph)
- ✅ **Lemma 3.x:** DP certificate applied (bounds all reachable paths)
- ✅ **Lemma 4.x:** Universality proven (bounds apply to all integers)
- ✅ **Lemma 5.x:** Contraction and descent (numeric decrease)
- ✅ **Lemma 6.x:** Convergence proven (basin + descent = 1)

**Then:** Run `lake build` → 0 errors → Proof complete! 🎉

---

## Questions?

### "Where do I start?"
→ Open [PROOF_SPECIFICATION_LEMMA_HIERARCHY.md](PROOF_SPECIFICATION_LEMMA_HIERARCHY.md) and find your lemma

### "What do I implement next?"
→ Follow the Proof Dependency Graph; Lemma 1.3 is the bottleneck

### "How long will it take?"
→ 4–6 hours for all remaining lemmas (Lemma 1.3 is the longest)

### "Is Lemma X already done?"
→ Check Implementation Status Summary section in PROOF_SPECIFICATION

### "Where can I see the Lean code?"
→ Check "Location:" field for your lemma; open that file in VS Code

---

## Final Notes

This hierarchical organization:
- ✅ Makes proof structure crystal clear
- ✅ Identifies exactly what's done vs. pending
- ✅ Provides reference statements for each lemma
- ✅ Shows implementation guidance for each
- ✅ Makes handoff to other developers trivial
- ✅ Enables parallel work on independent lemmas

**Status:** Bridge Lemma 3 ✅ Complete → Proof structure ✅ Documented → Ready for Lemmas 4–7

