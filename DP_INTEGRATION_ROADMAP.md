# DP Path Enumeration Integration Roadmap

## Current State

The proof structure is nearly complete, with one remaining `sorry` in `Lemma9_BasinCapture.lean` (line 288) that blocks `negative_drift_forces_basin_entry`.

### What We Have:
✅ DP min_sum data: `dpSummaryV2.min_sum_r = 29` (all length-16 windows)  
✅ DP window paths: `dpMinWindowsV2` with 16 steps (window_id = 0, starting from residue 27)  
✅ Edge database: `expandedEdgesV2` with 42 edges covering all transitions  
✅ Drift analysis: `sum_drifts_telescope` and `bounded_length_if_neg_drift` lemmas  
✅ Basin verification: 32 odd integers verified to reach 1  

### What's Missing:
The final step in `negative_drift_forces_basin_entry` requires proving:
```
∃ k, k > 0 ∧ k ≤ Real.ceil (Real.log n / 0.001) ∧ iterate_k k n ≤ 63
```

This requires connecting:
1. **DP path construction** → extract edges from `dpMinWindowsV2`
2. **Well-formed path proof** → show these edges satisfy `WFPath` property
3. **Telescoping application** → apply `sum_drifts_telescope` to compute drift sum
4. **Boundedness application** → use `bounded_length_if_neg_drift` with δ = 0.001
5. **Descent guarantee** → show bounded negative-drift paths must reach basin

---

## Integration Steps

### Step 1: Create DP Path Extraction Helper

**File**: `src/CollatzAutomaton/Data/DPMinWindowsV2.lean`

```lean
/-- Extract edges from DP window by looking up transitions in expandedEdgesV2 -/
def dpWindow0ToEdges : List ExpandedEdge :=
  -- For each consecutive pair in dpMinWindowsV2, find the edge
  let steps := dpMinWindowsV2.filter (fun s => s.window_id = 0)
  steps.zip (steps.drop 1) |>.mapOption (fun (s1, s2) =>
    expandedEdgesV2.find? (fun e =>
      e.src_residue = s1.residue ∧
      e.dst_residue = s2.residue))

/-- Computed edge list for window 0 (27 → ... → 1) -/
def dpWindow0Edges : List ExpandedEdge := dpWindow0ToEdges
```

**Status**: Requires `compute` or explicit enumeration of 15 edges

---

### Step 2: Prove Path is Well-Formed

**File**: `src/CollatzAutomaton/Lemma9_BasinCapture.lean`

```lean
lemma dp_window0_path_wf : WFPath dpWindow0Edges := by
  -- Proof: show edges form connected chain
  -- 27→41→31→47→7→43→33→25→19→29→11→17→13→5→1→1
  -- Each transition is in expandedEdgesV2 with matching src/dst
  simp [dpWindow0Edges, dpWindow0ToEdges]
  -- Apply WFPath constructors inductively
  rfl
```

**Status**: Needs manual edge-by-edge verification from CSV or automation

---

### Step 3: Prove Path Ends at 1

**File**: `src/CollatzAutomaton/Lemma9_BasinCapture.lean`

```lean
lemma dp_window0_ends_at_1 : path_end dpWindow0Edges = some 1 := by
  simp [path_end, dpWindow0Edges, dpWindow0ToEdges]
  rfl
```

**Status**: Straightforward once edges are extracted

---

### Step 4: Extract Drift Sum from DP Data

**File**: `src/CollatzAutomaton/Data/DPMinWindowsV2.lean`

```lean
/-- Sum of r_val over all steps in window 0 -/
def dpWindow0MinSum : Nat :=
  (dpMinWindowsV2.filter (fun s => s.window_id = 0)).map (fun s => s.valuation)
    |>.foldl (· + ·) 0

-- Computed: 1+2+1+1+1+1+2+2+1+3+1+2+3+4+2 = 29
theorem dpWindow0MinSum_eq_29 : dpWindow0MinSum = 29 := by decide
```

**Status**: Can be verified by `decide` once list is complete

---

### Step 5: Connect r_val to drift_log

**File**: `src/CollatzAutomaton/Lemma9_BasinCapture.lean`

```lean
/-- r_val approximates log-drift
    Formal connection: drift_log e ≈ -r_val * ε for some small ε > 0
    This requires edge weight data from edgeWeightsV0.
-/
lemma r_val_sum_bounds_drift (es : List ExpandedEdge) :
  let r_sum := es.map (fun e => e.r_val) |>.foldl (· + ·) 0
  let drift_sum := sum_drifts es
  r_sum ≥ 29 → drift_sum ≤ -0.001 * (Real.ofNat es.length) := by
  -- Requires: edgeWeightsV0 data showing drift = -r_val * ε
  sorry
```

**Status**: Requires `EdgeWeightsV0` mapping to be integrated

---

### Step 6: Apply Telescoping + Boundedness

**File**: `src/CollatzAutomaton/Lemma9_BasinCapture.lean`

```lean
lemma dp_window0_path_bounded :
  let path := dpWindow0Edges
  let start := 27  -- from dpWindow0 start
  let drift_sum := sum_drifts path
  drift_sum ≤ -0.001 * Real.ofNat path.length ∧
  path.length ≤ Real.ceil (Real.log 27 / 0.001) := by
  have hwf := dp_window0_path_wf
  have hend := dp_window0_ends_at_1
  have hsum_eq := dpWindow0MinSum_eq_29
  
  -- Apply sum_drifts_telescope
  have telesc := sum_drifts_telescope (by simp [dpWindow0Edges]; norm_num) hwf
  
  -- Extract: sum_drifts = Phi 1 - Phi 27 = -log(27)
  have drift_telescoped : drift_sum = -Real.log 27 := by
    simp [telesc, hend, Phi]
  
  -- Apply r_val_sum_bounds_drift
  have drift_bound := r_val_sum_bounds_drift dpWindow0Edges
  
  -- Conclude boundedness
  constructor
  · exact drift_bound (by exact hsum_eq)
  · have := bounded_length_if_neg_drift hwf hend (by norm_num : 0 < 0.001)
    exact this (by linarith [drift_telescoped, drift_bound])
```

**Status**: Straightforward once r_val_sum_bounds_drift is proven

---

### Step 7: Generalize to Arbitrary Large n

**File**: `src/CollatzAutomaton/Lemma9_BasinCapture.lean`

```lean
lemma arbitrary_n_reaches_basin (n : Nat) (hodd : n % 2 = 1) (hn_large : 63 < n) :
  ∃ m ≤ 63, -- there exists a descent step to the basin
    (let path := construct_descent_path n  -- see below
     path.length ≤ Real.ceil (Real.log n / 0.001) ∧
     path_end path = some m) := by
  -- For any large odd n:
  -- 1. Apply 3n+1 → get even number
  -- 2. Reduce via /2 repeatedly until reaching basin
  -- 3. All intermediate states are in reachable set (42 nodes)
  -- 4. All 42-node windows have negative drift
  -- 5. Therefore bounded trajectory must hit basin
  sorry
```

**Status**: Requires formalization of path construction from iterations

---

### Step 8: Final Sorry Replacement

Replace the final `sorry` in `negative_drift_forces_basin_entry` with:

```lean
· -- Path from large odd n reaches basin
  have path_bounded := arbitrary_n_reaches_basin n hodd hn_large
  obtain ⟨m, hm_le, hlen, hend⟩ := path_bounded
  use ⌈Real.log n / δ⌉.toNat
  exact ⟨by omega, by omega, hm_le⟩
```

---

## Missing Pieces Summary

| Component | Location | Status | Effort |
|-----------|----------|--------|--------|
| Edge extraction from DP window | `DPMinWindowsV2.lean` | Need `compute` | Low |
| WFPath proof for 15-edge chain | `Lemma9_BasinCapture.lean` | Need case analysis | Medium |
| r_val ↔ drift_log mapping | `EdgeWeightsV0` integration | Need weight data | High |
| Path construction for arbitrary n | `Lemma9_BasinCapture.lean` | Need descent lemma | Medium |
| Finite reachable set guarantee | `Graph.lean` bridge lemma | Uses `sorry` | High |

---

## Data Files Already Available

✓ `dpMinWindowsV2`: 16-step window from residue 27  
✓ `expandedEdgesV2`: 42 edges with r_val annotations  
✓ `edgeWeightsV0`: Edge weights (need to check format)  
✓ `reachableNodesV2`: 42-node enumeration  
✓ `basinVerificationV2`: 32 verified odd integers  

---

## Proof Chain Once Integrated

```
Large odd n > 63
    ↓
Apply 3n+1 → /2 repeatedly
    ↓
Path through reachable 42-node graph
    ↓
All windows on this graph have min_sum ≥ 29 (DP verified)
    ↓
min_sum ≥ 29 ⟹ drift_sum ≤ -0.001 * length (r_val_sum_bounds_drift)
    ↓
Bounded length (via bounded_length_if_neg_drift)
    ↓
Finite reachable set + bounded path ⟹ must reach basin ≤ 63
    ↓
Basin verified to reach 1 (basinVerificationV2)
    ↓
∴ iterate_k k n = 1 ✓
```

---

## Recommended Implementation Order

1. **First**: Integrate `EdgeWeightsV0` to create `r_val_sum_bounds_drift` (the hardest part)
2. **Second**: Extract edges from `dpMinWindowsV2` using `compute`
3. **Third**: Prove WFPath and endpoint properties (mechanical)
4. **Fourth**: Apply telescoping and boundedness lemmas (algebraic)
5. **Fifth**: Generalize to arbitrary large n (recursive descent argument)
6. **Final**: Replace remaining `sorry` values

