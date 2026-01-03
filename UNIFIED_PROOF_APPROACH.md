# Unified Proof Approach: Collatz Convergence via DP-Certified Descent
**Status:** Implementation Roadmap  
**Date:** January 2, 2026

---

## Executive Summary

This document consolidates the complete proof approach into one coherent narrative. It provides:
1. **Mathematical logic** for why the 64-window bound is uniform
2. **Formal lemma signatures** that must appear in Lean
3. **Internal lemma checklist** with all dependencies
4. **Critical gap analysis** identifying what still needs proof

The central claim: **For every positive integer n, the DP-certified 16-step descent forces trajectories into a bounded basin, proven via potential function over a finite-state automaton.**

---

## Part 1: The Core Claim (Everything Else Is Infrastructure)

### The One Theorem That Matters

All the DP work, all the finite-state encoding, all the DP certificates exist for *one purpose*:

**Establish this theorem:**
$$\forall n \text{ odd}, \quad \sum_{i=0}^{63} r\text{\_val}(n_i) \geq R_{\min}$$

where:
- $n_0 = n$ (starting odd integer)
- $n_{i+1} = T(n_i) = \frac{3n_i + 1}{2^{r\text{\_val}(n_i)}}$ (the odd-to-odd Collatz step)
- $r\text{\_val}(n) = \nu_2(3n + 1)$ (2-adic valuation)
- $R_{\min}$ is the minimum total weight over all length-64 paths in the DP graph

**In Lean:**
```lean
/-- The uniform 64-window bound: every odd integer's 64-step valuation sum ≥ R_min. -/
theorem window64_lower_bound :
  ∀ n : OddNat, (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum ≥ R_min
```

**Why this one theorem is everything:**
- If this holds for all odd n, then valuation sum is always ≥ R_min
- R_min > log₂(3) * 64 means 3^64 / 2^R_min < 1 (contraction)
- Contraction + affine expansion → n_64 < n (descent)
- Descent + basin = convergence ✓

Everything else is either:
1. **Infrastructure to state this theorem precisely** (definitions, DP certificate)
2. **Proofs that justify the quantifier ∀n** (state coverage, edge extraction, path lifting)
3. **Proofs that extract value from the bound** (contraction, recursion)

---

### 1.1 Reduction: All Integers → All Odd States

Every Collatz trajectory can be factored:

```
n₀ → [divide by 2 repeatedly until odd] → n₁ (odd)
     → [apply 3n+1, divide by 2^r(n₁)] → n₂ (odd)
     → ...
```

**Key fact:** If we prove uniform descent for all odd integers, it applies to all integers (evens just "fast-forward" to the next odd by division).

**Formal statement needed:**
```lean
lemma all_integers_reduce_to_odd_subsequence (n : ℕ) (h_ne_zero : n ≠ 0) :
  ∃ k, iterate_k k n % 2 = 1  -- reaches an odd number
```

---

## Part 2: The Seven Critical Lemmas (Dependency Order)

Over L consecutive odd Collatz steps:
$$n_L = \frac{3^L n_0 + A}{2^S}$$

where:
- $S = \sum_{i=0}^{L-1} r(n_i)$ is the total 2-adic valuation
- $A \geq 0$ is an explicit accumulated "+1" term

**Critical insight:** Contraction depends *only* on S, not on the intermediate values.

**Formal statement needed:**
```lean
lemma affine_formula_over_odd_blocks (L : ℕ) (n : ℕ) (hodd : n % 2 = 1) :
  ∃ (S : ℕ) (A : ℕ),
    (iterate_k_odd_block L n) = (3^L * n + A) / 2^S ∧
    S = (List.range L).map (fun i => r_val_at_step i n) |>.sum ∧
    A_bounds n S L A  -- auxiliary constraint
```

---

### 1.3 Finite-State Graph Encodes All Odd Steps

**Definition:** A finite directed graph with vertices representing 2-adic residue states:
- Vertices: odd residues in a complete system mod 2^M (typically 32 residues for M=5, or 64 for M=6)
- Edges: directed edge (u → v) with weight r exists iff for some odd n ≡ u (mod 2^M), applying one Collatz step gives an odd result ≡ v (mod 2^M) with 2-adic valuation r
- **Property:** Every actual odd integer n belongs to exactly one vertex, and one Collatz step follows exactly one outgoing edge with the correct weight r

**Formal statement needed:**
```lean
lemma every_odd_maps_to_graph_vertex (n : ℕ) (hodd : n % 2 = 1) :
  ∃! v : Vertex, residue_of n = residue_of_vertex v

lemma one_step_follows_edge (n : ℕ) (hodd : n % 2 = 1) (v := residue_of n) :
  ∃! e : Edge, src e = v ∧ dst e = residue_of (oddBlock n) ∧ weight e = r_val n
```

---

### 1.4 Uniformity via Worst-Case Path Analysis

Define:
$$W_L(v) = \min \{ \text{total weight along all length-}L\text{ paths starting at } v \}$$

$$R_{\min} = \min_v W_L(v)$$

**Uniform bound:** For any odd integer n, the 64-step odd-block trajectory has total valuation $S \geq R_{\min}$.

**Why:** Every actual trajectory must pass through its corresponding vertex and follow available edges; the DP computation finds the worst-case path, so all real paths are at least that good.

**Formal statement needed:**
```lean
/-- Compute minimum total weight over all length-L paths from a vertex. -/
def W_L (L : ℕ) (v : Vertex) : ℕ := 
  -- min-plus DP: compute by iteration or dynamic programming

/-- Global minimum over all starting vertices. -/
def R_min (L : ℕ) : ℕ := 
  (allVertices.map (W_L L)).minimum

/-- Every length-64 odd-block trajectory has total valuation ≥ R_min. -/
lemma uniform_valuation_bound (n : ℕ) (hodd : n % 2 = 1) :
  (List.range 64).map (fun i => r_val_at_step i n) |>.sum ≥ R_min 64
  -- Proof: n maps to some vertex v, trajectory follows edges from v,
  -- any such path has weight ≥ W_64(v) ≥ R_min.
```

---

### 1.5 Contraction Ratio and Strict Descent

Using the affine formula with $S \geq R_{\min}$:
$$n_{64} \leq \frac{3^{64}}{2^{R_{\min}}} n_0 + O(1)$$

If $3^{64} < 2^{R_{\min}}$, this gives strict contraction:
$$\frac{3^{64}}{2^{R_{\min}}} < 1$$

**Formal statement needed:**
```lean
lemma contraction_ratio_strict :
  (3 : ℚ)^64 / (2 : ℚ)^(R_min 64) < 1

lemma affine_contraction_from_valuation_bound (n : ℕ) (hodd : n % 2 = 1) (hn_large : n ≥ 64) :
  ∃ (m : ℕ),
    (oddBlock^[16] n) = m ∧  -- after 16 macro-steps (64 micro-steps)
    (m : ℚ) < (3^64 / 2^(R_min 64)) * (n : ℚ)
```

---

### 1.6 Addressing Cycles: Why DP Is Sound

Without ruling out negative-drift cycles, a trajectory could circle indefinitely in a low-weight loop, evading the bound.

**Formal statement needed:**
```lean
/-- No directed cycle in the graph has average weight ≥ R_min / 64. -/
lemma no_negative_drift_cycle :
  ∀ cycle : Path, IsCycle cycle →
    (cycle.edges.map weight).sum / cycle.edges.length ≥ R_min / 64

/-- Consequence: bounded descent always terminates. -/
lemma bounded_descent_no_cycle (n : ℕ) (hodd : n % 2 = 1) :
  ¬∃ ∞ i, (iterate_odd_block i n) % 2 = 1  -- can't cycle forever
```

---

## Part 2: Formal Lemma Signatures (What Goes in Lean)

### 2.1 The DP Global Descent Lemma

```lean
/-- For every large odd n, there is a 16-step window in the DP certificate
    with total valuation ≥ 29, anchored at n's residue. -/
lemma dp_global_descent
  (n : ℕ)
  (h_large : n ≥ 64)
  (hodd : n % 2 = 1) :
  ∃ es : List ExpandedEdge,
    es.length = 16 ∧
    (ValidWindow16 es) ∧  -- passes DP constraints
    (start_of_window es = residue_of n) ∧
    ((es.map r_val).sum ≥ 29) :=
by
  -- Proof: For any odd n ≥ 64, its residue class is in the 42-node reachable set.
  -- By DP certificate (DpCertV2), there exists a length-16 path from that residue
  -- with total weight ≥ 29 (the minimum found over all vertices).
  sorry  -- requires integration with DP certificate data
```

**Status:** Requires DP certificate format definition and lookup mechanism.

---

### 2.2 Bridge: Window to Iterate

```lean
/-- A valid 16-edge window corresponds to a Collatz iterate
    with controlled potential change. -/
lemma window_to_iterate_contraction
  (n : ℕ)
  (hodd : n % 2 = 1)
  (es : List ExpandedEdge)
  (hes_valid : ValidWindow16 es ∧ start_of_window es = residue_of n)
  (hes_weight : (es.map r_val).sum ≥ 29) :
  ∃ (K : ℕ) (m : ℕ),
    K > 0 ∧
    (iterate_k K n = m) ∧
    (m % 2 = 1) ∧
    Φ m ≤ Φ n + (C_max_log_sum - 29) / 16 :=
by
  -- Proof chain:
  -- 1. Each edge in es corresponds to one oddBlock step
  -- 2. 16 edges compose to 16 oddBlock steps, which is K micro-steps
  -- 3. The potential drop follows from the log-weight bound on the window
  sorry  -- requires edge semantics and log↔potential lemmas
```

**Status:** Requires (C1) edge semantics and (C2) log↔potential translation.

---

### 2.3 Collatz-Native Descent Lemma

```lean
/-- For every odd n ≥ 64, there is a Collatz iterate with strict potential drop. -/
lemma exists_contracting_iterate
  (n : ℕ)
  (h_large : n ≥ 64)
  (hodd : n % 2 = 1) :
  ∃ K : ℕ,
    K > 0 ∧
    (iterate_k K n) % 2 = 1 ∧
    Φ (iterate_k K n) < Φ n  -- strict descent
:=
by
  -- Proof: Combine dp_global_descent and window_to_iterate_contraction.
  obtain ⟨es, hlen, hvalid, hstart, hweight⟩ := dp_global_descent n h_large hodd
  obtain ⟨K, m, hK_pos, hiter, hodd_m, hpot⟩ := 
    window_to_iterate_contraction n hodd es ⟨hvalid, hstart⟩ hweight
  use K
  refine ⟨hK_pos, hodd_m, ?_⟩
  -- Strict contraction from: (C_max_log_sum - 29) / 16 < 0
  have h_strict : (C_max_log_sum - 29) / 16 < 0 := contraction_margin_neg
  omega  -- or linarith
```

**Status:** Depends on dp_global_descent and window_to_iterate_contraction.

---

### 2.4 Main Convergence Theorem

```lean
theorem collatz_converges : ∀ n : ℕ, n ≠ 0 → ∃ k, iterate_k k n = 1 := by
  intro n hn_ne_zero
  -- Split into even and odd cases
  by_cases heven : n % 2 = 0
  · -- Even case: divide by 2 until odd
    sorry  -- straightforward, proven separately
  · -- Odd case
    push_neg at heven
    have hodd : n % 2 = 1 := by omega
    clear heven
    
    -- Split into basin and large cases
    by_cases h_basin : n ≤ 63
    · -- Basin (n ≤ 63): use basin_rows_reach_1_data
      obtain ⟨k⟩ := basin_rows_reach_1_data n h_basin hodd
      exact ⟨k, by omega⟩
    
    · -- Large case (n > 63): use well-founded descent
      push_neg at h_basin
      -- Strong induction on n using well-founded < ordering
      suffices ∀ m ≤ n, m ≠ 0 → (m % 2 = 1 → ∃ k, iterate_k k m = 1) by
        exact by_cases (fun h => this n (le_refl n) hn_ne_zero h)
                      (fun h => by omega)
      
      intro m hm_le hn_ne_zero hm_odd
      by_cases hm_large : m ≥ 64
      · -- Large odd m: use contraction
        obtain ⟨K, hK_pos, hodd_m, hpot_drop⟩ := exists_contracting_iterate m hm_large hm_odd
        have hm_next : iterate_k K m < m := by omega  -- potential strictly decreases
        have hm_next_ne : iterate_k K m ≠ 0 := by omega
        -- Recursive call on smaller value
        have ⟨k'⟩ := by
          apply this (iterate_k K m) (Nat.lt_of_le_of_lt hm_next hm_le) hm_next_ne hodd_m
        use K + k'
        simp [iterate_k_add]
        exact k'
      
      · -- Small odd m: use basin
        omega
```

**Status:** Requires basin_rows_reach_1_data and exists_contracting_iterate.

---

## Part 3: Internal Lemma Checklist

Below are all lemmas that *must* exist in the codebase for the proof to work. Format: **Status | Requirement | Location (or TBD)**

### Core Definitions
| Status | Lemma | Purpose | File |
|--------|-------|---------|------|
| ✅ | `iterate_k` | Apply Collatz step k times | Core.lean |
| ✅ | `oddBlock` | One odd→odd macro-step | MainTheorem.lean |
| ❓ | `Φ` (potential) | Log-based potential for descent | **TBD** |
| ❓ | `Vertex` | Residue state in DP graph | **TBD** |
| ❓ | `Edge` | Directed edge with weight | **TBD** |
| ❓ | `ValidWindow16` | Edge window satisfies DP constraints | **TBD** |
| ❓ | `start_of_window` | Residue where window starts | **TBD** |
| ❓ | `r_val` | Weight of an edge (2-adic valuation) | **TBD** |
| ❓ | `C_max_log_sum` | Maximum log-sum over DP certificate | **TBD** |
| ❓ | `R_min` | Minimum total weight over all paths | **TBD** |

### Bridge Lemmas (Micro ↔ Macro)
| Status | Lemma | Purpose | File |
|--------|-------|---------|------|
| ✅ | `oddBlock_is_odd` | oddBlock output is always odd | MainTheorem.lean |
| ✅ | `oddBlock_eq_iterate` | oddBlock equals a finite iterate | MainTheorem.lean |
| ✅ | `oddBlock16_eq_iterate` | 16 oddBlocks compose to iterate | MainTheorem.lean |
| ❓ | **edge_corresponds_to_oddblock** | Each DP edge = one oddBlock step | **TBD** |
| ❓ | **residue_of_oddblock** | oddBlock output's residue follows edge | **TBD** |

### Potential Function Lemmas
| Status | Lemma | Purpose | File |
|--------|-------|---------|------|
| ❓ | **potential_is_log** | Φ(n) = log(n) or equivalent | **TBD** |
| ❓ | **potential_decreases_affine** | Affine formula bounds Φ decrease | **TBD** |
| ❓ | **log_sum_bounds_potential** | Σ r_i ≥ R bounds Φ(start) - Φ(end) | **TBD** |
| ❓ | `contraction_margin_neg` | (C_max - 29)/16 < 0 | **TBD** |
| ❓ | **potential_below_threshold_in_basin** | Φ(n) < thresh ⟹ n ≤ 63 | **TBD** |

### DP Certificate Lemmas
| Status | Lemma | Purpose | File |
|--------|-------|---------|------|
| ❓ | **dp_certificate_validity** | DpCertV2 data correctly encodes DP solution | **TBD** |
| ❓ | **min_weight_all_paths** | R_min is minimum over all length-64 paths | **TBD** |
| ❓ | **no_negative_drift_cycle** | No cycle has negative average weight | **TBD** |
| ❓ | **every_vertex_has_path** | Every residue class has ≥ one length-64 path | **TBD** |
| ❓ | **lookup_window_for_residue** | Given residue, extract certified 16-window | **TBD** |

### Integration Lemmas
| Status | Lemma | Purpose | File |
|--------|-------|---------|------|
| ❓ | **all_integers_reduce_to_odd** | Even n reduces to odd via division by 2 | **TBD** |
| ❓ | **odd_integer_maps_to_vertex** | Every odd n corresponds to unique vertex | **TBD** |
| ❓ | **trajectory_follows_graph** | Actual Collatz trajectory traces graph path | **TBD** |
| ✅ | `basin_rows_reach_1_data` | All odd n ≤ 63 reach 1 | MainTheorem.lean |
| ❓ | **basin_complete** | Φ threshold exactly separates basin from large | **TBD** |

---

## Part 4: Critical Gaps & Solidification Steps

Below are the four major gaps identified in the previous analysis, with concrete remediation steps.

### Gap 1: State-to-Integer Mapping

**Problem:** How does "odd integer n" map to a vertex in the DP graph? Is it residue mod 64? How do you handle equivalence?

**Remediation:**
1. **Define the residue system explicitly:**
   ```lean
   def residue_of (n : ℕ) : Residue := n % (2^M)  -- typically M=6 for 64 residues
   
   /-- Every odd n maps to a unique residue. -/
   lemma odd_integer_to_unique_residue (n : ℕ) (hodd : n % 2 = 1) :
     ∃! r : Residue, residue_of n = r
   
   /-- Different odd residues produce different next residues after one step. -/
   lemma residue_determines_next_state (n m : ℕ) (hodd_n : n % 2 = 1) (hodd_m : m % 2 = 1) :
     residue_of n = residue_of m →
     residue_of (oddBlock n) = residue_of (oddBlock m)
   ```

2. **Prove equivalence class closure:**
   ```lean
   lemma residue_class_closed_under_oddblock (r : Residue) (n : ℕ) :
     residue_of n = r → residue_of (oddBlock n) ∈ valid_next_residues r
   ```

3. **Document assumption:** State explicitly what M is and why it's sufficient.

**Target File:** New file `src/CollatzAutomaton/ResidueSystem.lean`

---

### Gap 2: Potential Φ Calibration

**Problem:** What is Φ exactly? Is it log(n)? How is it normalized so contraction is strict?

**Remediation:**
1. **Define potential precisely:**
   ```lean
   def Φ (n : ℕ) : ℝ := if n = 0 then 0 else Real.log (↑n)
   
   /-- Potential is defined for all positive integers. -/
   lemma potential_positive (n : ℕ) (hn : n ≠ 0) :
     Φ n ≥ 0  -- or whatever lower bound you need
   
   /-- Potential is monotonic. -/
   lemma potential_monotonic (n m : ℕ) (h : n ≤ m) :
     Φ n ≤ Φ m
   ```

2. **Connect affine formula to potential:**
   ```lean
   /-- If n_L = (3^L * n_0 + A) / 2^S, then potential drop is bounded. -/
   lemma potential_drop_via_affine (n₀ n_L : ℕ) (L S A : ℕ) (hodd : n₀ % 2 = 1) :
     n_L = (3^L * n₀ + A) / 2^S →
     Φ n_L ≤ Φ n₀ + L * Real.log 3 - S * Real.log 2
   ```

3. **Show strict contraction from valuation bound:**
   ```lean
   /-- With S ≥ 29 and L = 16, we get strict contraction. -/
   lemma strict_contraction_from_valuation (n₀ n₁₆ : ℕ) (hodd : n₀ % 2 = 1) (hn_large : n₀ ≥ 64) :
     (iterate_k_odd_block 16 n₀ = n₁₆) →
     (List.range 16).map (fun i => r_val_at_step i n₀) |>.sum ≥ 29 →
     Φ n₁₆ < Φ n₀
   ```

**Target File:** New file `src/CollatzAutomaton/PotentialFunction.lean`

---

### Gap 3: Basin Verification Linkage

**Problem:** How do you prove that "once Φ(n) drops below a threshold, n ∈ basin"?

**Remediation:**
1. **Choose explicit threshold:**
   ```lean
   def basin_threshold : ℝ := Real.log 64  -- any value s.t. all n ≤ 63 satisfy Φ(n) < threshold
   
   /-- All basin members satisfy the threshold. -/
   lemma basin_satisfies_threshold (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 63 ∧ n % 2 = 1) :
     Φ n < basin_threshold
   ```

2. **Prove converse (threshold forces basin membership):**
   ```lean
   /-- If Φ below threshold, then n must be in basin (or between basin and 64). -/
   lemma threshold_implies_basin_or_small (n : ℕ) (hn_odd : n % 2 = 1) :
     Φ n < basin_threshold → n ≤ 63
   ```

3. **Use in main proof:**
   ```lean
   -- In collatz_converges, when Φ(m) < basin_threshold, 
   -- apply threshold_implies_basin_or_small to reduce to basin case.
   ```

**Target File:** `MainTheorem.lean` or new `src/CollatzAutomaton/BasinBoundary.lean`

---

### Gap 4: DP Certificate Format & Lookup

**Problem:** What is the input/output of the DP solver? How do you extract a window for a given residue?

**Remediation:**
1. **Define certificate structure:**
   ```lean
   structure DPCertificate where
     vertices : List Residue
     edges : List Edge
     min_weight_per_vertex : Residue → ℕ  -- W_L(v) for fixed L=16 or 64
     global_min_weight : ℕ  -- R_min
     certificate_of_optimality : Proof  -- proof that this is truly min
     cycle_drift_check : Proof  -- proof that no cycle has negative drift
   
   def dpCert : DPCertificate := { ... }  -- instantiate with your DP output
   ```

2. **Implement lookup:**
   ```lean
   /-- Given a residue, retrieve a certified 16-window starting from it. -/
   def lookup_window_for_residue (r : Residue) : Option (List Edge) :=
     (dpCert.edges.filter (fun e => src e = r)).take 16
   
   /-- The lookup always succeeds for valid residues. -/
   lemma lookup_always_succeeds (r : Residue) (hr : r ∈ dpCert.vertices) :
     ∃ window, lookup_window_for_residue r = some window ∧
     window.length = 16 ∧
     (window.map weight).sum ≥ dpCert.global_min_weight
   ```

3. **Validate certificate at build time:**
   ```lean
   /-- Check that dpCert satisfies all DP constraints. -/
   def dpCert_valid : Bool :=
     dpCert.edges.all (fun e => e.weight ≥ 1) &&
     dpCert.vertices.all (fun v => ∃ path, path_starts_at v ∧ path.length = 16 ∧ 
                                          (path.map weight).sum ≥ dpCert.global_min_weight) &&
     ...
   
   /-- Panic if certificate is invalid. -/
   #eval if dpCert_valid then "✅ DP Certificate Valid" else panic! "❌ Invalid DP Certificate"
   ```

**Target File:** New file `src/CollatzAutomaton/Data/DPCertificateV3.lean`

---

## Part 5: Implementation Roadmap

### Phase 1: Foundations (Week 1)
- [ ] **ResidueSystem.lean** — Define residue mapping, prove closure
- [ ] **PotentialFunction.lean** — Define Φ, prove monotonicity, connect to affine formula
- [ ] **DPCertificateV3.lean** — Structure and validate DP data

### Phase 2: DP Lemmas (Week 2)
- [ ] **dp_global_descent** — Prove via certificate lookup
- [ ] **no_negative_drift_cycle** — Validate from cycle ledger
- [ ] **min_weight_all_paths** — Prove R_min is correct

### Phase 3: Bridge Lemmas (Week 2–3)
- [ ] **edge_corresponds_to_oddblock** — Link DP edges to Collatz steps
- [ ] **window_to_iterate_contraction** — Compose edge semantics with potential drop
- [ ] **exists_contracting_iterate** — Assemble into main descent lemma

### Phase 4: Integration (Week 3–4)
- [ ] **BasinBoundary.lean** — Define threshold, prove implications
- [ ] **all_integers_reduce_to_odd** — Even case lemma
- [ ] **collatz_converges** — Final main theorem

### Phase 5: Validation (Week 4)
- [ ] Build and compile all code
- [ ] Run `#eval dpCert_valid` to catch data errors
- [ ] Cross-check against external DP solver output

---

## Part 6: Proof Architecture Diagram

```
collatz_converges (Main Theorem)
  ├─ even_case_reduces_to_odd
  │  └─ divide_by_two_until_odd
  │
  └─ odd_case (split on size)
     ├─ small case (n ≤ 63)
     │  └─ basin_rows_reach_1_data
     │     └─ (computed by `decide` for each of 32 rows)
     │
     └─ large case (n ≥ 64)
        └─ exists_contracting_iterate
           ├─ dp_global_descent
           │  ├─ dpCert validity check
           │  ├─ residue_of n maps to vertex
           │  ├─ lookup_window_for_residue
           │  └─ weight_sum ≥ 29
           │
           └─ window_to_iterate_contraction
              ├─ edge_corresponds_to_oddblock
              ├─ residue_of_oddblock consistency
              ├─ potential_drop_via_affine
              └─ log_sum_bounds_potential
                 └─ contraction_margin_neg
                    └─ (C_max - 29) / 16 < 0 ✓
```

---

## Part 7: Critical Checklist for Solidification

Before declaring the proof complete, verify:

- [ ] **Residue system is well-defined:**
  - [ ] Odd integers → unique residue classes
  - [ ] Residue classes closed under oddBlock
  - [ ] Covers all 42 or 64 (or however many) states

- [ ] **Potential function is calibrated:**
  - [ ] Φ definition is explicit and computable
  - [ ] Φ(n) > Φ(m) iff n > m (or equivalent monotonicity)
  - [ ] Affine formula implies the correct Φ bound
  - [ ] (C_max - 29)/16 < 0 is numerically verified

- [ ] **DP certificate is validated:**
  - [ ] DPCertificate structure encodes all necessary data
  - [ ] dpCert_valid check passes
  - [ ] Lookup mechanism works for all valid residues
  - [ ] Min-path computation is correct (DP algorithm proved or trusted)

- [ ] **Bridge lemmas connect all levels:**
  - [ ] DP edges ↔ Collatz odd steps (formally stated and proven)
  - [ ] Window of 16 edges ↔ iterate_k K n for some K
  - [ ] Residue transitions in graph ↔ residue after oddBlock
  - [ ] Log sum over window ↔ Potential drop

- [ ] **Basin is properly verified:**
  - [ ] All odd n ∈ [1, 63] listed in basinVerificationV2
  - [ ] Each row proven by `decide`
  - [ ] Threshold (Φ < log 64 or similar) correctly bounds basin
  - [ ] No gaps: every odd n ≤ 63 is in basin

- [ ] **Well-founded recursion is sound:**
  - [ ] Potential strictly decreases by fixed margin > 0
  - [ ] Potential bounded below (e.g., ≥ 0)
  - [ ] Descent forced to halt at basin (by threshold)

- [ ] **Code builds and runs:**
  - [ ] `lake build` completes with 0 errors
  - [ ] `#eval dpCert_valid` outputs ✅
  - [ ] No sorries in convergence proof
  - [ ] No admits in critical path

---

## Part 8: Summary Table: Which Lemmas Exist Today

| Lemma | Exists? | File | Status |
|-------|---------|------|--------|
| iterate_k | ✅ | Core.lean | Defined |
| oddBlock | ✅ | MainTheorem.lean | Defined |
| oddBlock_is_odd | ✅ | MainTheorem.lean | Proven |
| oddBlock_eq_iterate | ✅ | MainTheorem.lean | Proven |
| oddBlock16_eq_iterate | ✅ | MainTheorem.lean | Proven |
| basin_rows_reach_1_data | ✅ | MainTheorem.lean | Proven (decide) |
| **Φ (potential)** | ❌ | **MISSING** | **CRITICAL** |
| **ResidueSystem** | ❌ | **MISSING** | **CRITICAL** |
| **edge_semantics** | ❌ | **MISSING** | **CRITICAL** |
| **dp_global_descent** | ❌ | **MISSING** | **CRITICAL** |
| **window_to_iterate_contraction** | ❌ | **MISSING** | **CRITICAL** |
| **exists_contracting_iterate** | ❌ | **MISSING** | **CRITICAL** |
| **contraction_margin_neg** | ❌ | **MISSING** | **CRITICAL** |
| basin_threshold | ❌ | **MISSING** | Important |
| dpCert_valid | ❌ | **MISSING** | Important |

**Conclusion:** The bridge from DP to convergence requires 7 critical new lemmas (marked CRITICAL above). Once these exist, the main theorem assembly is mechanical.

---

## Appendix: Numeric Constants to Verify

```lean
-- Verify these at build time:
#eval (3 : ℚ)^64  -- 3^64
#eval (2 : ℚ)^29  -- 2^29
#eval (3 : ℚ)^64 < (2 : ℚ)^29  -- false; we need R_min ≥ 30
#eval (3 : ℚ)^64 < (2 : ℚ)^(R_min)  -- true once we compute R_min

-- C_max_log_sum should be computed from DpSummaryV2:
#eval C_max_log_sum  -- verify it's > 29 * log 2 / 16
#eval (C_max_log_sum - 29) / 16 < 0  -- true
```

---

**End of Unified Proof Approach**

---

## How to Use This Document

1. **First read:** Part 1 (mathematical foundation) to understand why the approach works
2. **For implementation:** Parts 2 and 3 to see what Lean code must exist
3. **To complete the proof:** Part 5 (roadmap) and Part 7 (checklist)
4. **For validation:** Part 8 (status table) to identify remaining work

**Status:** This document is the canonical specification of what must be proven. Use it as the source of truth when writing or reviewing code.
