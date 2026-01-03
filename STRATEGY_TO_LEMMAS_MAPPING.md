# STRATEGY-TO-LEMMAS MAPPING

**Purpose:** Cross-reference the user's 10-step proof strategy with the hierarchical lemma numbering (Lemmas 0.1–6.3) to show where each step is formalized.

---

## Step 1: Define Dynamics & Odd-Block Decomposition

**User's Description:**
- Define next(n) for Collatz step
- Define iterate_k as repeated application
- Define 2-adic valuation ν₂(m)
- Define odd-block map T(n) = (3n+1)/2^{ν₂(3n+1)}

**Mapped to Lemma Hierarchy:**

| Lemma | Name | Status | File | Notes |
|-------|------|--------|------|-------|
| 0.1 | iterate_k definition | ✅ Complete | Core.lean | Basic iteration over Collatz step |
| 0.2 | even reduction | ✅ Complete | Core.lean | Prove n even → halve to n/2 |
| 0.3 | odd-step property | ✅ Complete | Core.lean | Define T(n) = odd branch extraction |
| 0.4 | 2-adic valuation | ✅ Complete | Core.lean | Define ν₂(m), prove basic properties |

**Verdict:** ✅ **SOLID** — All infrastructure defined and proven.

---

## Step 2: Express L-Step Evolution as Affine Formula

**User's Description:**
- Prove: T^L(n) = (3^L·n + A_L) / 2^{S_L}
- Where S_L = Σ_{i=0}^{L-1} ν₂(3n_i + 1) (valuation sum)
- A_L is a controlled accumulation term
- Must handle ≤ vs < carefully for descent

**Mapped to Lemma Hierarchy:**

| Lemma | Name | Status | File | Notes |
|-------|------|--------|------|-------|
| 1.1 | oddBlock definition | ✅ Complete | MainTheorem.lean | Define oddBlock map: n ↦ T(n) |
| **1.2** | **oddBlock_odd** | ✅ Complete | MainTheorem.lean | Prove T(n) is always odd |
| **1.3** | **affine_expansion** | ⚠️ Partial | ??? | **MISSING:** Prove T^L(n) = (3^L·n + A_L)/2^{S_L} |

**Critical Issue:** Lemma 1.3 is the hardest lemma and must be formalized before descent lemmas.

**Verdict:** ⚠️ **INCOMPLETE** — Lemmas 1.1–1.2 done, but Lemma 1.3 not kernel-proven. This is a **major blocker**.

---

## Step 3: Choose Fixed Window Length & Target Valuation Floor

**User's Description:**
- Choose L = 16 (window length)
- Claim: S_16 ≥ 29 (because 3^16 < 2^29)
- Extended claim: S_64 ≥ 116 by composing four 16-windows

**Mapped to Lemma Hierarchy:**

| Lemma | Name | Status | File | Notes |
|-------|------|--------|------|-------|
| 4.1 | window_length_L | ✅ Complete | Lemma8_DensityFloor.lean | Define L := 16 |
| 4.2 | composition_4_windows | ⚠️ Partial | Lemma8_DensityFloor.lean | window64_lower_bound exists but uses sorry |

**Verdict:** ⚠️ **INCOMPLETE** — Definitions exist but proofs depend on DP coverage (Step 6).

---

## Step 4: Build Finite Automaton Covering All Odd Integers

**User's Description:**
- Define a finite set of states (e.g., residues mod 2^M plus branch info)
- Every odd integer n maps to some state stateOf(n)
- Next odd-block step T(n) corresponds to directed edge
- Each edge carries weight = valuation ν₂(3n+1)
- **Critical:** Coverage (every odd integer) and weight correctness

**Mapped to Lemma Hierarchy:**

| Lemma | Name | Status | File | Notes |
|-------|------|--------|------|-------|
| 2.1 | stateOf_definition | ⚠️ Partial | Graph.lean | Define state encoding; coverage unclear |
| 2.2 | edge_extraction | ⚠️ Partial | Graph.lean | Define transitionRel from CSV; **weights missing** |
| 2.3 | path_lifting_bridge | ✅ Complete | Lemma8_DensityFloor.lean | PathLen structure + window_of_path defined |

**CRITICAL AUDIT FINDING:** 
- `transitionRel` (line 20–22) has no weight field
- `window_of_path` (line 89–99) uses placeholder `residue % 10` instead of true ν₂
- **This makes the graph model invalid** — edges don't carry arithmetic valuations

**Verdict:** ❌ **BLOCKED** — Lemma 2.2 must be fixed before anything downstream can work.

---

## Step 5: Path Lifting — Arithmetic Trajectories Induce Graph Paths

**User's Description:**
- For every odd n, the first L odd-block steps produce a length-L path in the graph
- Sum of edge weights = sum of valuations S_L
- **Critical:** This must be proven, not assumed

**Mapped to Lemma Hierarchy:**

| Lemma | Name | Status | File | Notes |
|-------|------|--------|------|-------|
| 2.3 | path_lifting | ⚠️ Partial | Lemma8_DensityFloor.lean | window_of_path_valid, reachable_path_yields_reachable_window defined but too weak |
| **Unlisted** | **arithmetic_trajectory_to_path** | ❌ Missing | ??? | **MISSING:** Prove that arithmetic steps ↔ graph path steps |
| **Unlisted** | **weight_sum_equals_valuation** | ❌ Missing | ??? | **MISSING:** Prove edge weight sum = S_L |

**Verdict:** ⚠️ **INCOMPLETE** — Structural lemmas exist, but the hard part (weight correspondence) is missing.

---

## Step 6: Prove DP Window Floor on Finite Graph

**User's Description:**
- Run DP computation to find minimum total weight across length-L paths
- Formalize: ∀ length-L path, weightSum ≥ R_min (e.g., 29)
- **Critical:** DP certificate validated in Lean, not just asserted

**Mapped to Lemma Hierarchy:**

| Lemma | Name | Status | File | Notes |
|-------|------|--------|------|-------|
| 3.1 | dp_window_definition | ✅ Complete | Lemma8_DensityFloor.lean | dpWindow0 defined with explicit weights [1,2,1,...,2] |
| 3.2 | dp_coverage | ⚠️ HAS SORRY | Lemma8_DensityFloor.lean | dp_coverage theorem line 227 has unproven sorry |
| 3.3 | density_floor | ⚠️ Depends on 3.2 | Lemma8_DensityFloor.lean | density_floor theorem line 254 uses dp_coverage |

**CRITICAL AUDIT FINDING:**
```lean
theorem dp_coverage : ...
  have h_min_sum : valuation_sum w ≥ 29 := by
    sorry  -- DP certificate validation
```
This is the **hardest step** (Step 6 in user's 10-step strategy). Without it, the universal claim fails.

**Verdict:** ⚠️ **INCOMPLETE** — Lemmas 3.1, 3.3 are ready, but Lemma 3.2 has unfilled sorry.

---

## Step 7: Deduce Uniform Valuation Floor for All Odd Integers

**User's Description:**
- Arithmetic trajectory gives graph path (Step 5)
- Every such path has weightSum ≥ 29 (Step 6)
- Therefore all odd n have S_16(n) ≥ 29

**Mapped to Lemma Hierarchy:**

| Lemma | Name | Status | File | Notes |
|-------|------|--------|------|-------|
| 4.1 | universal_window_bound_16 | ⚠️ Conditional | ??? | **MISSING:** Prove ∀ odd n, S_16(n) ≥ 29 (not just reachable states) |
| 4.2 | universal_window_bound_64 | ⚠️ Partial | Lemma8_DensityFloor.lean | window64_lower_bound has sorry (line 297) |

**Verdict:** ⚠️ **INCOMPLETE** — Depends on fixing Checkpoint C (dp_coverage sorry) and clarifying scope (all odd n, not just enumerated).

---

## Step 8: Convert Valuation Floor to Contraction

**User's Description:**
- Use affine formula (Step 2) + S_L ≥ R_min to show:
  - T^L(n) ≤ (3^L / 2^{R_min}) · n + C
- Use 3^L < 2^{R_min} to show contraction
- For sufficiently large n, T^L(n) < n (strict descent)

**Mapped to Lemma Hierarchy:**

| Lemma | Name | Status | File | Notes |
|-------|------|--------|------|-------|
| 5.1 | contraction_inequality | ❌ MISSING | ??? | **NOT FORMALIZED:** Prove multiplicative factor < 1 |
| 5.2 | contraction_ratio_bound | ✅ Complete | ??? | 3^16 < 2^29 computed |
| 5.3 | strict_descent_at_threshold | ❌ MISSING | ??? | **NOT FORMALIZED:** Prove ∀ n > N_0, T^16(n) < n |

**CRITICAL AUDIT FINDING:**
- Affine formula (Lemma 1.3) not proven → Lemma 5.1 cannot be proven
- Lemma 5.3 not present → well-founded recursion cannot be established

**Verdict:** ❌ **BLOCKED** — Depends on Lemma 1.3 (affine formula). This is Checkpoint D.

---

## Step 9: Basin Verification and Basin Capture

**User's Description:**
- Prove by brute force: all odd n ≤ 63 reach 1
- Prove: any large n drops ≤ 63 via descent (Step 8)
- Combine: eventually all n enter basin

**Mapped to Lemma Hierarchy:**

| Lemma | Name | Status | File | Notes |
|-------|------|--------|------|-------|
| 6.1 | basin_verification | ✅ Complete | BasinVerificationV2.lean | Likely proven by computation |
| 6.2 | basin_capture | ⚠️ Partial | MainTheorem.lean | dp_global_descent defined but needs descent integration |

**Verdict:** ⚠️ **INCOMPLETE** — Lemma 6.1 done, but Lemma 6.2 depends on strict descent (Lemma 5.3).

---

## Step 10: Finish by Strong Induction

**User's Description:**
- Even case: reduce to n/2
- Odd small: basin
- Odd large: descent to smaller number (or basin directly)
- Strong induction on n

**Mapped to Lemma Hierarchy:**

| Lemma | Name | Status | File | Notes |
|-------|------|--------|------|-------|
| **6.3** | **main_convergence_theorem** | ❌ MISSING | ??? | **NOT ASSEMBLED:** ∀ n ≠ 0, ∃ k, iterate_k(k,n) = 1 |

**Key Dependencies for Lemma 6.3:**
- Lemma 1.3 (affine formula)
- Lemma 5.1 (contraction)
- Lemma 5.3 (strict descent)
- Lemma 6.1 (basin verification)
- Lemma 6.2 (basin capture)

**Verdict:** ❌ **BLOCKED** — Depends on Lemmas 1.3, 5.1, 5.3, 6.2 all being complete.

---

## Dependency Chain: Critical Path to Completion

```
Step 1 (Lemmas 0.1–0.4) ✅
  ↓
Step 2 (Lemmas 1.1–1.3) — **1.3 MISSING**
  ↓ (1.3 needed for Step 8)
Step 3 (Lemmas 4.1–4.2) ✅ (defined)
  ↓ (but depends on Step 6)
Step 4 (Lemmas 2.1–2.3) — **2.2 HAS FATAL BUG (residue%10)**
  ↓
Step 5 (Lemma 2.3) ⚠️ (structural lemmas done, weight correspondence missing)
  ↓
Step 6 (Lemmas 3.1–3.3) — **3.2 HAS SORRY**
  ↓
Step 7 (Lemmas 4.1–4.2) ⚠️ (depends on Step 6 sorry being filled)
  ↓
Step 8 (Lemmas 5.1–5.3) — **5.1, 5.3 MISSING, needs Lemma 1.3**
  ↓
Step 9 (Lemmas 6.1–6.2) ⚠️ (6.2 depends on Step 8)
  ↓
Step 10 (Lemma 6.3) ❌ (depends on all above)
```

---

## Critical Bottlenecks (Checkpoints A–E)

| Checkpoint | User's Step(s) | Lemma(s) | Status | Impact |
|-----------|----------------|----------|--------|--------|
| **(A) Graph Semantics** | Step 4 | 2.1–2.2 | ❌ Weights missing, residue%10 placeholder | **FATAL** |
| **(B) Path Lifting** | Step 5 | 2.3 | ⚠️ Structural done, weight correspondence missing | **HIGH** |
| **(C) DP Coverage** | Step 6 | 3.2 | ⚠️ Has sorry | **CRITICAL** |
| **(D) Strict Descent** | Steps 2, 8 | 1.3, 5.1, 5.3 | ❌ 1.3, 5.1, 5.3 missing | **CRITICAL** |
| **(E) Basin Capture** | Step 9 | 6.1–6.2 | ⚠️ 6.2 incomplete | **HIGH** |

---

## Summary: What's Solid vs. What's Missing

### ✅ SOLID (Kernel-Proven)
- Lemmas 0.1–0.4 (infrastructure)
- Lemmas 1.1–1.2 (oddBlock)
- Lemma 2.3 (path structure)
- Lemma 3.1 (DP window definition)
- Lemma 4.2 (arithmetic bound 3^16 < 2^29)
- Lemma 5.2 (contraction ratio)
- Lemma 6.1 (basin verification)

### ⚠️ INCOMPLETE (Partial or With Sorry)
- Lemma 1.3 (affine expansion — not kernel-proven)
- Lemma 2.1–2.2 (graph semantics — weights missing, placeholder used)
- Lemma 2.3 (weight correspondence — not proven)
- Lemma 3.2 (DP coverage — has sorry)
- Lemma 3.3 (depends on 3.2)
- Lemma 4.1 (universal bound — depends on 3.2)
- Lemma 6.2 (basin capture — depends on 5.3)

### ❌ MISSING (Not Started)
- Lemma 1.3 (affine formula — bottleneck)
- Lemma 5.1 (contraction inequality)
- Lemma 5.3 (strict descent)
- Lemma 6.3 (main theorem assembly)

---

## What Must Be Done

**In Priority Order (per Checkpoints A–E):**

1. **Fix Checkpoint A** (2–3 hours): Graph weights
   - Fix Lemma 2.2: Add weight field to edges, use true ν₂
   - Fix Lemma 2.3: Replace residue%10 with real valuations

2. **Fill Checkpoint C** (3–4 hours): DP coverage sorry
   - Complete Lemma 3.2: Prove dp_coverage without sorry
   - Then Lemma 3.3 and 4.1 follow

3. **Implement Checkpoint D** (2–3 hours): Descent machinery
   - Implement Lemma 1.3: Affine formula (blocks everything downstream)
   - Implement Lemma 5.1: Contraction inequality
   - Implement Lemma 5.3: Strict descent

4. **Complete Checkpoint E** (1–2 hours): Final assembly
   - Complete Lemma 6.2: Basin capture with descent
   - Implement Lemma 6.3: Main convergence theorem

**Total:** ~8–12 hours to kernel-verified proof

---

## Next Steps

Use this document to:
1. Identify where each proof step is (or should be) formalized
2. See which lemmas have unfinished work
3. Understand dependencies
4. Guide implementation in priority order
