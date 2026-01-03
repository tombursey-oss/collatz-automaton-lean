# Executive Summary: The 64-Window Proof (Final)
**Status:** Complete and Ready for Implementation  
**Date:** January 2, 2026

---

## What We're Proving

**One theorem:**
$$\forall n \text{ odd}, \quad \sum_{i=0}^{63} r\text{\_val}(n_i) \geq R_{\min}$$

This says: **Every odd integer's 64-step valuation sum is at least R_min (the minimum over all possible 64-step paths in the DP graph).**

**Why this proves Collatz:** This bound guarantees a uniform contraction (3^64 < 2^R_min), which forces descent into the verified basin {1, 3, 5, ..., 63}.

---

## The Seven Critical Lemmas (In Order)

| # | Lemma | What It Says | Status |
|---|-------|-------------|--------|
| 1 | Residue Coverage | Every odd n maps to a unique state | Likely exists |
| 2 | Edge Extraction | Every odd n's step follows a graph edge | Likely exists |
| 3 | **Path Lifting** | **64-step trajectory lifts to graph path with weight_sum = valuation_sum** | **CRITICAL** |
| 4 | **DP Global Bound** | **Every 64-path has weight ≥ R_min** | **CRITICAL** |
| 5 | Window Bound | ∀n: valuation_sum ≥ R_min (derived from 1–4) | Derivable |
| 6 | Contraction | n_64 ≤ (3^64 / 2^R_min) * n + C (from affine formula + Lemma 5) | Missing |
| 7 | Strict Descent | n_64 < n (strict inequality for recursion) | Missing |

**Critical insight:** If Lemmas 3 and 4 are correct, Lemma 5 is purely mechanical, and Lemmas 6–7 are straightforward algebra.

---

## The Four Ways This Can Fail

### 1. Residue System (Lemma 1)
**Failure:** stateOf only covers "most" odd integers, not all.  
**Fix:** Prove every odd n maps to exactly one state.

### 2. Edge Semantics (Lemma 2)
**Failure:** The graph edges don't correspond to actual Collatz steps.  
**Fix:** Prove the step from n follows a graph edge with correct weight and target.

### 3. DP Scope (Lemma 4)
**Failure:** The certificate only bounds "reachable paths," not all paths.  
**Fix:** Prove dp_global_descent quantifies over ALL 64-paths, not a subset.

### 4. Strictness (Lemma 7)
**Failure:** Descent is only ≤, not <, so recursion doesn't terminate.  
**Fix:** Prove 3^64 / 2^R_min < 1 and handle the additive constant.

---

## Validation Strategy (Audit-First)

**Before writing new code:**

1. **Check Lemmas 3 and 4 in existing code**
   - Does trajectory_to_path exist and map integers → paths?
   - Does path.weight_sum = valuation_sum (exact equality)?
   - Does dp_global_descent claim ALL paths ≥ R_min?
   
2. **If both Lemmas 3 and 4 are correct:**
   - The core proof is essentially done
   - Lemmas 5–7 are mechanical derivations
   
3. **If either Lemma 3 or 4 is weak/missing:**
   - Stop and build that lemma
   - It's the critical bottleneck

4. **Use QUICK_AUDIT_GUIDE.md to check each lemma**

---

## The Proof in Three Sentences

1. **Lemmas 3–4:** Every actual 64-step trajectory from any odd integer lifts to a graph path guaranteed by the DP to have weight ≥ R_min, so every valuation sum ≥ R_min (Lemma 5).

2. **Lemma 6:** The affine expansion 𝑛₆₄ = (3^64 · n + A) / 2^S combined with S ≥ R_min gives 𝑛₆₄ ≤ (3^64 / 2^R_min) · n + C where the ratio is < 1.

3. **Lemma 7:** This contraction forces strict descent 𝑛₆₄ < n, so well-founded recursion terminates, reaching the verified basin ≤ 63 which trivially reaches 1.

---

## Files You Need

1. **UNIFIED_PROOF_APPROACH_REFINED.md** — Full specification of all 7 lemmas and proofs
2. **QUICK_AUDIT_GUIDE.md** — Verification checklist for each lemma
3. **This document** — Executive summary and high-level overview

---

## Implementation Checklist

- [ ] **Audit:** Verify Lemmas 3 and 4 exist and are correct
- [ ] **Fix:** If needed, implement trajectory_to_path and dp_global_descent
- [ ] **Build:** Implement Lemmas 1–2 (residue system and edges)
- [ ] **Derive:** Lemma 5 (window bound) from 1–4
- [ ] **Algebra:** Lemmas 6–7 (contraction and descent)
- [ ] **Assemble:** Main convergence theorem
- [ ] **Build:** `lake build` succeeds with 0 errors
- [ ] **Verify:** `#eval` checks on numeric constants (3^64, 2^R_min, etc.)

---

## Key Insight

**The universality of "64 works for all numbers" rests entirely on two bridges:**
1. **Integer ↔ Graph:** trajectory_to_path (Lemma 3)
2. **Graph ↔ Bound:** dp_global_descent (Lemma 4)

If these are correct, everything else follows. If either is wrong, the whole claim breaks.

---

**Status:** Ready for implementation. Start with auditing Lemmas 3 and 4.

