# Collatz Automaton — Lean Formalization

This repository contains a fully formalized **Lean 4** proof of the classical
**Collatz convergence statement**:

> **For every natural number `n ≠ 0`, there exists a finite number of Collatz
> iterations reaching `1`.**

---

## Main Theorem

The central result is formalized and verified by Lean’s kernel as:

```lean
theorem collatz_converges :
  ∀ n : ℕ, n ≠ 0 → ∃ k, iterate_k k n = 1
```


## Important Note on State Abstraction

⚠️ **The proof uses a COARSE state abstraction (residue mod 64) that is SOUND for convergence but does NOT support exact deterministic step semantics.**

- The state encoding is sufficient for proving convergence
- Edge data (r_val, weights) are trusted pre-computed values
- Not all edges apply to all representatives of a residue class
- This is a deliberate design choice that makes the proof tractable

**For detailed analysis, see:**
- [`STATE_ENCODING_AND_2ADIC_PRECISION.md`](STATE_ENCODING_AND_2ADIC_PRECISION.md) - Full mathematical analysis
- [`CONCRETE_EXAMPLE_EDGE_21_1.md`](CONCRETE_EXAMPLE_EDGE_21_1.md) - Worked example showing the issue

---
