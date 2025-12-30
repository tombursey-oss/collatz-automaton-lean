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

