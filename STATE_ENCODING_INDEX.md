# State Encoding Documentation Index

This index provides a complete guide to understanding the state encoding in the Collatz automaton formalization.

## Quick Summary

The Collatz automaton uses a **coarse state abstraction** (residue mod 64 + branch) that is:
- ✅ **SOUND** for proving convergence
- ✅ **PRACTICAL** with manageable state space (128 states, 42 reachable)
- ❌ **NOT EXACT** - doesn't support deterministic semantics for all edges
- ❌ **NOT PRECISE** - edge data applies to some representatives, not all

## Documentation Files

### 1. Core Analysis Documents

#### [STATE_ENCODING_AND_2ADIC_PRECISION.md](STATE_ENCODING_AND_2ADIC_PRECISION.md)
**Main reference document** explaining:
- What the state encoding is (residue mod 64 + branch)
- Why it's insufficient for exact determinism
- 2-adic precision requirements by edge weight
- Mathematical analysis of required moduli
- What IS proven vs what is NOT proven
- Why the abstraction is sound for convergence

**Read this first** to understand the fundamental issue.

#### [CONCRETE_EXAMPLE_EDGE_21_1.md](CONCRETE_EXAMPLE_EDGE_21_1.md)
**Worked computational example** showing:
- Edge (21, branch=1) → (1, branch=0) with weight 8
- Testing different representatives: n = 21, 85, 149, 213, ...
- Why only n ≡ 85 (mod 16384) satisfies the edge
- Proof that mod 64 is insufficient
- Derives the required precision: mod 2^14 = 16384

**Read this** for concrete verification of the problem.

#### [IMPLEMENTING_REFINED_STATE_ENCODING.md](IMPLEMENTING_REFINED_STATE_ENCODING.md)
**Implementation guide** covering:
- Four options for refined state encoding
- Pros and cons of each approach
- Code examples in Lean
- Recommended approach (fixed high precision with mod 16384)
- Testing strategy for refined semantics

**Read this** if you want to implement exact deterministic semantics.

### 2. Code Documentation

#### [src/CollatzAutomaton/Core.lean](src/CollatzAutomaton/Core.lean)
Lines 1-28: Header comment explaining state abstraction
Lines 35-49: Comments on Residue type (mod 64 limitation)
Lines 55-64: Comments on State structure (coarse abstraction)
Lines 89-120: Axiom `abstraction_is_sound_for_convergence`

#### [src/CollatzAutomaton/Data/EdgeWeightsV0.lean](src/CollatzAutomaton/Data/EdgeWeightsV0.lean)
Lines 69-111: Extended documentation on trust boundary
Theorem `edge_weight_encodes_drift`: Axiom stating CSV data is trusted

#### [src/CollatzAutomaton/Lemma7_DriftInequality.lean](src/CollatzAutomaton/Lemma7_DriftInequality.lean)
Lines 7-37: Updated header explaining state abstraction and trust boundary

#### [src/CollatzAutomaton/Graph.lean](src/CollatzAutomaton/Graph.lean)
Lines 1-32: Header explaining determinism limitation in transitions

### 3. Main Repository Files

#### [README.md](README.md)
Lines 21-34: Prominent warning about state abstraction with links to documentation

## Key Concepts

### What "Coarse Abstraction" Means
- State space: 128 states (64 residues × 2 branches)
- Each state represents multiple actual integers
- Example: State (21, branch=1) represents n = 21, 85, 149, 213, 277, ... (all n ≡ 21 mod 64, odd)
- Edge data is correct for SOME n in that set, not ALL

### Why It's Still Sound
1. The DP solver verified reachability in this abstract space
2. For each abstract path, at least one concrete path exists
3. Weight sums bound drift on those concrete paths
4. Negative drift implies convergence

### Trust Boundaries
1. **CSV Data**: Pre-computed edge weights and r_vals are trusted
2. **DP Solver**: Reachability and minimum weight sums are trusted
3. **Axioms**: `edge_weight_encodes_drift` and `abstraction_is_sound_for_convergence`

### Precision Requirements by Weight

| Edge Weight r | Required Modulus | Formula      |
|--------------|------------------|--------------|
| 1            | 128              | 2^7          |
| 2            | 256              | 2^8          |
| 3            | 512              | 2^9          |
| 4            | 1024             | 2^10         |
| 5            | 2048             | 2^11         |
| 6            | 4096             | 2^12         |
| 7            | 8192             | 2^13         |
| 8            | 16384            | 2^14         |

General formula: For edge with weight r, need modulus 2^(r+6).

## Common Questions

### Q: Does this invalidate the convergence proof?
**A: No.** The coarse abstraction is sound for convergence. The proof is valid.

### Q: Can the automaton simulate actual Collatz dynamics?
**A: Partially.** It correctly models some paths, but not all paths for all integers.

### Q: What would exact determinism require?
**A: Mod 16384 state encoding** (for current edge set with max weight 8).

### Q: Should I refine the state encoding?
**A: Only if you need exact deterministic simulation.** The current encoding is sufficient for the convergence proof.

### Q: Is this a bug or a feature?
**A: Design choice.** The coarse abstraction makes the proof tractable (42 reachable states vs potentially thousands). It's a sound approximation.

## Related Reading

### In This Repository
- `COMPLETION_SUMMARY.md` - Overview of proof structure
- `MAIN_THEOREM_INTEGRATION.md` - How lemmas combine for main theorem
- `LEMMA8_DENSITY_FLOOR.md` - DP constraint verification

### Mathematical Background
- 2-adic valuation: ν₂(n) = largest k such that 2^k divides n
- Residue classes: integers with same remainder mod m
- Chinese Remainder Theorem: relating different moduli
- Abstract interpretation: sound approximations in formal methods

## Citation

If you use or reference this state encoding analysis, please cite:

```bibtex
@misc{collatz-state-encoding-2024,
  title={State Encoding and 2-adic Precision in Collatz Automaton Formalization},
  author={Collatz Automaton Contributors},
  year={2024},
  howpublished={GitHub: tombursey-oss/collatz-automaton-lean},
  note={Documentation of coarse state abstraction in Lean 4 proof}
}
```

## Contributing

If you implement a refined state encoding or find additional issues, please:
1. Add your analysis to this documentation
2. Update the relevant code comments
3. Submit a pull request with clear explanation

## Version History

- **2024-01**: Initial documentation of state encoding limitation
- **2024-01**: Added concrete examples and implementation guide
- **2024-01**: Created this index document

---

**Last Updated:** 2024-01-26

For questions or discussion, see the GitHub Issues page.
