# TIER 2c: Semantic Foundation & Red Flag Analysis

**Critical Review of Current Codebase Against Your 4-Point Framework**

---

## ⚠️ CRITICAL FINDING: RED FLAG 1 IS ACTIVE

Your **Red Flag 1** is currently **TRIGGERED**:

> "stateOf n = { residue := n % 64, ... } but weights claim to be raw ν₂(3n+1)"
>
> "ν₂(3n+1) is not determined by n mod 64."

**Current state of codebase:**
- State is defined as `{ residue : Nat, branch : Bool }`
- StateOK requires `residue < 64`
- ExpandedEdgesV2 contains 64 edges (one per odd residue class mod 64)
- Each edge carries `r_val : Nat` claimed to be ν₂(3n+1)
- **BUT**: ν₂(3n+1) depends on the FULL VALUE of n, not just n mod 64

**Example of the problem:**
- n = 1: 3n+1 = 4 = 2², so ν₂(4) = 2
- n = 65: 3n+1 = 196 = 4×49 = 2² × 49, so ν₂(196) = 2
- n = 129: 3n+1 = 388 = 4×97 = 2² × 97, so ν₂(388) = 2
- **All have residue ≡ 1 (mod 64), all have ν₂(3n+1) = 2**

- BUT:
- n = 21: 3n+1 = 64 = 2⁶, so ν₂(64) = 6
- n = 85: 3n+1 = 256 = 2⁸, so ν₂(256) = 8
- n = 149: 3n+1 = 448 = 64×7 = 2⁶ × 7, so ν₂(448) = 6
- **All have residue ≡ 21 (mod 64), but valuations differ (6 vs 8 vs 6)**

---

## What the ExpandedEdgesV2 Data Actually Represents

Looking at the CSV structure:

```
src_residue, src_b, dst_residue, dst_b, transition_type, r_val, branch
```

**Hypothesis** (needs confirmation):

The edges are **template transitions** for each residue class mod 64.
The `r_val` field is **NOT** the true ν₂(3n+1) for all integers with that residue,
but rather an **example** or **representative** 2-adic valuation.

**Evidence from the data:**
```lean
-- (src_residue := 21, src_b := 0) has r_val := 6
-- But we showed above that n ≡ 21 (mod 64) can have ν₂(3n+1) ∈ {6, 8, ...}
```

**Second hypothesis** (more likely):

The edges represent **"expanded" transitions** that bundle together:
- A single **oddBlock step**: n ↦ oddBlock(n) = (3n+1) / 2^r
- Where r = **THE ν₂(3n+1) for that specific n**

NOT: "all integers with residue r mod 64"

Rather: "a specific subset of integers whose oddBlock output lands in the finite state graph"

---

## What MUST Be True for Tier 2c to Work

### Requirement 1: Arithmetic Step Definition (CRITICAL)

You must explicitly state: **What does one "arithmetic step" mean?**

**Option A: Raw odd-block step**
```
arithStep(n) := oddBlock(n) = (3n+1) / 2^{ν₂(3n+1)}
arithWeight(n) := ν₂(3n+1)
```

**Problem with Option A**: For this to match the graph (64 finite edges with bounded weights),
you need **proof** that:
- Every reachable odd integer n has a corresponding edge
- That edge's source state = stateOf(n)
- That edge's destination state = stateOf(arithStep(n))
- That edge's weight = arithWeight(n)

**This is almost certainly FALSE** as stated, because:
- ν₂(3n+1) can be arbitrarily large
- But edges have bounded weights (in the data: max r_val = 8)
- So either you restrict the domain, or edges don't model raw odd-blocks

**Option B: Restricted odd-block (more plausible)**

Edges model odd-blocks **only for specific odd integers whose results stay within the mod-64 universe**.

You'd need to define:
```lean
def selectedOdds : Set Nat := 
  { n | n % 2 = 1 ∧ 
         oddBlock(n) % 64 fits in our state graph ∧ 
         n satisfies other constraints }
```

And prove that the 64 edges in ExpandedEdgesV2 form a bijection with these selected odd integers.

---

### Requirement 2: stateOf Function (MANDATORY)

Currently missing. You must define:

```lean
def stateOf (n : Nat) : State := ...
```

**Constraints it must satisfy:**
1. `StateOK (stateOf n)` — always produces a valid state
2. Consistent with the arithmetic notion of "current position"
3. If using Option A (raw odd-blocks), probably:
   ```lean
   def stateOf (n : Nat) : State :=
     { residue := n % 64, 
       branch := ??? (depends on how you track branch state)
     }
   ```
   But then **you can't claim the weight is ν₂(3n+1)** because it's not uniquely determined.

4. If using Option B (restricted odd-blocks), probably:
   ```lean
   def stateOf (n : Nat) : State :=
     let r := n % 64
     let b := ???  -- need logic for which branch
     { residue := r, branch := b }
   ```

**Essential lemma:**
```lean
lemma stateOf_StateOK (n : Nat) : StateOK (stateOf n) := by
  unfold stateOf StateOK
  omega  -- or whatever proof shows residue < 64
```

---

### Requirement 3: step_edge Lemma (THE BOTTLENECK)

Once stateOf is defined, **THE CRITICAL PROOF**:

```lean
lemma step_edge (n : Nat) (hodd : n % 2 = 1) :
  ∃ e ∈ edges,
    e.src = stateOf n ∧
    e.dst = stateOf (arithStep n) ∧
    e.w = arithWeight n
```

Where you **explicitly define** arithStep and arithWeight:

```lean
def arithStep (n : Nat) : Nat := oddBlock n
def arithWeight (n : Nat) : Nat := twoAdicValuation (3 * n + 1)
```

**This lemma is unprovable as written if:**
- arithStep and arithWeight are not actually computed by the edges
- Or if stateOf doesn't preserve the right invariants
- Or if arithWeight is unbounded but edges have bounded weights

**Proof strategy** (if it's provable):
1. Compute `stateOf n` to get `s = { residue := n % 64, branch := ... }`
2. Compute `oddBlock n` (from ExpandedEdgesV2 data? Or via Mathlib twoAdicValuation?)
3. Compute `stateOf (oddBlock n)` to get `s' = { ... }`
4. **Look up the edge** in the edges list that has:
   - src = s
   - dst = s'
5. Verify that edge's weight matches ν₂(3n+1)
6. Conclude the edge exists.

**The hard part**: Step 2 and 5 require knowledge of the actual CSV data, or a proof that ExpandedEdgesV2 encodes the right mappings.

---

### Requirement 4: Determinism (Important But Not Blocking)

```lean
lemma outgoing_unique (n : Nat) (hodd : n % 2 = 1) :
  ∃! e, e ∈ edges ∧ e.src = stateOf n ∧ e.dst = stateOf (arithStep n)
```

This ensures that "the path induced by arithmetic sequence" is well-defined and unique.

If not provable: paths become non-deterministic, which complicates DP bounds (but is still possible).

---

## Current Data: What We Have

### ExpandedEdgesV2 Structure
```lean
structure ExpandedEdge where
  src_residue : Nat   -- 0..63
  src_b : Nat         -- 0 or 1
  dst_residue : Nat   -- 0..63
  dst_b : Nat         -- 0 or 1
  transition_type : String  -- "thick" or "thin"
  r_val : Nat         -- claimed 2-adic valuation
  branch : String     -- "det" (deterministic)
```

**Total: 64 edges** (one per odd residue class mod 64, with two branches each, totaling 128 edge definitions for 32 starting states)

**r_val distribution:**
```
1: appears 32 times (thin edges)
2: appears 16 times
3: appears 8 times
4: appears 4 times
5: appears 2 times
6: appears 1 time
8: appears 1 time
```

**Key observation**: r_val is bounded (max = 8), but ν₂(3n+1) is unbounded.

---

## How to Resolve RED FLAG 1

**Choice A: Define what "the edges" actually represent**

Document: "ExpandedEdgesV2 contains 64 edges that represent oddBlock steps
for a specific subset of odd integers. The mapping is: ..."

Then define stateOf and arithStep such that step_edge is provable.

**Choice B: Admit the edges are abstract templates**

Document: "We use the 64-edge graph as an abstract state machine.
Convergence is proven by showing that the mod-64 graph dynamics
have the right contraction properties, independent of the arithmetic semantics."

This requires a **different proof strategy** than what's currently described.

---

## The Bottom Line

**Before implementing Tier 2c, resolve:**

1. **What is the mapping n ↔ (residue, branch)?**
   - Is branch derived from oddBlock trajectory?
   - Or is it a separate state variable?

2. **What is arithStep(n)?**
   - Raw oddBlock? Or something bounded?

3. **What is arithWeight(n)?**
   - True ν₂(3n+1)? Or a proxy?

4. **Can you prove step_edge?**
   - If yes: Tier 2c is on solid ground
   - If no: The method needs revision

---

## Recommended Next Actions

### Phase 0: Clarification (1-2 hours)
- [ ] Read the original research paper / documentation that generated ExpandedEdgesV2
- [ ] Confirm whether edges model:
  - (A) Raw oddBlock for all odd n, or
  - (B) oddBlock restricted to a specific finite set, or
  - (C) Something else entirely
- [ ] Document the intended semantics explicitly in Lean comments

### Phase 1: Formalize stateOf and step_edge (2-3 hours)
- [ ] Define `stateOf : Nat → State` with proof of StateOK
- [ ] Prove or identify blockers for `step_edge` lemma
- [ ] If unprovable: revisit the semantics

### Phase 2: Build Tier 2c (2-3 hours)
- [ ] Define `trajectoryPath : Nat → PathLen L`
- [ ] Prove `weightSum_eq_valSum` (exact equality, not inequality)
- [ ] Verify: `#check` and `#print axioms`

---

## Status Flags

| Item | Status | Blocker |
|------|--------|---------|
| Arithmetic step defined | ❌ MISSING | RED FLAG 1 |
| stateOf formalized | ❌ MISSING | Required for step_edge |
| step_edge lemma | ❌ MISSING | Critical bottleneck |
| Determinism | ❌ MISSING | Needed for well-defined paths |
| trajectoryPath | ❌ BLOCKED | Needs step_edge |
| weightSum_eq_valSum | ❌ BLOCKED | Needs trajectoryPath |

**Tier 2c is blocked on clarification of RED FLAG 1.**

---

## Appendix: Understanding the ExpandedEdges Data

**Sample edge:**
```
src_residue := 1, src_b := 0
→ dst_residue := 1, dst_b := 0
transition_type := "thick", r_val := 2, branch := "det"
```

**Interpretation options:**

**Option 1**: "Odd n with n ≡ 1 (mod 64) and branch=0 maps to oddBlock(n) ≡ 1 (mod 64), with weight ν₂(3n+1) = 2"
- Problem: ν₂(3n+1) ≠ 2 for all such n (see examples above)

**Option 2**: "A representative odd n with n ≡ 1 (mod 64) has oddBlock(n) ≡ 1 (mod 64), and for that specific n, ν₂(3n+1) = 2"
- Problem: Which specific n? How do you handle other n with residue 1 mod 64?

**Option 3**: "The graph is an abstract machine with 64 nodes. Edge (1,0) → (1,0) with weight 2 is part of the automaton. Whether it matches real odd integers is a separate concern (either proven or assumed)."
- Problem: Conflicts with claimed "Collatz convergence proof"

**Most likely**: The ExpandedEdgesV2 was generated from a computational tool that enumerated Collatz trajectories and abstracted them to the mod-64 graph. The mapping is implicit in the CSV structure and needs to be reverse-engineered or documented.

---

## Questions for the Research Archive

If you have access to the original generation code or paper:

1. How was ExpandedEdgesV2 generated?
2. For each edge (r, b) → (r', b'), what was the input odd integer n?
3. How is branch (0 or 1) determined in the trajectory?
4. Are all odd integers covered, or only a subset?
5. Why are there two branch states per residue?

**Without these answers, Tier 2c cannot be formalized.**
