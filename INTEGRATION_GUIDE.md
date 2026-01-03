# Integration Guide: Using These Documents
**Status:** Final Navigation Document  
**Date:** January 2, 2026

---

## What These Documents Do

You now have **four coordinated documents** that form a complete specification for the Collatz proof:

| Document | Purpose | Audience |
|----------|---------|----------|
| **PROOF_EXECUTIVE_SUMMARY.md** | High-level overview in 3 sentences | Everyone |
| **UNIFIED_PROOF_APPROACH_REFINED.md** | Complete specification of 7 lemmas + failure modes | Proof writers |
| **QUICK_AUDIT_GUIDE.md** | Verification checklist for each lemma | Code reviewers |
| **CODE_SEARCH_CHECKLIST.md** | Find which lemmas already exist in codebase | Developers |

---

## Reading Order

### For First-Time Readers
1. Start with **PROOF_EXECUTIVE_SUMMARY.md** — 2 minutes
2. Read **UNIFIED_PROOF_APPROACH_REFINED.md Part 1** (core claim) — 5 minutes
3. Skim **UNIFIED_PROOF_APPROACH_REFINED.md Part 2** (7 lemmas) — 10 minutes

### For Auditing Existing Code
1. **CODE_SEARCH_CHECKLIST.md** — Find the 7 lemmas in your codebase
2. **QUICK_AUDIT_GUIDE.md** — Verify each one is correct
3. Report findings in CODE_SEARCH_CHECKLIST.md's summary table

### For Writing New Code
1. **UNIFIED_PROOF_APPROACH_REFINED.md Part 2** — Copy the lemma signature you need
2. **QUICK_AUDIT_GUIDE.md** — Check the "Verification Questions" for your lemma
3. **UNIFIED_PROOF_APPROACH_REFINED.md Part 3** — Understand the failure modes to avoid

### For Code Review
1. **QUICK_AUDIT_GUIDE.md** — Run through the checklist for each lemma
2. **UNIFIED_PROOF_APPROACH_REFINED.md Part 3** — Check against the 4 failure points
3. **UNIFIED_PROOF_APPROACH_REFINED.md Part 8** — Verify the final checklist is satisfied

---

## The Master Checklist

Before you declare the proof complete, fill this in:

### Existence and Location

- [ ] **Lemma 1 (Residue Coverage)** exists in: ___________________
- [ ] **Lemma 2 (Edge Extraction)** exists in: ___________________
- [ ] **Lemma 3 (Path Lifting)** exists in: ___________________
- [ ] **Lemma 4 (DP Global Bound)** exists in: ___________________
- [ ] **Lemma 5 (Window Bound)** exists in: ___________________
- [ ] **Lemma 6 (Contraction)** exists in: ___________________
- [ ] **Lemma 7 (Strict Descent)** exists in: ___________________

### Correctness Verification (Use QUICK_AUDIT_GUIDE.md)

- [ ] **Lemma 1**: Passed all verification questions ✅
- [ ] **Lemma 2**: Passed all verification questions ✅
- [ ] **Lemma 3**: Passed all verification questions ✅ **CRITICAL**
- [ ] **Lemma 4**: Passed all verification questions ✅ **CRITICAL**
- [ ] **Lemma 5**: Passed all verification questions ✅
- [ ] **Lemma 6**: Passed all verification questions ✅
- [ ] **Lemma 7**: Passed all verification questions ✅

### Build Status

- [ ] `lake build` completes with 0 errors
- [ ] No `sorry` or `admit` in the critical path
- [ ] `#eval contraction_margin_neg` verifies 3^64 / 2^R_min < 1
- [ ] `#eval dpCert_valid` verifies certificate integrity

### Failure Mode Checks (Part 3 of UNIFIED_PROOF_APPROACH_REFINED.md)

- [ ] **Failure Point A (Residue System):** stateOf covers all odd integers
- [ ] **Failure Point B (Edge Semantics):** step_edge proves the actual step follows an edge
- [ ] **Failure Point C (DP Scope):** dp_global_descent quantifies over ALL paths
- [ ] **Failure Point D (Strictness):** oddIter64_strict_descent proves n_64 < n

### Documentation

- [ ] Code has clear comments linking each lemma to the unified approach
- [ ] Type signatures match UNIFIED_PROOF_APPROACH_REFINED.md exactly
- [ ] Proof strategy documented in comments

---

## If You Get Stuck

| Problem | Solution |
|---------|----------|
| "I don't understand why 64 works" | Read PROOF_EXECUTIVE_SUMMARY.md |
| "What lemmas do I need to prove?" | Read UNIFIED_PROOF_APPROACH_REFINED.md Part 2 |
| "How do I check if my lemma is correct?" | Use QUICK_AUDIT_GUIDE.md |
| "Where should this code go?" | Read CODE_SEARCH_CHECKLIST.md for expected locations |
| "Why does the proof fail?" | Check the 4 failure modes in UNIFIED_PROOF_APPROACH_REFINED.md Part 3 |
| "Lemma 3 vs. Lemma 4 — which is more critical?" | Both equally critical; they're the bridge |
| "Can I skip any lemma?" | No; all 7 are necessary in dependency order |
| "What if my DP certificate is different?" | As long as dp_global_descent is correct, the rest works |

---

## Document Cross-References

**In PROOF_EXECUTIVE_SUMMARY.md:**
- See "The Seven Critical Lemmas" table for overview
- See "The Four Ways This Can Fail" to understand risks

**In UNIFIED_PROOF_APPROACH_REFINED.md:**
- Part 1: The core theorem that proves "64 works for all numbers"
- Part 2: Full specification of all 7 lemmas with examples
- Part 3: Detailed discussion of 4 failure modes
- Part 4: Audit-first checklist for existing code
- Part 5: Implementation order
- Part 8: Final verification before declaring proof complete

**In QUICK_AUDIT_GUIDE.md:**
- For each lemma: "Verification Questions" checklist
- For each lemma: "Red Flags" to watch for
- Summary table to record status

**In CODE_SEARCH_CHECKLIST.md:**
- For each lemma: Search terms and expected signatures
- Search strategies in PowerShell
- Summary table to record what you found

---

## The Proof in Context

These documents define exactly what must be proven to establish:

**Theorem:** The Collatz conjecture is true (every positive integer reaches 1)

**Method:** Finite-state descent via DP-certified 64-window contraction

**Key claim:** The 64-window valuation bound is uniform (applies to every odd integer)

**Why this matters:** Once the uniform bound is proven (Lemma 5), the rest is standard descent theory

---

## Version History

- **v1 (Jan 2, 2026):** Refined approach focusing on one core theorem and 7 critical lemmas
- **v0 (Jan 1, 2026):** Earlier 3-part analysis (superseded by this refined version)

---

## Contact & Updates

If you find:
- **Ambiguities** in these documents, clarify in comments
- **Lemmas** already proven in your codebase, update CODE_SEARCH_CHECKLIST.md
- **Implementation gaps**, refer to UNIFIED_PROOF_APPROACH_REFINED.md Part 5 (Implementation Order)

---

**Status:** These documents are the canonical specification. All code should refer back to them.

