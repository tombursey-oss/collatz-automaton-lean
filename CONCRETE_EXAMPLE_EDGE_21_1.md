# Concrete Example: Edge (21,1) with weight 8

This document provides a concrete computational verification showing that the edge
from state (21, branch=1) with r_val=8 does NOT apply to all integers n ≡ 21 (mod 64).

## The Edge in Question

From `src/CollatzAutomaton/Data/ExpandedEdgesV2.lean`, line 35:
```lean
{ src_residue := 21, src_b := 1, dst_residue := 1, dst_b := 0, 
  transition_type := "thick", r_val := 8, branch := "det" }
```

This edge claims:
- Starting from residue 21 (branch 1)
- After Collatz step: (3n+1)/2^8 → residue 1 (branch 0)
- The 2-adic valuation is ν₂(3n+1) = 8

## Testing Different Representatives

Let's test different integers n ≡ 21 (mod 64):

### n = 21
```
3n + 1 = 3(21) + 1 = 64 = 2^6
ν₂(64) = 6 ≠ 8 ❌
```
**Result:** r_val = 6, not 8. Edge does NOT apply to n=21.

### n = 21 + 64 = 85
```
3n + 1 = 3(85) + 1 = 256 = 2^8
ν₂(256) = 8 ✓
(3n+1)/2^8 = 256/256 = 1
```
**Result:** r_val = 8 ✓, destination = 1 ✓. Edge DOES apply to n=85.

### n = 21 + 128 = 149
```
3n + 1 = 3(149) + 1 = 448 = 2^6 × 7 = 64 × 7
ν₂(448) = 6 ≠ 8 ❌
```
**Result:** r_val = 6, not 8. Edge does NOT apply to n=149.

### n = 21 + 192 = 213
```
3n + 1 = 3(213) + 1 = 640 = 2^7 × 5 = 128 × 5
ν₂(640) = 7 ≠ 8 ❌
```
**Result:** r_val = 7, not 8. Edge does NOT apply to n=213.

### n = 21 + 256 = 277
```
3n + 1 = 3(277) + 1 = 832 = 2^6 × 13 = 64 × 13
ν₂(832) = 6 ≠ 8 ❌
```
**Result:** r_val = 6, not 8. Edge does NOT apply to n=277.

### n = 21 + 16384 = 16405
```
3n + 1 = 3(16405) + 1 = 49216 = 2^6 × 769
ν₂(49216) = 6 ≠ 8 ❌
```
**Result:** r_val = 6, not 8. Edge does NOT apply to n=16405.

## Pattern Analysis

The condition ν₂(3n+1) = 8 means:
```
3n + 1 ≡ 0 (mod 2^8)
3n + 1 ≢ 0 (mod 2^9)
```

This is equivalent to:
```
3n ≡ -1 ≡ 255 (mod 256)
3n ≢ 255 (mod 512)
```

Since gcd(3, 256) = 1, we can solve:
```
n ≡ 3^(-1) × 255 (mod 256)
```

Computing 3^(-1) mod 256:
```
3 × 171 = 513 = 256 × 2 + 1 ≡ 1 (mod 256)
```
So 3^(-1) ≡ 171 (mod 256).

Therefore:
```
n ≡ 171 × 255 (mod 256)
n ≡ 43605 (mod 256)
n ≡ 85 (mod 256)
```

**Key Finding:** For ν₂(3n+1) = 8 exactly, we need n ≡ 85 (mod 256), NOT just n ≡ 21 (mod 64).

## Required Precision

The residue classes mod 64 containing n=85:
- 85 mod 64 = 21 ✓
- But also: 21, 21+64=85, 21+128=149, 21+192=213, ...
- Only 85, 85+256=341, 85+512=597, ... have ν₂(3n+1) = 8

**Conclusion:** To distinguish which n ≡ 21 (mod 64) have ν₂(3n+1) = 8, we need:
- n ≡ 85 (mod 256) for ν₂ = 8
- Minimum required precision: **mod 256**

But actually, we also need to check the condition ν₂(3n+1) ≢ 0 (mod 2^9) to ensure exactly 8, not more:

For exactly r = 8, we need:
- 3n + 1 ≡ 0 (mod 2^8)
- 3n + 1 ≢ 0 (mod 2^9)

This gives us two congruence conditions. The second is:
```
3n ≢ -1 (mod 512)
```

Combined, for exactly ν₂(3n+1) = 8:
```
n ≡ 85 (mod 256)  AND  n ≢ 85 + 256 (mod 512)
```

So n can be: 85, 85+512=597, 85+1024=1109, ...

The period is 512, but we need to exclude half of them. The exact characterization is:
```
n ≡ 85 (mod 512) OR n ≡ 341 (mod 512) [need to verify which]
```

Actually, let's verify:
- n = 85: 3×85+1 = 256 = 2^8 ✓ (exactly 8)
- n = 85+256 = 341: 3×341+1 = 1024 = 2^10 ✗ (ν₂ = 10, not 8)
- n = 85+512 = 597: 3×597+1 = 1792 = 2^8 × 7 ✓ (exactly 8)

So the pattern is n ≡ 85 (mod 512).

**For exact invariance of r_val=8, we need mod 512 precision.**

But that's not enough! We also need to verify the destination residue is correct:
```
(3n+1)/2^8 ≡ dst_residue (mod 64)
```

For n = 85:
```
(3×85+1)/2^8 = 256/256 = 1 ≡ 1 (mod 64) ✓
```

For n = 85+512 = 597:
```
(3×597+1)/2^8 = 1792/256 = 7 ≡ 7 (mod 64) ✗
```

So even mod 512 isn't enough! The destination changes.

**To ensure BOTH r_val=8 AND dst_residue=1, we need:**
```
3n + 1 = 256k where k ≡ 1 (mod 64)
```

This means:
```
3n = 256k - 1 where k ≡ 1 (mod 64)
k = 1, 65, 129, 193, ...
3n = 255, 16639, 33023, 49407, ...
n = 85, 5546.33..., ...
```

Wait, k must be such that 256k - 1 is divisible by 3:
- k=1: 255/3 = 85 ✓
- k=65: 16639/3 = 5546.33... ✗
- k=129: 33023/3 = 11007.67... ✗

We need 256k ≡ 1 (mod 3), so k ≡ 1 (mod 3).
And k ≡ 1 (mod 64).

By Chinese Remainder Theorem: k ≡ 1 (mod lcm(3,64)) = 1 (mod 192).

So k = 1, 193, 385, ...
- k=1: n=85
- k=193: 3n = 256×193-1 = 49407, so n = 16469
- k=385: 3n = 256×385-1 = 98559, so n = 32853

Verification:
- n=16469: 16469 mod 64 = 21 ✓, (3×16469+1)/256 = 193, 193 mod 64 = 1 ✓
- n=32853: 32853 mod 64 = 21 ✓, (3×32853+1)/256 = 385, 385 mod 64 = 1 ✓

The period is 256×192/3 = 16384.

**FINAL ANSWER: For exact deterministic edge (21,1)→1 with r_val=8, we need n ≡ 85 (mod 16384).**

## Conclusion

The edge (21, branch=1) → (1, branch=0) with r_val=8 requires **mod 16384 precision**, not mod 64.

This matches the problem statement's calculation: 2^(r+6) = 2^14 = 16384.

The current mod 64 state encoding cannot support exact deterministic semantics for this edge.
