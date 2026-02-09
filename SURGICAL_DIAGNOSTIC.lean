-- SURGICAL DIAGNOSTIC: Is CSV data really indexed by (residue, branch)?
--
-- Question: For a fixed (residue, branch) pair, is the (dst, r_val) always the same?
--
-- Test case: (21, 1) from ExpandedEdgesV2
-- CSV claims: r_val = 8, dst = (1, 0)
--
-- stateOf definition: stateOf(n) = (n % 64, (n / 64) % 2 = 1)
-- For (21, 1): n % 64 = 21 AND (n / 64) % 2 = 1
--   This means: n = 64k + 21 where k is odd
--   i.e., n ≡ 21 (mod 64) AND k ≡ 1 (mod 2)
--   Substituting k = 2m + 1: n = 64(2m+1) + 21 = 128m + 85
--   So S(21,1) = {85, 213, 341, 469, 597, ...} = {n : n ≡ 85 (mod 128), n odd}

namespace Diagnostic

-- Helper: compute 2-adic valuation (highest power of 2 dividing m)
def nu2 : ℕ → ℕ
  | 0 => 0
  | m + 1 => if (m + 1) % 2 = 0 then 1 + nu2 ((m + 1) / 2) else 0

-- Helper: compute oddBlock result
def oddBlock (n : ℕ) : ℕ :=
  let r := nu2 (3 * n + 1)
  (3 * n + 1) / (2 ^ r)

-- Helper: compute branch for a result
def branchOf (n : ℕ) : Bool :=
  (n / 64) % 2 = 1

-- Representative values from S(21, 1) = {n : n ≡ 85 (mod 128)}
-- Test n = 85, 213, 341, 469

example : 85 % 64 = 21 := by decide
example : (85 / 64) % 2 = 1 := by decide
example : nu2 (3 * 85 + 1) = 8 := by decide
example : oddBlock 85 = 1 := by decide
example : branchOf 1 = false := by decide
-- So n=85 gives (dst=1, branch=0, r=8) ✓ Matches CSV

example : 213 % 64 = 21 := by decide
example : (213 / 64) % 2 = 1 := by decide
example : nu2 (3 * 213 + 1) = 7 := by decide  -- NOT 8!
example : oddBlock 213 = 5 := by decide
example : branchOf 5 = false := by decide
-- So n=213 gives (dst=5, branch=0, r=7) ✗ CONTRADICTS CSV!

example : 341 % 64 = 21 := by decide
example : (341 / 64) % 2 = 1 := by decide
example : nu2 (3 * 341 + 1) = 10 := by decide  -- NOT 8!
example : oddBlock 341 = 1 := by decide
example : branchOf 1 = false := by decide
-- So n=341 gives (dst=1, branch=0, r=10) ✗ CONTRADICTS CSV!

example : 469 % 64 = 21 := by decide
example : (469 / 64) % 2 = 1 := by decide
example : nu2 (3 * 469 + 1) = 7 := by decide  -- NOT 8!
example : oddBlock 469 = 11 := by decide
example : branchOf 11 = false := by decide
-- So n=469 gives (dst=11, branch=0, r=7) ✗ CONTRADICTS CSV!

-- CONCLUSION: CSV is NOT indexed by (n % 64, (n / 64) % 2)
-- The valuation r_val varies on S(21,1):
--   n=85:   r=8
--   n=213:  r=7
--   n=341:  r=10
--   n=469:  r=7
--
-- The destination also varies:
--   n=85:   dst=1
--   n=213:  dst=5
--   n=341:  dst=1
--   n=469:  dst=11

-- HYPOTHESIS: CSV is indexed by a finer modulus. Which one?
--
-- Test candidates:
-- - n % 256?
-- - n % 1024?
-- - n % 16384?

-- Check if n % 256 discriminates:
example : 85 % 256 = 85 := by decide
example : 213 % 256 = 213 := by decide
example : 341 % 256 = 85 := by decide  -- 341 ≡ 85 (mod 256)!
example : 469 % 256 = 213 := by decide -- 469 ≡ 213 (mod 256)!

-- So the 256-cycle repeats with period 256.
-- Let's check 256-values within [1, 255]:

-- Class 0: n ≡ 21 (mod 256) with (n/64)%2=1
--   n = 21 is not in this form (21 < 64)
--   n = 21 + 256*0 = 21: (21/64)%2 = 0, not 1
--   n = 21 + 256*1 = 277: (277/64)%2 = 4%2 = 0, not 1
--   n = 21 + 256*2 = 533: (533/64)%2 = 8%2 = 0, not 1
-- Hmm, that's not matching. Let me recalculate.

-- Actually, for the class (21, 1):
-- n ≡ 21 (mod 64) and (n / 64) % 2 = 1
-- This gives n = 64(2k+1) + 21 = 128k + 85 for k ≥ 0
-- So within mod 256: {85, 85+128} = {85, 213}
-- Within mod 512: {85, 213, 85+256, 213+256} = {85, 213, 341, 469}
-- So mod 256 gives exactly two classes from (21, 1): {85, 213}

-- And we already saw:
-- - 85 → (1, 0, 8)
-- - 213 → (5, 0, 7)
--
-- So even mod 256 doesn't make it constant!

-- Let's try computing what modulus WOULD make this constant.
-- For it to be constant on the equivalence class, all n ≡ a (mod M)
-- would need the same oddBlock result.

-- But we have n=85 and n=341 both ≡ 21 (mod 64) with (n/64)%2=1,
-- yet:
--   oddBlock(85) = 1
--   oddBlock(341) = 1 ✓ Both land on 1
-- But their r-valuations differ: r(85)=8, r(341)=10.
--
-- So EVEN IF the destination is constant on (residue, branch),
-- the r-value is NOT constant!

-- This means the CSV cannot be indexed by (residue, branch) at all,
-- because the edge weight varies.

-- CRITICAL REALIZATION:
-- The CSV row (src_residue=21, src_b=1) → (dst_residue=1, dst_b=0, r_val=8)
-- is NOT a function of just (21, 1).
--
-- It must represent a SINGLE residue class modulo a LARGER modulus,
-- or it's encoding additional information not visible in (residue, branch).

end Diagnostic
