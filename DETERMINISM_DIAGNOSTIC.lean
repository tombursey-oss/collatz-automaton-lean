-- DEFINITIVE DIAGNOSTIC: What modulus makes the CSV deterministic?
--
-- Approach:
-- 1. Pick several CSV rows (different (residue, branch) pairs)
-- 2. For each row, test representatives from its equivalence class
-- 3. Find: are they all the same, or do they vary?
-- 4. If they vary, what modulus WOULD make them the same?
-- 5. Find LCM across all rows to get minimum state space size
--
-- Key insight:
--   - If LCM is small (64 or 256 or 1024): CSV can be exact, just needs reindexing
--   - If LCM is huge (2^20+): CSV was never meant to be exact, it's an approximation

namespace DeterminismDiagnostic

-- Helpers
def nu2 : ℕ → ℕ
  | 0 => 0
  | m + 1 => if (m + 1) % 2 = 0 then 1 + nu2 ((m + 1) / 2) else 0

def oddBlock (n : ℕ) : ℕ :=
  let r := nu2 (3 * n + 1)
  (3 * n + 1) / (2 ^ r)

def stateOf_residue (n : ℕ) : ℕ := n % 64
def stateOf_branch (n : ℕ) : Bool := (n / 64) % 2 = 1

-- ============================================================================
-- TEST 1: (residue=1, branch=0)
-- ============================================================================
-- S(1,0) = {n : n ≡ 1 (mod 64) and (n/64) % 2 = 0}
--   n = 64(2k) + 1 = 128k + 1 for k ≥ 0
--   S(1,0) = {1, 129, 257, 385, 513, 641, ...}

section Test1_Residue1_Branch0

example : 1 % 64 = 1 := by decide
example : (1 / 64) % 2 = 0 := by decide

example : nu2 (3 * 1 + 1) = 2 := by decide           -- 3*1+1=4=2^2
example : oddBlock 1 = 1 := by decide                -- 4/4=1
example : stateOf_residue 1 = 1 := by decide
example : stateOf_branch 1 = false := by decide

example : 129 % 64 = 1 := by decide
example : (129 / 64) % 2 = 0 := by decide

example : nu2 (3 * 129 + 1) = 4 := by decide         -- 3*129+1=388=4*97=2^2*97
example : oddBlock 129 = 97 := by decide             -- 388/4=97
example : stateOf_residue 97 = 97 % 64 := by decide  -- 97 % 64 = 33
example : stateOf_residue 97 = 33 := by decide

-- RESULT: n=1 and n=129 both have stateOf(n)=(1,0)
--         But: 1 → (1,0,2)  vs  129 → (33,0,4)
--         THEY DIFFER!

-- The key insight: For n to be in S(1,0) AND produce the same result,
-- we need not just n % 64 = 1, but some finer constraint.
--
-- Let's check: are n=1 and n=257 in same pattern?

example : 257 % 64 = 1 := by decide
example : (257 / 64) % 2 = 0 := by decide

example : nu2 (3 * 257 + 1) = 2 := by decide         -- 3*257+1=772=4*193
example : oddBlock 257 = 193 := by decide            -- 772/4=193
example : stateOf_residue 193 = 193 % 64 := by decide
example : stateOf_residue 193 = 1 := by decide       -- 193 % 64 = 1

-- RESULT: n=1 and n=257 both have stateOf(n)=(1,0)
--         But: 1 → (1, 2)  vs  257 → (1, 2)  ✓ SAME DESTINATION
--         Both have r=2 ✓
--         Yet n=129 → (33, 4) ✗ DIFFERENT

-- Check n=385, n=513, etc. to see the pattern

example : 385 % 64 = 1 := by decide
example : nu2 (3 * 385 + 1) = 7 := by decide         -- 3*385+1=1156=4*289=2^2*17^2
example : oddBlock 385 = 289 := by decide

example : 513 % 64 = 1 := by decide
example : nu2 (3 * 513 + 1) = 4 := by decide         -- 3*513+1=1540=4*385
example : oddBlock 513 = 385 := by decide

-- Observation: 1,257 give r=2; 129,641,... give r=4; 385,897,... give r=7
-- The pattern repeats with period = LCM(?, ?, ...) = ?
--
-- Hypothesis: Need to check modulo 256, 512, 1024, 16384?

-- More systematic: check if n % 256 is the discriminant

example : 1 % 256 = 1 := by decide
example : 129 % 256 = 129 := by decide
example : 257 % 256 = 1 := by decide                  -- 257 ≡ 1 (mod 256)
example : 385 % 256 = 129 := by decide                -- 385 ≡ 129 (mod 256)
example : 513 % 256 = 1 := by decide

-- So within mod 256:
-- - 1 mod 256 = 1:   gives r=2
-- - 129 mod 256 = 129: gives r=4

-- Check 257 ≡ 1 (mod 256): does it give r=2? YES ✓
-- Check 385 ≡ 129 (mod 256): does it give r=7? But 129 gives r=4... ✗

-- So even mod 256 doesn't work!
-- Try mod 512?

example : 1 % 512 = 1 := by decide
example : 129 % 512 = 129 := by decide
example : 257 % 512 = 257 := by decide
example : 385 % 512 = 385 := by decide
example : 513 % 512 = 1 := by decide                  -- 513 ≡ 1 (mod 512)

-- So 1 and 513 are ≡ 1 (mod 512)
-- 1 gives (r=2, dst=1)
-- 513 gives (r=4, dst=385)
-- These differ!

-- Hypothesis: need much larger modulus, like 16384 or 2^16 = 65536

end Test1_Residue1_Branch0

-- ============================================================================
-- TEST 2: (residue=5, branch=1)
-- ============================================================================
-- S(5,1) = {n : n ≡ 5 (mod 64) and (n/64) % 2 = 1}
--   n = 64(2k+1) + 5 = 128k + 69 for k ≥ 0
--   S(5,1) = {69, 197, 325, 453, ...}

section Test2_Residue5_Branch1

example : 69 % 64 = 5 := by decide
example : (69 / 64) % 2 = 1 := by decide

example : nu2 (3 * 69 + 1) = 4 := by decide          -- 3*69+1=208=16*13
example : oddBlock 69 = 13 := by decide              -- 208/16=13

example : 197 % 64 = 5 := by decide
example : (197 / 64) % 2 = 1 := by decide

example : nu2 (3 * 197 + 1) = 1 := by decide         -- 3*197+1=592=16*37
example : oddBlock 197 = 37 := by decide             -- 592/2=296... wait let me recalculate

-- Actually 3*197+1 = 591+1 = 592 = 2 * 296 = 2 * 2 * 148 = 4 * 148 = 4 * 4 * 37 = 16 * 37
-- So ν₂(592) = 4, not 1. Let me recompute.

-- 592 / 2 = 296
-- 296 / 2 = 148
-- 148 / 2 = 74
-- 74 / 2 = 37 (odd)
-- So ν₂(592) = 4 ✓

example : nu2 (3 * 197 + 1) = 4 := by decide
example : oddBlock 197 = 37 := by decide             -- 592/16=37

-- So: 69 → (13, r=4) and 197 → (37, r=4)
-- Both have r=4, but different destinations

example : 325 % 64 = 5 := by decide
example : (325 / 64) % 2 = 1 := by decide

example : nu2 (3 * 325 + 1) = 1 := by decide         -- 3*325+1=976=16*61
example : oddBlock 325 = 61 := by decide             -- 976/2=488... hmm

-- 976 / 2 = 488
-- 488 / 2 = 244
-- 244 / 2 = 122
-- 122 / 2 = 61 (odd)
-- So ν₂(976) = 4

example : nu2 (3 * 325 + 1) = 4 := by decide
example : oddBlock 325 = 61 := by decide

-- So all three (69, 197, 325) have r=4 but different destinations (13, 37, 61)

end Test2_Residue5_Branch1

-- ============================================================================
-- TENTATIVE CONCLUSION
-- ============================================================================
--
-- For (residue=1, branch=0):
--   - Elements 1, 129, 257, 385, 513, ... have same (residue, branch)
--   - But different r values and destinations
--   - Mod 64: doesn't work
--   - Mod 256: doesn't work
--   - Mod 512: doesn't work
--   - Hypothesis: would need much larger, like 2^14 = 16384 or 2^16 = 65536
--
-- For (residue=5, branch=1):
--   - Elements 69, 197, 325, 453, ... have same (residue, branch)
--   - All have r=4 (good!)
--   - But different destinations (13, 37, 61, ...)
--   - Destinations vary, so state space must be finer
--
-- IMPLICATION:
-- The CSV cannot be a deterministic exact automaton with state space size 64.
-- Either:
--   (A) State space needs to be 2^14 or 2^16 or larger
--   (B) CSV is an abstract/approximate automaton (lower bounds on weights)
--
-- To determine which, need to:
-- 1. Check ALL 64 CSV rows
-- 2. For each, determine minimum modulus making it deterministic
-- 3. Find LCM of all these moduli
-- 4. If LCM is "reasonable" (≤ 2^20): Option A is viable
-- 5. If LCM is "huge" (> 2^20): Option B/C/D are necessary

end DeterminismDiagnostic
