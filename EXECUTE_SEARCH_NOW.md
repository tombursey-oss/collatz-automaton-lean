# ACTION NOW: Search Your Codebase for Lemmas 3 and 4
**Status:** Executable Search Guide  
**Date:** January 2, 2026

---

## Your Mission (15 minutes)

Find whether **Lemma 3** and **Lemma 4** exist in your code.

If both exist and are correct → **Proof is essentially done.**

---

## LEMMA 3: Look for This Pattern

```
weight_sum = ∑ r_val(...)
```

### Copy-paste this search command:

```powershell
Get-ChildItem c:\collatz_automaton\src -Include "*.lean" -Recurse | 
  Select-String "weight_sum\s*=" | 
  Select-String "r_val|valuation" | 
  Select-Object Filename, LineNumber, Line | 
  Format-Table -AutoSize
```

### What You're Looking For

When you run it, you should see output like:

```
Filename: C:\collatz_automaton\src\CollatzAutomaton\Lemma9_BasinCapture.lean
LineNumber: 142
Line: lemma path_weight_equals_valuation (n : OddNat) :
        (trajectory_to_path n).weight_sum = (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum := sorry
```

### ✅ If You Find It

**Record:**
- File: ___________________
- Line number: ___________________
- Lemma name: ___________________

**Then check:**
- Is it exactly `weight_sum =` (equality, not `≥` or `≤`)?  
  ☐ Yes ☐ No ☐ Not sure
- Does it sum `r_val (iterateOddStep i n)` for 64 steps?  
  ☐ Yes ☐ No ☐ Not sure

**If both YES:** Lemma 3 is ✅ FOUND

### ❌ If You Don't Find It

**Try these backup searches:**

```powershell
# Search for any lemma mentioning path and weight and r_val
Get-ChildItem c:\collatz_automaton\src -Include "*.lean" -Recurse | 
  Select-String "lemma.*weight" | 
  Select-String "r_val"

# Search for trajectory_to_path definition and usage
Get-ChildItem c:\collatz_automaton\src -Include "*.lean" -Recurse | 
  Select-String "trajectory_to_path"

# Search for path lifting (different naming)
Get-ChildItem c:\collatz_automaton\src -Include "*.lean" -Recurse | 
  Select-String "lift_path|path_lift|path_of_integer"
```

**If still not found:** Lemma 3 needs to be implemented.

---

## LEMMA 4: Look for This Pattern

```
∀ p : PathLen 64, weight_sum ≥ R_min
```

### Copy-paste this search command:

```powershell
Get-ChildItem c:\collatz_automaton\src -Include "*.lean" -Recurse | 
  Select-String "weight_sum.*≥.*R_min|R_min.*≥.*weight" | 
  Select-Object Filename, LineNumber, Line | 
  Format-Table -AutoSize
```

### What You're Looking For

When you run it, you should see output like:

```
Filename: C:\collatz_automaton\src\CollatzAutomaton\Lemma9_BasinCapture.lean
LineNumber: 287
Line: lemma dp_global_descent (p : PathLen 64) :
        p.weight_sum ≥ R_min := sorry
```

OR

```
Line: lemma every_path_min_weight : ∀ p : PathLen 64, p.weight_sum ≥ R_min := sorry
```

### ✅ If You Find It

**Record:**
- File: ___________________
- Line number: ___________________
- Lemma name: ___________________

**Then check:**
- Is it quantified over ALL paths (not a subset)?  
  ☐ Yes ☐ No ☐ Unsure
- Does it claim `weight_sum ≥ R_min` (not reversed)?  
  ☐ Yes ☐ No ☐ Unsure
- Is R_min the global minimum (not just a local constant)?  
  ☐ Yes ☐ No ☐ Unsure

**If all YES:** Lemma 4 is ✅ FOUND

### ❌ If You Don't Find It

**Try these backup searches:**

```powershell
# Search for R_min definition
Get-ChildItem c:\collatz_automaton\src -Include "*.lean" -Recurse | 
  Select-String "R_min|Rmin" | 
  Select-String "def|:=" | 
  Head -20

# Search for dp_global or similar
Get-ChildItem c:\collatz_automaton\src -Include "*.lean" -Recurse | 
  Select-String "dp_global|global_descent|global_bound"

# Search for all paths with weight bound
Get-ChildItem c:\collatz_automaton\src -Include "*.lean" -Recurse | 
  Select-String "∀.*Path|forall.*path" | 
  Select-String "weight_sum"
```

**If still not found:** Lemma 4 needs to be implemented.

---

## Result Checklist

After running both searches, fill this in:

### Lemma 3 Status
- [ ] **Found**: Lemma name is ___________________
- [ ] **Location**: File _________________ Line _______
- [ ] **Pattern verified**: `weight_sum = ∑ r_val(...)`
- [ ] **Confidence**: High / Medium / Low

### Lemma 4 Status
- [ ] **Found**: Lemma name is ___________________
- [ ] **Location**: File _________________ Line _______
- [ ] **Pattern verified**: `∀ p : PathLen 64, weight_sum ≥ R_min`
- [ ] **Confidence**: High / Medium / Low

### Next Steps

**If both are found and verified:**
- [ ] Record results in CODE_SEARCH_CHECKLIST.md
- [ ] Run QUICK_AUDIT_GUIDE.md on both lemmas
- [ ] If both pass audit → Implement Lemmas 5–7 (mechanical, 1–2 days)

**If only Lemma 3 is found:**
- [ ] Mark Lemma 4 as CRITICAL MISSING in CODE_SEARCH_CHECKLIST.md
- [ ] Implement Lemma 4 using UNIFIED_PROOF_APPROACH_REFINED.md Part 2

**If only Lemma 4 is found:**
- [ ] Mark Lemma 3 as CRITICAL MISSING in CODE_SEARCH_CHECKLIST.md
- [ ] Implement Lemma 3 using UNIFIED_PROOF_APPROACH_REFINED.md Part 2

**If neither is found:**
- [ ] Both are CRITICAL MISSING
- [ ] Implement both (Lemma 3 typically easier; do it first)
- [ ] Then implement Lemmas 5–7

---

## Quick Interpretation Guide

### Lemma 3 Search Results

| Result | Interpretation | Action |
|--------|-----------------|--------|
| Find `weight_sum = ∑ r_val(...)` | Exact match | ✅ LEMMA 3 FOUND |
| Find `weight_sum ≥ ∑ r_val(...)` | Inequality (too weak) | ❌ Wrong lemma, keep searching |
| Find `∑ r_val(...) ≥ weight_sum` | Backwards (wrong) | ❌ Wrong direction, keep searching |
| Find nothing with weight_sum | Lemma doesn't exist | ❌ LEMMA 3 MISSING, implement |

### Lemma 4 Search Results

| Result | Interpretation | Action |
|--------|-----------------|--------|
| Find `∀ p, weight_sum ≥ R_min` | Exact match | ✅ LEMMA 4 FOUND |
| Find `∃ p, weight_sum ≥ R_min` | Existence (too weak) | ❌ Wrong lemma, keep searching |
| Find `weight_sum ≤ R_min` | Reversed inequality | ❌ Wrong direction, keep searching |
| Find `∀ v, minPath(v) ≥ R_min` | About vertices, not paths | ❌ Wrong focus, keep searching |
| Find nothing with R_min | Lemma doesn't exist | ❌ LEMMA 4 MISSING, implement |

---

## Copy-Paste One-Liner (Both Searches)

```powershell
Write-Host "=== SEARCHING LEMMA 3 ==="; Get-ChildItem c:\collatz_automaton\src -Include "*.lean" -Recurse | Select-String "weight_sum\s*=" | Select-String "r_val"; Write-Host "`n=== SEARCHING LEMMA 4 ==="; Get-ChildItem c:\collatz_automaton\src -Include "*.lean" -Recurse | Select-String "weight_sum.*≥" | Select-String "R_min|PathLen"
```

Run this in PowerShell and you'll get results for both lemmas instantly.

---

## What to Do With Results

1. **Copy the output** from the search
2. **Paste it into** the summary section below
3. **Fill in the Status table** at the end of this document

---

## Search Results (Fill in After Running Commands)

### Lemma 3 Search Output:
```
[PASTE HERE]
```

### Lemma 4 Search Output:
```
[PASTE HERE]
```

---

## Final Summary

| Lemma | Status | File | Line | Next Action |
|-------|--------|------|------|------------|
| 3 | ☐ Found ☐ Missing | | | |
| 4 | ☐ Found ☐ Missing | | | |

**If both found:** Update CODE_SEARCH_CHECKLIST.md and run QUICK_AUDIT_GUIDE.md

**If either missing:** Refer to UNIFIED_PROOF_APPROACH_REFINED.md Part 2 to implement

---

**Time estimate:** 15 minutes to search + interpret

**Expected outcome:** Clear understanding of what critical lemmas exist vs. need implementation

**Critical insight:** If both are found and correct, the proof is essentially complete. Everything else is mechanical.

