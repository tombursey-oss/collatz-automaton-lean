#!/usr/bin/env python3
"""
Determinism diagnostic: For each CSV row, find minimum modulus for determinism.

This script:
1. For each (residue, branch) pair in [0,63] x [0,1]
2. Enumerates representatives from its equivalence class
3. Computes their arithmetic (r-value, destination)
4. Finds minimum modulus M such that n % M uniquely determines (r, dst)
5. Computes LCM of all minimum moduli
6. Outputs table and recommendation
"""

from math import gcd
from functools import reduce

def lcm(a, b):
    """Least common multiple"""
    return abs(a * b) // gcd(a, b)

def lcm_list(lst):
    """LCM of a list"""
    return reduce(lcm, lst, 1)

def nu2(m):
    """2-adic valuation: highest power of 2 dividing m"""
    if m == 0:
        return 0
    count = 0
    while m % 2 == 0:
        count += 1
        m //= 2
    return count

def oddBlock(n):
    """Collatz oddBlock: (3n+1) / 2^{ν₂(3n+1)}"""
    if n % 2 == 0:
        return None  # Only defined for odd n
    val = nu2(3 * n + 1)
    return (3 * n + 1) // (2 ** val)

def stateOf(n):
    """Current state encoding: (n % 64, (n // 64) % 2)"""
    return (n % 64, (n // 64) % 2)

def find_representatives(residue, branch, num_representatives=20):
    """
    Find representatives of the equivalence class S(residue, branch).
    
    S(r,b) = {n : n % 64 = r and (n // 64) % 2 = b}
    These are: n = 64(2k + b) + r = 128k + (64b + r)
    """
    start = 64 * (2 * 0 + branch) + residue  # First element
    representatives = [start + 128 * i for i in range(num_representatives)]
    return representatives

def get_arithmetic_signature(n):
    """For an odd n, get (r-value, destination residue, destination branch)"""
    if n % 2 == 0:
        return None
    
    r = nu2(3 * n + 1)
    dst = oddBlock(n)
    dst_residue = dst % 64
    dst_branch = (dst // 64) % 2
    
    return (r, dst_residue, dst_branch)

def find_min_modulus(residue, branch, max_modulus=2**20):
    """
    Find minimum modulus M such that all representatives with same n % M
    have the same arithmetic signature.
    
    Returns: (is_deterministic, min_modulus)
    where is_deterministic = True if M <= 64, False if M > 64
    """
    representatives = find_representatives(residue, branch, num_representatives=30)
    
    # Get signatures for all representatives
    signatures_by_residue = {}
    for n in representatives:
        sig = get_arithmetic_signature(n)
        n_mod_64 = n % 64
        if n_mod_64 not in signatures_by_residue:
            signatures_by_residue[n_mod_64] = []
        signatures_by_residue[n_mod_64].append(sig)
    
    # Check if mod 64 is deterministic
    is_consistent_mod64 = all(len(sigs) == 0 or len(set(sigs)) == 1 
                               for sigs in signatures_by_residue.values())
    
    if is_consistent_mod64:
        return (True, 64)
    
    # Try larger moduli
    for exp in range(7, 21):  # 2^7 = 128 to 2^20 = 1048576
        modulus = 2 ** exp
        signatures_by_residue_mod = {}
        
        for n in representatives:
            sig = get_arithmetic_signature(n)
            n_mod_m = n % modulus
            if n_mod_m not in signatures_by_residue_mod:
                signatures_by_residue_mod[n_mod_m] = set()
            signatures_by_residue_mod[n_mod_m].add(sig)
        
        # Check if this modulus is deterministic
        is_consistent = all(len(sigs) == 1 for sigs in signatures_by_residue_mod.values())
        
        if is_consistent:
            return (False, modulus)
    
    # If even 2^20 doesn't work, mark as problematic
    return (False, 2**20 + 1)

def main():
    print("=" * 100)
    print("DETERMINISM DIAGNOSTIC: Computing minimum state space size")
    print("=" * 100)
    print()
    
    results = []
    min_moduli = []
    
    for residue in range(64):
        for branch in range(2):
            print(f"Testing ({residue:2d}, {branch})...", end=" ", flush=True)
            
            is_det, min_mod = find_min_modulus(residue, branch)
            
            # Verify by testing some representatives
            reps = find_representatives(residue, branch, 10)
            sigs = [get_arithmetic_signature(n) for n in reps]
            
            # Check consistency at min_mod
            sigs_by_residue = {}
            for n, sig in zip(reps, sigs):
                n_mod = n % min_mod
                if n_mod not in sigs_by_residue:
                    sigs_by_residue[n_mod] = set()
                sigs_by_residue[n_mod].add(sig)
            
            all_consistent = all(len(s) == 1 for s in sigs_by_residue.values())
            
            status = "✓ CONSISTENT" if is_det else "✗ NEEDS LARGER MODULUS"
            print(f"{status:30s} min_mod = 2^{min_mod.bit_length()-1:2d} ({min_mod:8d})")
            
            results.append({
                'residue': residue,
                'branch': branch,
                'is_deterministic': is_det,
                'min_modulus': min_mod
            })
            
            if not is_det:  # Only track non-64 moduli
                min_moduli.append(min_mod)
    
    print()
    print("=" * 100)
    print("SUMMARY")
    print("=" * 100)
    print()
    
    # Count results
    consistent_64 = sum(1 for r in results if r['is_deterministic'])
    inconsistent = sum(1 for r in results if not r['is_deterministic'])
    
    print(f"Rows consistent with mod 64:        {consistent_64:3d} / 64")
    print(f"Rows requiring larger modulus:      {inconsistent:3d} / 64")
    print()
    
    if inconsistent == 0:
        print("✓ All rows are deterministic with mod 64!")
        print("  This suggests the CSV indexing is fundamentally incompatible with (residue, branch).")
        print("  The issue is not a missing modulus, but a different problem.")
    else:
        # Find LCM
        lcm_value = lcm_list(min_moduli)
        lcm_bits = lcm_value.bit_length()
        
        print(f"LCM of all min moduli:              2^{lcm_bits-1} = {lcm_value:,}")
        print()
        
        # Recommendation
        if lcm_value <= 2**16:
            print("✓ OPTION A (Refine state space) is VIABLE")
            print(f"  The state space needs only 2^{lcm_bits-1} ({lcm_value:,} states)")
            print("  This is manageable. Estimate: ~1 week to regenerate CSV and reprove.")
        elif lcm_value <= 2**20:
            print("⚠ OPTION A (Refine state space) is MARGINALLY VIABLE")
            print(f"  The state space needs 2^{lcm_bits-1} ({lcm_value:,} states)")
            print("  This is large but still finite. Estimate: ~2 weeks (data generation overhead)")
        else:
            print("✗ OPTION A (Refine state space) is NOT VIABLE")
            print(f"  The state space would need 2^{lcm_bits-1} ({lcm_value:,} states)")
            print("  This suggests the CSV is meant to be approximate, not exact.")
            print("  Proceed with OPTION B (bounds) or OPTION C (DP lower bounds).")
    
    print()
    print("=" * 100)
    print("DETAILED RESULTS BY MIN_MODULUS")
    print("=" * 100)
    print()
    
    # Group by min_modulus
    from collections import defaultdict
    by_mod = defaultdict(list)
    for r in results:
        by_mod[r['min_modulus']].append((r['residue'], r['branch']))
    
    for mod in sorted(by_mod.keys()):
        pairs = by_mod[mod]
        mod_bits = mod.bit_length() - 1 if mod > 64 else 6
        print(f"Min modulus 2^{mod_bits:2d} ({mod:8d}): {len(pairs):2d} rows")
        if len(pairs) <= 16:
            print(f"  Pairs: {pairs}")
    
    print()

if __name__ == '__main__':
    main()
