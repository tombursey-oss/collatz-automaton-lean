#!/usr/bin/env python3
"""
Extended Determinism Diagnostic: Deep analysis of worst-case rows 21 and 53.

Tests with 100+ representatives to see if required modulus grows beyond 2^12.
"""

from math import gcd
from functools import reduce

def lcm(a, b):
    """Least common multiple"""
    return abs(a * b) // gcd(a, b)

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
        return None
    val = nu2(3 * n + 1)
    return (3 * n + 1) // (2 ** val)

def stateOf(n):
    """Current state encoding: (n % 64, (n // 64) % 2)"""
    return (n % 64, (n // 64) % 2)

def find_representatives(residue, branch, num_representatives=100):
    """
    Find representatives of S(residue, branch).
    S(r,b) = {n : n % 64 = r and (n // 64) % 2 = b}
    """
    start = 64 * (2 * 0 + branch) + residue
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

def find_min_modulus_extended(residue, branch, num_reps=100, max_modulus=2**24):
    """
    Find minimum modulus M such that all representatives with same n % M
    have the same arithmetic signature.
    
    Tests with num_reps representatives and up to max_modulus.
    Returns: (min_modulus, tested_up_to, growth_pattern)
    """
    representatives = find_representatives(residue, branch, num_representatives=num_reps)
    
    # Collect all signatures
    all_sigs = [get_arithmetic_signature(n) for n in representatives]
    
    # Test moduli from small to large
    modulus_progression = []
    
    for exp in range(6, 25):  # 2^6 to 2^24
        modulus = 2 ** exp
        if modulus > max_modulus:
            break
        
        # Group by residue mod this modulus
        sigs_by_residue_mod = {}
        for n, sig in zip(representatives, all_sigs):
            n_mod_m = n % modulus
            if n_mod_m not in sigs_by_residue_mod:
                sigs_by_residue_mod[n_mod_m] = set()
            sigs_by_residue_mod[n_mod_m].add(sig)
        
        # Check if deterministic
        is_consistent = all(len(sigs) == 1 for sigs in sigs_by_residue_mod.values())
        
        modulus_progression.append({
            'exp': exp,
            'modulus': modulus,
            'is_deterministic': is_consistent,
            'num_distinct_signatures': len(set(all_sigs))
        })
        
        if is_consistent:
            return (modulus, modulus, modulus_progression)
    
    # If we got here, even 2^24 didn't work
    return (None, max_modulus, modulus_progression)

def main():
    print("=" * 100)
    print("EXTENDED DETERMINISM DIAGNOSTIC: Worst-case rows 21 and 53")
    print("=" * 100)
    print()
    
    worst_cases = [(21, 0), (21, 1), (53, 0), (53, 1)]
    
    for residue, branch in worst_cases:
        print(f"\n{'=' * 100}")
        print(f"Testing ({residue:2d}, {branch}) with 100 representatives")
        print(f"{'=' * 100}")
        print()
        
        min_mod, tested_up_to, progression = find_min_modulus_extended(residue, branch, num_reps=100)
        
        print(f"Modulus progression for ({residue}, {branch}):")
        print()
        print(f"{'Exp':>4} | {'Modulus':>12} | Status")
        print("-" * 35)
        
        for p in progression:
            status = "✓ DETERMINISTIC" if p['is_deterministic'] else "✗ Non-deterministic"
            print(f"{p['exp']:>4} | {p['modulus']:>12,} | {status}")
        
        print()
        if min_mod:
            bits = min_mod.bit_length() - 1
            print(f"✓ DETERMINISTIC at: 2^{bits} = {min_mod:,}")
        else:
            print(f"✗ NOT DETERMINISTIC even at 2^24 = {tested_up_to:,}")
            print(f"   This suggests a fundamental architectural issue, not just insufficient modulus.")
        print()

if __name__ == '__main__':
    main()
