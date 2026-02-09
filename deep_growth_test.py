#!/usr/bin/env python3
"""
Very deep diagnostic on (21,1) with 1000 representatives to see if modulus keeps growing.
"""

from math import gcd

def nu2(m):
    if m == 0:
        return 0
    count = 0
    while m % 2 == 0:
        count += 1
        m //= 2
    return count

def oddBlock(n):
    if n % 2 == 0:
        return None
    val = nu2(3 * n + 1)
    return (3 * n + 1) // (2 ** val)

def get_arithmetic_signature(n):
    if n % 2 == 0:
        return None
    r = nu2(3 * n + 1)
    dst = oddBlock(n)
    dst_residue = dst % 64
    dst_branch = (dst // 64) % 2
    return (r, dst_residue, dst_branch)

def test_with_sample_sizes():
    """Test (21,1) with increasing sample sizes to see if modulus grows."""
    residue, branch = 21, 1
    start = 64 * (2 * 0 + branch) + residue  # = 64*1 + 21 = 85
    
    sample_sizes = [30, 100, 300, 1000]
    
    print("Testing (21,1) with increasing sample sizes:")
    print()
    print(f"Sample Size | Min Modulus Required")
    print("-" * 40)
    
    for sample_size in sample_sizes:
        representatives = [start + 128 * i for i in range(sample_size)]
        all_sigs = [get_arithmetic_signature(n) for n in representatives]
        
        # Find minimum modulus
        for exp in range(6, 30):
            modulus = 2 ** exp
            sigs_by_residue = {}
            
            for n, sig in zip(representatives, all_sigs):
                n_mod = n % modulus
                if n_mod not in sigs_by_residue:
                    sigs_by_residue[n_mod] = set()
                sigs_by_residue[n_mod].add(sig)
            
            is_consistent = all(len(s) == 1 for s in sigs_by_residue.values())
            
            if is_consistent:
                bits = exp
                print(f"{sample_size:>11} | 2^{bits:>2} ({modulus:>10,})")
                break
        else:
            print(f"{sample_size:>11} | > 2^29 (NOT FOUND)")

if __name__ == '__main__':
    test_with_sample_sizes()
