#!/usr/bin/env python3
"""
Generate Lean proof lines for basin verification rows.

For each (n, stopping_time_steps) in basin_verification_v2.csv,
output a Lean line:
  have h_<n> : iterate_k <stopping_time_steps> <n> = 1 := by decide

These can be inserted into MainTheorem.lean to discharge the
basin_rows_reach_1_data lemma.
"""

# Basin verification data from basin_verification_v2.csv
basin_data = [
    (1, 0),
    (3, 7),
    (5, 5),
    (7, 16),
    (9, 19),
    (11, 14),
    (13, 9),
    (15, 17),
    (17, 12),
    (19, 20),
    (21, 7),
    (23, 15),
    (25, 23),
    (27, 111),
    (29, 18),
    (31, 106),
    (33, 26),
    (35, 13),
    (37, 21),
    (39, 34),
    (41, 109),
    (43, 29),
    (45, 16),
    (47, 104),
    (49, 24),
    (51, 24),
    (53, 11),
    (55, 112),
    (57, 32),
    (59, 32),
    (61, 19),
    (63, 107),
]

def generate_proofs():
    """Generate Lean proof lines for each basin row."""
    print("-- Auto-generated proof lines for basin_rows_reach_1_data")
    print("-- Insert these into the `intro r hr` case in MainTheorem.lean")
    print()
    
    for n, k in basin_data:
        print(f"  have h_{n} : iterate_k {k} {n} = 1 := by decide")
    
    print()
    print("-- Or using `decide` tactic on the entire case split:")
    print("-- (after intro r hr, you can also use 'decide' directly if cases are decidable)")
    print()
    print("-- Aggregate proof using the cases:")
    for idx, (n, k) in enumerate(basin_data):
        print(f"  | case cons h_{idx} => simp [basinVerificationV2] at h_{idx}; decide")

if __name__ == "__main__":
    generate_proofs()
