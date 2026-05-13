# Index
<!-- One line per file. Update line numbers when the file changes. -->

- `MordellArchon/Basic.lean`: 6 sorries to fill. Priority: mordell_minus1_solution_iff (line 27) → mordell_minus2_solutions_iff (line 31) → mordell_minus5 (line 39) → mordell_minus6 (line 43). Defer mordell_d (line 18) and mordell_minus13_solutions_iff (line 35).

## Key Context
- **Method**: Factor in quadratic integer rings (GaussianInt for d=-1, Zsqrtd for d=-2)
- **Key lemma**: `exists_associated_pow_of_mul_eq_pow` in `Mathlib.Algebra.GCDMonoid.Basic` — coprime product = k-th power → each factor is associated to a k-th power
- **GaussianInt**: EuclideanDomain instance exists — well-supported
- **Zsqrtd (-2)**: May lack EuclideanDomain instance — prover may need to build it
- **Non-UFD cases (d=-5,-6,-13)**: Very hard, infrastructure likely insufficient
- **Previous iterations**: iter-001 and iter-002 produced no task_results — no prior work to build on
- **See PROGRESS.md for full informal proof sketches**
---
