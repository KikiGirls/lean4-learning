/-
# Maximizing the number of permutations of a given order

## Problem

Let `f_k(n)` count the number of elements of `S_n` (the symmetric group on `n` elements)
of order `k`. For which values of `k` will `f_k(n)` be maximal?

## Answer

For `n ≥ 3`, the value `k = 2` maximizes `f_k(n)`. That is, **involutions**
(permutations that are products of disjoint transpositions) are the most numerous
among all permutations of any fixed order in `S_n`.

Recall that a permutation has order 2 if and only if every cycle in its cycle
decomposition has length 1 or 2, and at least one cycle has length 2.

The number of involutions in `S_n` satisfies the recurrence
  `a(n) = a(n-1) + (n-1) · a(n-2)`
and grows asymptotically as `√(2πn) · (n/e)^(n/2) · e^√n · (2e)^(-1/4)`,
which dominates the count of elements of any other fixed order.
-/

import Mathlib

open Equiv Finset

/-! ## Definition of f_k(n) -/

/-- `permCountOfOrder n k` counts the number of elements of `S_n`
    (permutations of `Fin n`) that have order exactly `k`. -/
noncomputable def permCountOfOrder (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Perm (Fin n) => orderOf σ = k)).card

/-- The order that maximizes `permCountOfOrder n k` over all `k`. -/
noncomputable def maxPermOrder (n : ℕ) : ℕ :=
  ((Finset.range (n.factorial + 1)).image (permCountOfOrder n)).max' ⟨permCountOfOrder n 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _), rfl⟩⟩

/-! ## Main result -/

/-- For `n ≥ 3`, involutions (elements of order 2) are the most numerous
    among permutations of any fixed order in `S_n`. -/
theorem involutions_maximize_permCountOfOrder (n : ℕ) (hn : 3 ≤ n) (k : ℕ) :
    permCountOfOrder n k ≤ permCountOfOrder n 2 := by
  sorry

/-! ## Equivalent formulation: the maximizing order is 2 -/

/-- For `n ≥ 3`, `permCountOfOrder n 2` equals the maximum of `permCountOfOrder n k`
    over all `k`. -/
theorem permCountOfOrder_two_eq_max (n : ℕ) (hn : 3 ≤ n) :
    permCountOfOrder n 2 = maxPermOrder n := by
  sorry

/-! ## Boundary cases -/

/-
For `n = 1`, the only permutation is the identity (order 1).
-/
theorem permCountOfOrder_one_one :
    permCountOfOrder 1 1 = 1 := by
  -- For $n = 1$, the only permutation is the identity permutation, which has order 1.
  simp [permCountOfOrder];
  simp +decide

/-
For `n = 2`, there is exactly one involution and one identity.
-/
theorem permCountOfOrder_two_cases :
    permCountOfOrder 2 1 = 1 ∧ permCountOfOrder 2 2 = 1 := by
  unfold permCountOfOrder; simp +decide ;
  simp +decide only [orderOf_eq_iff]