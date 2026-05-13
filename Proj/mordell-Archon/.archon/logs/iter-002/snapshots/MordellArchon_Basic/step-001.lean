import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

open Zsqrtd

/-!
# Mordell Targets

This file lists the main theorem-proving targets for the Mordell project.
-/

axiom quadClassNumber : ℤ → ℕ

/--
Generic Mordell descent target for equations of the form `y^2 = x^3 + d`.

Under the usual negative, congruence, squarefree, and class-number hypotheses,
every solution is controlled by an integer parameter `m`.
-/
theorem mordell_d (d : ℤ) (hd : d ≤ -1)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ m : ℤ, (d = 1 - 3 * m ^ 2 ∨ d = -1 - 3 * m ^ 2) ∧
      y = m * (3 * d + m ^ 2) := by
  sorry

theorem mordell_minus1_solution_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 1 ↔ x = 1 ∧ y = 0 := by
  sorry

theorem mordell_minus2_solutions_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 2 ↔ (x = 3 ∧ y = 5) ∨ (x = 3 ∧ y = -5) := by
  sorry

theorem mordell_minus13_solutions_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 13 ↔ (x = 17 ∧ y = 70) ∨ (x = 17 ∧ y = -70) := by
  sorry

theorem mordell_minus5 (x y : ℤ) :
    ¬ y ^ 2 = x ^ 3 - 5 := by
  sorry

theorem mordell_minus6 (x y : ℤ) :
    ¬ y ^ 2 = x ^ 3 - 6 := by
  sorry
