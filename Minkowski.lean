import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Tactic

/-!
# Minkowski class-number method

This file packages the Minkowski class-number input from Mathlib in a form that
is convenient for the concrete Mordell project.

The main point is that every ideal class in the ring of integers of a number
field has an integral ideal representative whose absolute norm is bounded by the
Minkowski bound.  For quadratic imaginary fields this gives a particularly small
finite search.
-/

open scoped nonZeroDivisors Real

open NumberField NumberField.InfinitePlace Module Ideal Nat

namespace Mordell
namespace Minkowski

/--
The usual Minkowski bound

`(4 / π)^r₂ * n! / n^n * sqrt(|D_K|)`.

Mathlib uses this expression directly in `NumberField.exists_ideal_in_class_of_norm_le`;
we name it here so downstream files can state the method without repeating the
formula.
-/
noncomputable abbrev bound (K : Type*) [Field K] [NumberField K] : ℝ :=
  (4 / Real.pi) ^ nrComplexPlaces K *
    ((Module.finrank ℚ K)! / (Module.finrank ℚ K) ^ (Module.finrank ℚ K) *
      Real.sqrt |NumberField.discr K|)

variable (K : Type*) [Field K] [NumberField K]

/--
Minkowski's ideal-class representative theorem.

Every ideal class has a representative whose absolute norm is at most
`Mordell.Minkowski.bound K`.
-/
theorem exists_ideal_in_class_of_norm_le (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      Ideal.absNorm (I : Ideal (𝓞 K)) ≤ bound K := by
  simpa [bound] using NumberField.exists_ideal_in_class_of_norm_le (K := K) C

/--
Minkowski method in proof-search form.

To prove that the ring of integers is a PID, it suffices to prove that every
nonzero ideal whose norm is below the Minkowski bound is principal.
-/
theorem isPrincipalIdealRing_of_norm_le
    (h : ∀ ⦃I : (Ideal (𝓞 K))⁰⦄, Ideal.absNorm (I : Ideal (𝓞 K)) ≤ bound K →
      Submodule.IsPrincipal (I : Ideal (𝓞 K))) :
    IsPrincipalIdealRing (𝓞 K) := by
  simpa [bound] using RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le (K := K) h

/--
A small-discriminant Minkowski criterion for principality of the ring of integers.

This is often the shortest route for tiny imaginary quadratic fields with very
small discriminant.
-/
theorem isPrincipalIdealRing_of_abs_discr_lt
    (h : |NumberField.discr K| <
      (2 * (Real.pi / 4) ^ nrComplexPlaces K *
        ((Module.finrank ℚ K) ^ (Module.finrank ℚ K) / (Module.finrank ℚ K)!)) ^ 2) :
    IsPrincipalIdealRing (𝓞 K) := by
  exact RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt (K := K) h

/--
The same small-discriminant criterion stated as a class-number computation.
-/
theorem classNumber_eq_one_of_abs_discr_lt
    (h : |NumberField.discr K| <
      (2 * (Real.pi / 4) ^ nrComplexPlaces K *
        ((Module.finrank ℚ K) ^ (Module.finrank ℚ K) / (Module.finrank ℚ K)!)) ^ 2) :
    NumberField.classNumber K = 1 := by
  exact NumberField.classNumber_eq_one_iff.mpr
    (isPrincipalIdealRing_of_abs_discr_lt (K := K) h)

/--
In a quadratic imaginary field, the small-discriminant threshold from
`isPrincipalIdealRing_of_abs_discr_lt` is exactly `π^2`.
-/
theorem quad_complex_threshold_eq_pi_sq
    (hdeg : Module.finrank ℚ K = 2)
    (hcomplex : nrComplexPlaces K = 1) :
    (2 * (Real.pi / 4) ^ nrComplexPlaces K *
        ((Module.finrank ℚ K) ^ (Module.finrank ℚ K) / (Module.finrank ℚ K)!)) ^ 2 =
      Real.pi ^ 2 := by
  rw [hdeg, hcomplex]
  norm_num [Nat.factorial]
  ring

/--
Minkowski's PID criterion specialized to quadratic imaginary fields.

For a quadratic imaginary number field, proving `|D_K| < π^2` is enough to
deduce that its ring of integers is a PID.
-/
theorem isPrincipalIdealRing_of_quadratic_complex_abs_discr_lt_pi_sq
    (hdeg : Module.finrank ℚ K = 2)
    (hcomplex : nrComplexPlaces K = 1)
    (hdisc : |NumberField.discr K| < Real.pi ^ 2) :
    IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_abs_discr_lt (K := K) ?_
  rwa [quad_complex_threshold_eq_pi_sq (K := K) hdeg hcomplex]

/--
Class-number-one version of
`isPrincipalIdealRing_of_quadratic_complex_abs_discr_lt_pi_sq`.
-/
theorem classNumber_eq_one_of_quadratic_complex_abs_discr_lt_pi_sq
    (hdeg : Module.finrank ℚ K = 2)
    (hcomplex : nrComplexPlaces K = 1)
    (hdisc : |NumberField.discr K| < Real.pi ^ 2) :
    NumberField.classNumber K = 1 := by
  exact NumberField.classNumber_eq_one_iff.mpr
    (isPrincipalIdealRing_of_quadratic_complex_abs_discr_lt_pi_sq
      (K := K) hdeg hcomplex hdisc)

end Minkowski
end Mordell
