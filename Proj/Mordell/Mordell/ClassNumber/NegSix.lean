import Mordell.ClassNumber.Common

open Zsqrtd
open scoped nonZeroDivisors

/-!
# Class-number input for `d = -6`
-/

namespace Mordell

def sqrtTwoIdealNegSix : Ideal R6 :=
  Ideal.span ({(⟨0, 1⟩ : R6), (2 : R6)} : Set R6)

lemma sqrtTwoIdealNegSix_ne_bot : sqrtTwoIdealNegSix ≠ ⊥ := by
  intro h
  have hmem : (2 : R6) ∈ sqrtTwoIdealNegSix := Ideal.subset_span (by simp)
  rw [h] at hmem
  have htwo : (2 : R6) = 0 := by simpa using hmem
  norm_num at htwo

noncomputable def sqrtTwoClassNegSix [IsDomain R6] [IsDedekindDomain R6] :
    ClassGroup R6 :=
  ClassGroup.mk0
    ⟨sqrtTwoIdealNegSix,
      mem_nonZeroDivisors_iff_ne_zero.mpr sqrtTwoIdealNegSix_ne_bot⟩

lemma mem_sqrtTwoIdealNegSix_iff (z : R6) :
    z ∈ sqrtTwoIdealNegSix ↔ Even z.re := by
  constructor
  · intro hz
    change z ∈ Submodule.span R6 ({(⟨0, 1⟩ : R6), (2 : R6)} : Set R6) at hz
    exact Submodule.span_induction (p := fun x _ => Even x.re)
      (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · simp
        · norm_num)
      (by simp)
      (by
        intro _ _ _ _ hxEven hyEven
        exact hxEven.add hyEven)
      (by
        intro a x _ hxEven
        rcases hxEven with ⟨k, hk⟩
        rcases a with ⟨ar, ai⟩
        rcases x with ⟨xr, xi⟩
        simp at hk ⊢
        use ar * k - 3 * ai * xi
        rw [hk]
        ring)
      hz
  · rintro ⟨k, hk⟩
    have h_eq : z = (k : R6) * (2 : R6) + (z.im : R6) * (⟨0, 1⟩ : R6) := by
      ext <;> simp [hk] <;> ring
    rw [h_eq]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

lemma class_mk0_eq_one_or_sqrtTwo_negSix
    [IsDomain R6] [IsDedekindDomain R6]
    (J : nonZeroDivisors (Ideal R6)) (h2 : (2 : R6) ∈ (J : Ideal R6)) :
    ClassGroup.mk0 J = 1 ∨ ClassGroup.mk0 J = sqrtTwoClassNegSix := by
  let I : Ideal R6 := J
  by_cases hodd : ∃ z : R6, z ∈ I ∧ Odd z.re
  · obtain ⟨z, hz, hzodd⟩ := hodd
    have hnorm_odd : Odd z.norm := by
      rcases hzodd with ⟨k, hk⟩
      use 2 * k ^ 2 + 2 * k + 3 * z.im ^ 2
      rcases z with ⟨zr, zi⟩
      simp [Zsqrtd.norm] at hk ⊢
      rw [hk]
      ring
    have hnorm_mem : ((z.norm : ℤ) : R6) ∈ I := by
      have hzmul := I.mul_mem_left (star z) hz
      simpa [Zsqrtd.norm_eq_mul_conj, mul_comm] using hzmul
    have hone : (1 : R6) ∈ I := by
      rcases hnorm_odd with ⟨k, hk⟩
      have hmul : (k : R6) * (2 : R6) ∈ I := I.mul_mem_left (k : R6) h2
      have h_eq : (1 : R6) = ((z.norm : ℤ) : R6) - (k : R6) * (2 : R6) := by
        ext <;> simp [hk] <;> ring
      rw [h_eq]
      exact I.sub_mem hnorm_mem hmul
    left
    rw [ClassGroup.mk0_eq_one_iff J.2]
    have htop : I = ⊤ := (Ideal.eq_top_iff_one I).mpr hone
    change I.IsPrincipal
    rw [htop]
    infer_instance
  · have h_even_re : ∀ z : R6, z ∈ I → Even z.re := by
      intro z hz
      rw [← Int.not_odd_iff_even]
      intro hzodd
      exact hodd ⟨z, hz, hzodd⟩
    by_cases hsqrt : (⟨0, 1⟩ : R6) ∈ I
    · right
      have hle : I ≤ sqrtTwoIdealNegSix := by
        intro z hz
        exact (mem_sqrtTwoIdealNegSix_iff z).mpr (h_even_re z hz)
      have hge : sqrtTwoIdealNegSix ≤ I := by
        rw [sqrtTwoIdealNegSix, Ideal.span_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hsqrt
        · exact h2
      have hEq : I = sqrtTwoIdealNegSix := le_antisymm hle hge
      have hJ :
          J =
            ⟨sqrtTwoIdealNegSix,
              mem_nonZeroDivisors_iff_ne_zero.mpr sqrtTwoIdealNegSix_ne_bot⟩ :=
        Subtype.ext hEq
      rw [hJ]
      rfl
    · left
      have hle : I ≤ Ideal.span ({(2 : R6)} : Set R6) := by
        intro z hz
        have hre : Even z.re := h_even_re z hz
        have him : Even z.im := by
          rw [← Int.not_odd_iff_even]
          intro himOdd
          apply hsqrt
          rcases hre with ⟨k, hk⟩
          rcases himOdd with ⟨l, hl⟩
          have h02 : (⟨0, 2⟩ : R6) ∈ I := by
            have hmul := I.mul_mem_left (⟨0, 1⟩ : R6) h2
            simpa using hmul
          have h_eq :
              (⟨0, 1⟩ : R6) = z - (k : R6) * (2 : R6) - (l : R6) * (⟨0, 2⟩ : R6) := by
            ext <;> simp [hk, hl] <;> ring
          rw [h_eq]
          exact I.sub_mem (I.sub_mem hz (I.mul_mem_left (k : R6) h2))
            (I.mul_mem_left (l : R6) h02)
        exact (mem_span_two_negSix_iff z).mpr ⟨hre, him⟩
      have hge : Ideal.span ({(2 : R6)} : Set R6) ≤ I := by
        rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact h2
      have hEq : I = Ideal.span ({(2 : R6)} : Set R6) := le_antisymm hle hge
      rw [ClassGroup.mk0_eq_one_iff J.2]
      change I.IsPrincipal
      rw [hEq]
      infer_instance

lemma classGroup_negSix_eq_one_or_sqrtTwo
    [IsDomain R6] [IsDedekindDomain R6] (C : ClassGroup R6) :
    C = 1 ∨ C = sqrtTwoClassNegSix := by
  obtain ⟨J, hJ, h2⟩ :=
    classGroup_exists_mk0_mem_two_of_neg_six_le (-6) (by norm_num) (by norm_num) C
  rcases class_mk0_eq_one_or_sqrtTwo_negSix J h2 with h | h
  · left
    rw [hJ, h]
  · right
    rw [hJ, h]

theorem classNumber_gcd_three_neg_six :
    Nat.gcd (quadClassNumber (-6)) 3 = 1 := by
  have hmod : (-6 : ℤ) % 4 = 2 ∨ (-6 : ℤ) % 4 = 3 := Or.inl (by decide)
  have hsqf : Squarefree (-6 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact (Nat.squarefree_mul (by norm_num : Nat.Coprime 2 3)).mpr
      ⟨Nat.prime_two.squarefree, (by norm_num : Nat.Prime 3).squarefree⟩
  haveI : IsDedekindDomain R6 :=
    zsqrtd_isDedekindDomain_of_squarefree_mod (-6) hmod hsqf
  letI : Fintype (ClassGroup R6) :=
    ClassGroup.fintypeOfAdmissibleOfAlgebraic
      (zsqrtdBasis (-6)) AbsoluteValue.absIsAdmissible
  have hquad : quadClassNumber (-6) = Nat.card (ClassGroup R6) := by
    simp [quadClassNumber]
  rw [hquad]
  exact ClassNumber.gcd_three_of_card_le_two
    (ClassNumber.card_le_two_of_two_values sqrtTwoClassNegSix
      classGroup_negSix_eq_one_or_sqrtTwo)

end Mordell
