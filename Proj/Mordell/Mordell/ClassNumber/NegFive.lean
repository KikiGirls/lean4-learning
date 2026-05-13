import Mordell.ClassNumber.Common

open Zsqrtd
open scoped nonZeroDivisors

/-!
# Class-number input for `d = -5`
-/

namespace Mordell

def sqrtTwoIdealNegFive : Ideal R5 :=
  Ideal.span ({(⟨1, 1⟩ : R5), (2 : R5)} : Set R5)

lemma sqrtTwoIdealNegFive_ne_bot : sqrtTwoIdealNegFive ≠ ⊥ := by
  intro h
  have hmem : (2 : R5) ∈ sqrtTwoIdealNegFive := Ideal.subset_span (by simp)
  rw [h] at hmem
  have htwo : (2 : R5) = 0 := by simpa using hmem
  norm_num at htwo

noncomputable def sqrtTwoClassNegFive [IsDomain R5] [IsDedekindDomain R5] :
    ClassGroup R5 :=
  ClassGroup.mk0
    ⟨sqrtTwoIdealNegFive,
      mem_nonZeroDivisors_iff_ne_zero.mpr sqrtTwoIdealNegFive_ne_bot⟩

lemma mem_sqrtTwoIdealNegFive_iff (z : R5) :
    z ∈ sqrtTwoIdealNegFive ↔ Even (z.re - z.im) := by
  constructor
  · intro hz
    change z ∈ Submodule.span R5 ({(⟨1, 1⟩ : R5), (2 : R5)} : Set R5) at hz
    exact Submodule.span_induction (p := fun x _ => Even (x.re - x.im))
      (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · simp
        · norm_num)
      (by simp)
      (by
        intro x y _ _ hxEven hyEven
        rcases hxEven with ⟨m, hm⟩
        rcases hyEven with ⟨n, hn⟩
        use m + n
        simp
        nlinarith)
      (by
        intro a x _ hxEven
        rcases hxEven with ⟨k, hk⟩
        rcases a with ⟨ar, ai⟩
        rcases x with ⟨xr, xi⟩
        simp at hk ⊢
        use ar * k - ai * (3 * xi + k)
        have hxr : xr = xi + 2 * k := by omega
        rw [hxr]
        ring)
      hz
  · rintro ⟨k, hk⟩
    have h_eq : z = (z.im : R5) * (⟨1, 1⟩ : R5) + (k : R5) * (2 : R5) := by
      have hre : z.re = z.im + 2 * k := by omega
      ext <;> simp [hre] <;> ring
    rw [h_eq]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

lemma class_mk0_eq_one_or_sqrtTwo_negFive
    [IsDomain R5] [IsDedekindDomain R5]
    (J : nonZeroDivisors (Ideal R5)) (h2 : (2 : R5) ∈ (J : Ideal R5)) :
    ClassGroup.mk0 J = 1 ∨ ClassGroup.mk0 J = sqrtTwoClassNegFive := by
  let I : Ideal R5 := J
  by_cases hodd : ∃ z : R5, z ∈ I ∧ Odd (z.re - z.im)
  · obtain ⟨z, hz, hzodd⟩ := hodd
    have hnorm_odd : Odd z.norm := by
      rcases hzodd with ⟨k, hk⟩
      use 3 * z.im ^ 2 + 2 * k ^ 2 + 2 * k * z.im + z.im + 2 * k
      rcases z with ⟨zr, zi⟩
      simp [Zsqrtd.norm] at hk ⊢
      have hzr : zr = zi + (2 * k + 1) := by omega
      rw [hzr]
      ring
    have hnorm_mem : ((z.norm : ℤ) : R5) ∈ I := by
      have hzmul := I.mul_mem_left (star z) hz
      simpa [Zsqrtd.norm_eq_mul_conj, mul_comm] using hzmul
    have hone : (1 : R5) ∈ I := by
      rcases hnorm_odd with ⟨k, hk⟩
      have hmul : (k : R5) * (2 : R5) ∈ I := I.mul_mem_left (k : R5) h2
      have h_eq : (1 : R5) = ((z.norm : ℤ) : R5) - (k : R5) * (2 : R5) := by
        ext <;> simp [hk] <;> ring
      rw [h_eq]
      exact I.sub_mem hnorm_mem hmul
    left
    rw [ClassGroup.mk0_eq_one_iff J.2]
    have htop : I = ⊤ := (Ideal.eq_top_iff_one I).mpr hone
    change I.IsPrincipal
    rw [htop]
    infer_instance
  · have h_even_diff : ∀ z : R5, z ∈ I → Even (z.re - z.im) := by
      intro z hz
      rw [← Int.not_odd_iff_even]
      intro hzodd
      exact hodd ⟨z, hz, hzodd⟩
    by_cases hsqrt : (⟨1, 1⟩ : R5) ∈ I
    · right
      have hle : I ≤ sqrtTwoIdealNegFive := by
        intro z hz
        exact (mem_sqrtTwoIdealNegFive_iff z).mpr (h_even_diff z hz)
      have hge : sqrtTwoIdealNegFive ≤ I := by
        rw [sqrtTwoIdealNegFive, Ideal.span_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hsqrt
        · exact h2
      have hEq : I = sqrtTwoIdealNegFive := le_antisymm hle hge
      have hJ :
          J =
            ⟨sqrtTwoIdealNegFive,
              mem_nonZeroDivisors_iff_ne_zero.mpr sqrtTwoIdealNegFive_ne_bot⟩ :=
        Subtype.ext hEq
      rw [hJ]
      rfl
    · left
      have hle : I ≤ Ideal.span ({(2 : R5)} : Set R5) := by
        intro z hz
        have hdiff : Even (z.re - z.im) := h_even_diff z hz
        have him : Even z.im := by
          rw [← Int.not_odd_iff_even]
          intro himOdd
          apply hsqrt
          rcases hdiff with ⟨k, hk⟩
          rcases himOdd with ⟨l, hl⟩
          have h22 : (⟨2, 2⟩ : R5) ∈ I := by
            have hmul := I.mul_mem_left (⟨1, 1⟩ : R5) h2
            simpa using hmul
          have h_eq :
              (⟨1, 1⟩ : R5) = z - (k : R5) * (2 : R5) - (l : R5) * (⟨2, 2⟩ : R5) := by
            have hre : z.re = z.im + 2 * k := by omega
            ext <;> simp [hre, hl] <;> ring
          rw [h_eq]
          exact I.sub_mem (I.sub_mem hz (I.mul_mem_left (k : R5) h2))
            (I.mul_mem_left (l : R5) h22)
        have hre : Even z.re := by
          rcases hdiff with ⟨k, hk⟩
          rcases him with ⟨l, hl⟩
          use l + k
          omega
        exact (mem_span_two_negFive_iff z).mpr ⟨hre, him⟩
      have hge : Ideal.span ({(2 : R5)} : Set R5) ≤ I := by
        rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact h2
      have hEq : I = Ideal.span ({(2 : R5)} : Set R5) := le_antisymm hle hge
      rw [ClassGroup.mk0_eq_one_iff J.2]
      change I.IsPrincipal
      rw [hEq]
      infer_instance

lemma classGroup_negFive_eq_one_or_sqrtTwo
    [IsDomain R5] [IsDedekindDomain R5] (C : ClassGroup R5) :
    C = 1 ∨ C = sqrtTwoClassNegFive := by
  obtain ⟨J, hJ, h2⟩ :=
    classGroup_exists_mk0_mem_two_of_neg_six_le (-5) (by norm_num) (by norm_num) C
  rcases class_mk0_eq_one_or_sqrtTwo_negFive J h2 with h | h
  · left
    rw [hJ, h]
  · right
    rw [hJ, h]

theorem classNumber_gcd_three_neg_five :
    Nat.gcd (quadClassNumber (-5)) 3 = 1 := by
  have hmod : (-5 : ℤ) % 4 = 2 ∨ (-5 : ℤ) % 4 = 3 := Or.inr (by decide)
  have hsqf : Squarefree (-5 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact (by norm_num : Nat.Prime 5).squarefree
  haveI : IsDedekindDomain R5 :=
    zsqrtd_isDedekindDomain_of_squarefree_mod (-5) hmod hsqf
  letI : Fintype (ClassGroup R5) :=
    ClassGroup.fintypeOfAdmissibleOfAlgebraic
      (zsqrtdBasis (-5)) AbsoluteValue.absIsAdmissible
  have hquad : quadClassNumber (-5) = Nat.card (ClassGroup R5) := by
    simp [quadClassNumber]
  rw [hquad]
  exact ClassNumber.gcd_three_of_card_le_two
    (ClassNumber.card_le_two_of_two_values sqrtTwoClassNegFive
      classGroup_negFive_eq_one_or_sqrtTwo)

end Mordell
