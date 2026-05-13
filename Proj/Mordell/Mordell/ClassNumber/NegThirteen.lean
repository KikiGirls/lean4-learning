import Mordell.ClassNumber.Common

open Zsqrtd
open scoped nonZeroDivisors

/-!
# Class-number input for `d = -13`
-/

namespace Mordell

def sqrtTwoIdealNegThirteen : Ideal R13 :=
  Ideal.span ({(⟨1, 1⟩ : R13), (2 : R13)} : Set R13)

lemma sqrtTwoIdealNegThirteen_ne_bot : sqrtTwoIdealNegThirteen ≠ ⊥ := by
  intro h
  have hmem : (2 : R13) ∈ sqrtTwoIdealNegThirteen := Ideal.subset_span (by simp)
  rw [h] at hmem
  have htwo : (2 : R13) = 0 := by simpa using hmem
  norm_num at htwo

noncomputable def sqrtTwoClassNegThirteen [IsDomain R13] [IsDedekindDomain R13] :
    ClassGroup R13 :=
  ClassGroup.mk0
    ⟨sqrtTwoIdealNegThirteen,
      mem_nonZeroDivisors_iff_ne_zero.mpr sqrtTwoIdealNegThirteen_ne_bot⟩

lemma mem_sqrtTwoIdealNegThirteen_iff (z : R13) :
    z ∈ sqrtTwoIdealNegThirteen ↔ Even (z.re - z.im) := by
  constructor
  · intro hz
    change z ∈ Submodule.span R13 ({(⟨1, 1⟩ : R13), (2 : R13)} : Set R13) at hz
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
        use ar * k - ai * (7 * xi + k)
        have hxr : xr = xi + 2 * k := by omega
        rw [hxr]
        ring)
      hz
  · rintro ⟨k, hk⟩
    have h_eq : z = (z.im : R13) * (⟨1, 1⟩ : R13) + (k : R13) * (2 : R13) := by
      have hre : z.re = z.im + 2 * k := by omega
      ext <;> simp [hre] <;> ring
    rw [h_eq]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

lemma three_dvd_re_and_im_of_three_dvd_norm_negThirteen (z : R13)
    (h : (3 : ℤ) ∣ z.norm) :
    (3 : ℤ) ∣ z.re ∧ (3 : ℤ) ∣ z.im := by
  have hcast : ((z.norm : ℤ) : ZMod 3) = 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h
  have hsum : (z.re : ZMod 3) ^ 2 + (z.im : ZMod 3) ^ 2 = 0 := by
    have hcast' :
        (z.re : ZMod 3) * (z.re : ZMod 3) +
          (13 : ZMod 3) * (z.im : ZMod 3) * (z.im : ZMod 3) = 0 := by
      simpa [Zsqrtd.norm, pow_two] using hcast
    have h13 : (13 : ZMod 3) = 1 := by decide
    simpa [pow_two, h13, mul_assoc] using hcast'
  have hzero : (z.re : ZMod 3) = 0 ∧ (z.im : ZMod 3) = 0 := by
    have h : ∀ a b : ZMod 3, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0 := by
      decide
    exact h _ _ hsum
  constructor
  · simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hzero.1
  · simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hzero.2

lemma class_mk0_eq_one_or_sqrtTwo_negThirteen
    [IsDomain R13] [IsDedekindDomain R13]
    (J : nonZeroDivisors (Ideal R13)) (h2 : (2 : R13) ∈ (J : Ideal R13)) :
    ClassGroup.mk0 J = 1 ∨ ClassGroup.mk0 J = sqrtTwoClassNegThirteen := by
  let I : Ideal R13 := J
  by_cases hodd : ∃ z : R13, z ∈ I ∧ Odd (z.re - z.im)
  · obtain ⟨z, hz, hzodd⟩ := hodd
    have hnorm_odd : Odd z.norm := by
      rcases hzodd with ⟨k, hk⟩
      use 7 * z.im ^ 2 + 2 * k * z.im + z.im + 2 * k ^ 2 + 2 * k
      rcases z with ⟨zr, zi⟩
      simp [Zsqrtd.norm] at hk ⊢
      have hzr : zr = zi + (2 * k + 1) := by omega
      rw [hzr]
      ring
    have hnorm_mem : ((z.norm : ℤ) : R13) ∈ I := by
      have hzmul := I.mul_mem_left (star z) hz
      simpa [Zsqrtd.norm_eq_mul_conj, mul_comm] using hzmul
    have hone : (1 : R13) ∈ I := by
      rcases hnorm_odd with ⟨k, hk⟩
      have hmul : (k : R13) * (2 : R13) ∈ I := I.mul_mem_left (k : R13) h2
      have h_eq : (1 : R13) = ((z.norm : ℤ) : R13) - (k : R13) * (2 : R13) := by
        ext <;> simp [hk] <;> ring
      rw [h_eq]
      exact I.sub_mem hnorm_mem hmul
    left
    rw [ClassGroup.mk0_eq_one_iff J.2]
    have htop : I = ⊤ := (Ideal.eq_top_iff_one I).mpr hone
    change I.IsPrincipal
    rw [htop]
    infer_instance
  · have h_even_diff : ∀ z : R13, z ∈ I → Even (z.re - z.im) := by
      intro z hz
      rw [← Int.not_odd_iff_even]
      intro hzodd
      exact hodd ⟨z, hz, hzodd⟩
    by_cases hsqrt : (⟨1, 1⟩ : R13) ∈ I
    · right
      have hle : I ≤ sqrtTwoIdealNegThirteen := by
        intro z hz
        exact (mem_sqrtTwoIdealNegThirteen_iff z).mpr (h_even_diff z hz)
      have hge : sqrtTwoIdealNegThirteen ≤ I := by
        rw [sqrtTwoIdealNegThirteen, Ideal.span_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hsqrt
        · exact h2
      have hEq : I = sqrtTwoIdealNegThirteen := le_antisymm hle hge
      have hJ :
          J =
            ⟨sqrtTwoIdealNegThirteen,
              mem_nonZeroDivisors_iff_ne_zero.mpr sqrtTwoIdealNegThirteen_ne_bot⟩ :=
        Subtype.ext hEq
      rw [hJ]
      rfl
    · left
      have hle : I ≤ Ideal.span ({(2 : R13)} : Set R13) := by
        intro z hz
        have hdiff : Even (z.re - z.im) := h_even_diff z hz
        have him : Even z.im := by
          rw [← Int.not_odd_iff_even]
          intro himOdd
          apply hsqrt
          rcases hdiff with ⟨k, hk⟩
          rcases himOdd with ⟨l, hl⟩
          have h22 : (⟨2, 2⟩ : R13) ∈ I := by
            have hmul := I.mul_mem_left (⟨1, 1⟩ : R13) h2
            simpa using hmul
          have h_eq :
              (⟨1, 1⟩ : R13) = z - (k : R13) * (2 : R13) - (l : R13) * (⟨2, 2⟩ : R13) := by
            have hre : z.re = z.im + 2 * k := by omega
            ext <;> simp [hre, hl] <;> ring
          rw [h_eq]
          exact I.sub_mem (I.sub_mem hz (I.mul_mem_left (k : R13) h2))
            (I.mul_mem_left (l : R13) h22)
        have hre : Even z.re := by
          rcases hdiff with ⟨k, hk⟩
          rcases him with ⟨l, hl⟩
          use l + k
          omega
        exact (mem_span_two_negThirteen_iff z).mpr ⟨hre, him⟩
      have hge : Ideal.span ({(2 : R13)} : Set R13) ≤ I := by
        rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact h2
      have hEq : I = Ideal.span ({(2 : R13)} : Set R13) := le_antisymm hle hge
      rw [ClassGroup.mk0_eq_one_iff J.2]
      change I.IsPrincipal
      rw [hEq]
      infer_instance

lemma one_one_mem_of_mem_four_of_odd_re_even_diff
    (I : Ideal R13) (h4 : (4 : R13) ∈ I) {z : R13}
    (hz : z ∈ I) (hzre : Odd z.re) (hdiff : Even (z.re - z.im)) :
    (⟨1, 1⟩ : R13) ∈ I := by
  rcases hzre with ⟨a, ha⟩
  rcases hdiff with ⟨k, hk⟩
  let b : ℤ := a - k
  have him : z.im = 2 * b + 1 := by omega
  have h04 : (⟨0, 4⟩ : R13) ∈ I := by
    have hmul := I.mul_mem_left (⟨0, 1⟩ : R13) h4
    simpa using hmul
  have hmem_of_congr :
      ∀ w : R13, w ∈ I → ∀ u v : ℤ,
        w.re = 1 + 4 * u → w.im = 1 + 4 * v → (⟨1, 1⟩ : R13) ∈ I := by
    intro w hw u v hre himw
    have h_eq :
        (⟨1, 1⟩ : R13) = w - (u : R13) * (4 : R13) - (v : R13) * (⟨0, 4⟩ : R13) := by
      ext <;> simp [hre, himw] <;> ring
    rw [h_eq]
    exact I.sub_mem (I.sub_mem hw (I.mul_mem_left (u : R13) h4))
      (I.mul_mem_left (v : R13) h04)
  rcases Int.even_or_odd' a with ⟨u, hau | hau⟩
  · rcases Int.even_or_odd' b with ⟨v, hbv | hbv⟩
    · exact hmem_of_congr z hz u v (by omega) (by omega)
    · have hw : (⟨0, 1⟩ : R13) * z ∈ I := I.mul_mem_left (⟨0, 1⟩ : R13) hz
      exact hmem_of_congr ((⟨0, 1⟩ : R13) * z) hw (-13 * v - 10) u
        (by simp [ha, him, hbv]; ring)
        (by simp [ha, hau]; ring)
  · rcases Int.even_or_odd' b with ⟨v, hbv | hbv⟩
    · have hw : -((⟨0, 1⟩ : R13) * z) ∈ I :=
        I.neg_mem (I.mul_mem_left (⟨0, 1⟩ : R13) hz)
      exact hmem_of_congr (-((⟨0, 1⟩ : R13) * z)) hw (13 * v + 3) (-u - 1)
        (by simp [ha, him, hbv]; ring)
        (by simp [ha, hau]; ring)
    · exact hmem_of_congr (-z) (I.neg_mem hz) (-u - 1) (-v - 1)
        (by simp [ha, hau]; ring)
        (by simp [him, hbv]; ring)

lemma class_mk0_eq_one_or_sqrtTwo_negThirteen_of_mem_four
    [IsDomain R13] [IsDedekindDomain R13]
    (J : nonZeroDivisors (Ideal R13)) (h4 : (4 : R13) ∈ (J : Ideal R13)) :
    ClassGroup.mk0 J = 1 ∨ ClassGroup.mk0 J = sqrtTwoClassNegThirteen := by
  let I : Ideal R13 := J
  by_cases h2 : (2 : R13) ∈ I
  · exact class_mk0_eq_one_or_sqrtTwo_negThirteen J h2
  have h_even_diff : ∀ z : R13, z ∈ I → Even (z.re - z.im) := by
    intro z hz
    rw [← Int.not_odd_iff_even]
    intro hzodd
    have hnorm_odd : Odd z.norm := by
      rcases hzodd with ⟨k, hk⟩
      use 7 * z.im ^ 2 + 2 * k * z.im + z.im + 2 * k ^ 2 + 2 * k
      rcases z with ⟨zr, zi⟩
      simp [Zsqrtd.norm] at hk ⊢
      have hzr : zr = zi + (2 * k + 1) := by omega
      rw [hzr]
      ring
    have hnorm_mem : ((z.norm : ℤ) : R13) ∈ I := by
      have hzmul := I.mul_mem_left (star z) hz
      simpa [Zsqrtd.norm_eq_mul_conj, mul_comm] using hzmul
    have hcop : IsCoprime z.norm ((2 : ℤ) ^ 2) := by
      have hnot_two : ¬ (2 : ℤ) ∣ z.norm := by
        intro htwo
        exact (Int.not_even_iff_odd.mpr hnorm_odd) (even_iff_two_dvd.mpr htwo)
      exact (Int.prime_two.coprime_iff_not_dvd.mpr hnot_two).symm.pow_right
    obtain ⟨u, v, huv⟩ := hcop
    have hleft : (u : R13) * ((z.norm : ℤ) : R13) ∈ I :=
      I.mul_mem_left (u : R13) hnorm_mem
    have hright : (v : R13) * (4 : R13) ∈ I :=
      I.mul_mem_left (v : R13) h4
    have hone : (1 : R13) ∈ I := by
      have hsum := I.add_mem hleft hright
      have h_eq :
          (u : R13) * ((z.norm : ℤ) : R13) + (v : R13) * (4 : R13) = 1 := by
        ext
        · simpa [pow_two] using huv
        · simp
      rwa [h_eq] at hsum
    exact h2 ((Ideal.eq_top_iff_one I).mpr hone ▸ trivial)
  have hle_two : I ≤ Ideal.span ({(2 : R13)} : Set R13) := by
    intro z hz
    have hdiff : Even (z.re - z.im) := h_even_diff z hz
    have hre : Even z.re := by
      rw [← Int.not_odd_iff_even]
      intro hzre
      have h11 := one_one_mem_of_mem_four_of_odd_re_even_diff I h4 hz hzre hdiff
      have hnorm_mem : ((14 : ℤ) : R13) ∈ I := by
        have hmul := I.mul_mem_left (star (⟨1, 1⟩ : R13)) h11
        simpa [Zsqrtd.norm_eq_mul_conj, Zsqrtd.norm, mul_comm] using hmul
      have hthree4 : (3 : R13) * (4 : R13) ∈ I := I.mul_mem_left (3 : R13) h4
      have htwo_eq : (2 : R13) = ((14 : ℤ) : R13) - (3 : R13) * (4 : R13) := by
        ext <;> norm_num
      exact h2 (by rw [htwo_eq]; exact I.sub_mem hnorm_mem hthree4)
    have him : Even z.im := by
      rcases hre with ⟨r, hr⟩
      rcases hdiff with ⟨k, hk⟩
      use r - k
      omega
    exact (mem_span_two_negThirteen_iff z).mpr ⟨hre, him⟩
  let K : Ideal R13 := idealDivBy (2 : R13) I
  have hK2 : (2 : R13) ∈ K := by
    change (2 : R13) * (2 : R13) ∈ I
    simpa using h4
  have hK_ne : K ≠ ⊥ := by
    intro hK
    have hmem : (2 : R13) ∈ (⊥ : Ideal R13) := by simpa [hK] using hK2
    have hzero : (2 : R13) = 0 := by simpa using hmem
    norm_num at hzero
  let K0 : nonZeroDivisors (Ideal R13) :=
    ⟨K, mem_nonZeroDivisors_iff_ne_zero.mpr hK_ne⟩
  have hIeq : Ideal.span ({(2 : R13)} : Set R13) * K = I :=
    span_singleton_mul_idealDivBy_eq_of_le hle_two
  have hclass : ClassGroup.mk0 J = ClassGroup.mk0 K0 := by
    rw [ClassGroup.mk0_eq_mk0_iff]
    refine ⟨(1 : R13), (2 : R13), by norm_num, by norm_num, ?_⟩
    change Ideal.span ({(1 : R13)} : Set R13) * I =
      Ideal.span ({(2 : R13)} : Set R13) * K
    rw [Ideal.span_singleton_one, Ideal.top_mul, hIeq]
  rcases class_mk0_eq_one_or_sqrtTwo_negThirteen K0 hK2 with h | h
  · left
    rw [hclass, h]
  · right
    rw [hclass, h]

lemma class_mk0_eq_one_or_sqrtTwo_negThirteen_of_mem_twelve
    [IsDomain R13] [IsDedekindDomain R13]
    (J : nonZeroDivisors (Ideal R13)) (h12 : (12 : R13) ∈ (J : Ideal R13)) :
    ClassGroup.mk0 J = 1 ∨ ClassGroup.mk0 J = sqrtTwoClassNegThirteen := by
  let I : Ideal R13 := J
  by_cases hle_three : I ≤ Ideal.span ({(3 : R13)} : Set R13)
  · let K : Ideal R13 := idealDivBy (3 : R13) I
    have hK4 : (4 : R13) ∈ K := by
      change (3 : R13) * (4 : R13) ∈ I
      simpa using h12
    have hK_ne : K ≠ ⊥ := by
      intro hK
      have hmem : (4 : R13) ∈ (⊥ : Ideal R13) := by simpa [hK] using hK4
      have hzero : (4 : R13) = 0 := by simpa using hmem
      norm_num at hzero
    let K0 : nonZeroDivisors (Ideal R13) :=
      ⟨K, mem_nonZeroDivisors_iff_ne_zero.mpr hK_ne⟩
    have hIeq : Ideal.span ({(3 : R13)} : Set R13) * K = I :=
      span_singleton_mul_idealDivBy_eq_of_le hle_three
    have hclass : ClassGroup.mk0 J = ClassGroup.mk0 K0 := by
      rw [ClassGroup.mk0_eq_mk0_iff]
      refine ⟨(1 : R13), (3 : R13), by norm_num, by norm_num, ?_⟩
      change Ideal.span ({(1 : R13)} : Set R13) * I =
        Ideal.span ({(3 : R13)} : Set R13) * K
      rw [Ideal.span_singleton_one, Ideal.top_mul, hIeq]
    rcases class_mk0_eq_one_or_sqrtTwo_negThirteen_of_mem_four K0 hK4 with h | h
    · left
      rw [hclass, h]
    · right
      rw [hclass, h]
  · have hnot_le := hle_three
    rw [SetLike.le_def] at hnot_le
    push Not at hnot_le
    obtain ⟨z, hz, hz_not_three⟩ := hnot_le
    have hnorm_mem : ((z.norm : ℤ) : R13) ∈ I := by
      have hzmul := I.mul_mem_left (star z) hz
      simpa [Zsqrtd.norm_eq_mul_conj, mul_comm] using hzmul
    have hnot_three : ¬ (3 : ℤ) ∣ z.norm := by
      intro hnorm3
      exact hz_not_three ((mem_span_three_negThirteen_iff z).mpr
        (three_dvd_re_and_im_of_three_dvd_norm_negThirteen z hnorm3))
    have hcop : IsCoprime z.norm (3 : ℤ) := by
      exact ((show Prime (3 : ℤ) by norm_num).coprime_iff_not_dvd.mpr hnot_three).symm
    obtain ⟨u, v, huv⟩ := hcop
    have hleft : ((4 * u : ℤ) : R13) * ((z.norm : ℤ) : R13) ∈ I :=
      I.mul_mem_left (((4 * u : ℤ) : R13)) hnorm_mem
    have hright : (v : R13) * (12 : R13) ∈ I :=
      I.mul_mem_left (v : R13) h12
    have h4 : (4 : R13) ∈ I := by
      have hsum := I.add_mem hleft hright
      have h_eq :
          ((4 * u : ℤ) : R13) * ((z.norm : ℤ) : R13) +
            (v : R13) * (12 : R13) = 4 := by
        ext
        · norm_num [Int.cast_mul]
          nlinarith [huv]
        · simp
      rwa [h_eq] at hsum
    exact class_mk0_eq_one_or_sqrtTwo_negThirteen_of_mem_four J h4

lemma classGroup_negThirteen_eq_one_or_sqrtTwo
    [IsDomain R13] [IsDedekindDomain R13] (C : ClassGroup R13) :
    C = 1 ∨ C = sqrtTwoClassNegThirteen := by
  obtain ⟨J, hJ, h12⟩ := classGroup_exists_mk0_mem_twelve_neg_thirteen C
  rcases class_mk0_eq_one_or_sqrtTwo_negThirteen_of_mem_twelve J h12 with h | h
  · left
    rw [hJ, h]
  · right
    rw [hJ, h]

theorem classNumber_gcd_three_neg_thirteen :
    Nat.gcd (quadClassNumber (-13)) 3 = 1 := by
  have hmod : (-13 : ℤ) % 4 = 2 ∨ (-13 : ℤ) % 4 = 3 := Or.inr (by decide)
  have hsqf : Squarefree (-13 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact (by norm_num : Nat.Prime 13).squarefree
  haveI : IsDedekindDomain R13 :=
    zsqrtd_isDedekindDomain_of_squarefree_mod (-13) hmod hsqf
  letI : Fintype (ClassGroup R13) :=
    ClassGroup.fintypeOfAdmissibleOfAlgebraic
      (zsqrtdBasis (-13)) AbsoluteValue.absIsAdmissible
  have hquad : quadClassNumber (-13) = Nat.card (ClassGroup R13) := by
    simp [quadClassNumber]
  rw [hquad]
  exact ClassNumber.gcd_three_of_card_le_two
    (ClassNumber.card_le_two_of_two_values sqrtTwoClassNegThirteen
      classGroup_negThirteen_eq_one_or_sqrtTwo)

end Mordell
