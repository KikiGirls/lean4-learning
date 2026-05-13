import Mordell.Approximation

open Zsqrtd
open scoped nonZeroDivisors

namespace Mordell

/--
自定义的类群代表元判别准则。

如果分式域论证中的每个商都能用有限集合 `M` 近似，那么每个理想类都有一个
包含 `prodM` 的整代表元。这是旧版类数计算中在具体枚举
`d = -5, -6, -13` 之前使用的小型一般引理的 Lean4 版本。
-/
theorem exists_mk0_eq_mk0_of_approx
    {R S : Type*} [EuclideanDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [IsDedekindDomain S]
    (abv : AbsoluteValue R ℤ) (I : (Ideal S)⁰)
    (M : Finset R) (prodM : R)
    (hprodM : ∀ m ∈ M, m ∣ prodM)
    (hprodMnz : algebraMap R S prodM ≠ 0)
    (hex : ∀ (a : S) {b : S}, b ≠ 0 →
      ∃ (q : S) (r : R), r ∈ M ∧
        abv (Algebra.norm R (r • a - q * b)) < abv (Algebra.norm R b)) :
    ∃ J : (Ideal S)⁰,
      ClassGroup.mk0 I = ClassGroup.mk0 J ∧ algebraMap R S prodM ∈ (J : Ideal S) := by
  classical
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ := ClassGroup.exists_min abv I
  have hI_ne : (I : Ideal S) ≠ 0 := nonZeroDivisors.coe_ne_zero I
  suffices hdiv : Ideal.span ({b} : Set S) ∣ Ideal.span ({algebraMap R S prodM} : Set S) * I.1 by
    obtain ⟨J, hJ⟩ := hdiv
    have hJ_ne : J ≠ 0 := by
      intro hJ0
      subst J
      have hJ' : algebraMap R S prodM = 0 ∨ (I : Ideal S) = 0 := by
        simpa [Ideal.mul_eq_bot, Ideal.span_singleton_eq_bot] using hJ
      rcases hJ' with hM0 | hI0
      · exact hprodMnz hM0
      · exact hI_ne hI0
    refine ⟨⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ_ne⟩, ?_, ?_⟩
    · rw [ClassGroup.mk0_eq_mk0_iff]
      refine ⟨algebraMap R S prodM, b, hprodMnz, b_ne_zero, ?_⟩
      exact hJ
    · rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Ideal.span_le, ← Ideal.dvd_iff_le]
      apply (mul_dvd_mul_iff_left ?_).mp
      · rw [Subtype.coe_mk, Ideal.dvd_iff_le, ← hJ, mul_comm]
        apply Ideal.mul_mono le_rfl
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact b_mem
      · exact mt Ideal.span_singleton_eq_bot.mp b_ne_zero
  rw [Ideal.dvd_iff_le, Ideal.mul_le]
  intro r' hr' a ha
  rw [Ideal.mem_span_singleton] at hr' ⊢
  obtain ⟨q, r, r_mem, lt⟩ := hex a b_ne_zero
  apply @dvd_of_mul_left_dvd _ _ q
  simp only [Algebra.smul_def] at lt
  rw [← sub_eq_zero.mp (b_min _
    (I.1.sub_mem (I.1.mul_mem_left _ ha) (I.1.mul_mem_left _ b_mem)) lt)]
  refine mul_dvd_mul_right (dvd_trans (map_dvd (algebraMap R S) ?_) hr') _
  exact hprodM _ r_mem

theorem classGroup_exists_mk0_mem_two_of_neg_six_le
    (d : ℤ) (hd_neg : d < 0) (hd_ge : -6 ≤ d)
    [IsDomain (ℤ√d)] [IsDedekindDomain (ℤ√d)] (C : ClassGroup (ℤ√d)) :
    ∃ J : (Ideal (ℤ√d))⁰,
      C = ClassGroup.mk0 J ∧ (2 : ℤ√d) ∈ (J : Ideal (ℤ√d)) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective C
  obtain ⟨J, hJ, hmem⟩ :=
    exists_mk0_eq_mk0_of_approx (R := ℤ) (S := ℤ√d) AbsoluteValue.abs I
      ({1, 2} : Finset ℤ) 2
      (by
        intro m hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl <;> norm_num)
      (by norm_num)
      (by
        intro a b hb
        exact exists_q_r_of_neg_six_le d hd_neg hd_ge a hb)
  exact ⟨J, hJ, by simpa using hmem⟩

theorem classGroup_exists_mk0_mem_twelve_neg_thirteen
    [IsDomain (ℤ√(-13 : ℤ))] [IsDedekindDomain (ℤ√(-13 : ℤ))]
    (C : ClassGroup (ℤ√(-13 : ℤ))) :
    ∃ J : (Ideal (ℤ√(-13 : ℤ)))⁰,
      C = ClassGroup.mk0 J ∧ (12 : ℤ√(-13 : ℤ)) ∈ (J : Ideal (ℤ√(-13 : ℤ))) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective C
  obtain ⟨J, hJ, hmem⟩ :=
    exists_mk0_eq_mk0_of_approx (R := ℤ) (S := ℤ√(-13 : ℤ)) AbsoluteValue.abs I
      ({1, 2, 3, 4} : Finset ℤ) 12
      (by
        intro m hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl | rfl | rfl <;> norm_num)
      (by norm_num)
      (by
        intro a b hb
        exact exists_q_r_of_neg_thirteen a hb)
  exact ⟨J, hJ, by simpa using hmem⟩

/--
Mordell 下降法所需的类数输入。

当 `d` 为负时，它是 `ℤ√d` 的类群基数。
-/
noncomputable def quadClassNumber (d : ℤ) : ℕ :=
  if hd : d < 0 then
    haveI : IsDomain (ℤ√d) := by
      letI : NoZeroDivisors (ℤ√d) :=
      {
        eq_zero_or_eq_zero_of_mul_eq_zero := by
          intro a b hab
          have hnorm : a.norm * b.norm = 0 := by
            simpa [Zsqrtd.norm_mul] using congrArg Zsqrtd.norm hab
          rcases mul_eq_zero.mp hnorm with ha | hb
          · exact Or.inl ((Zsqrtd.norm_eq_zero_iff hd a).mp ha)
          · exact Or.inr ((Zsqrtd.norm_eq_zero_iff hd b).mp hb) }
      exact NoZeroDivisors.to_isDomain (ℤ√d)
    Nat.card (ClassGroup (ℤ√d))
  else
    0

end Mordell
