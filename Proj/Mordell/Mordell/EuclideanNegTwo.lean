import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic

open Zsqrtd

/-!
# `ℤ√-2` 上的欧几里得结构

本文件包含 `ℤ√(-2)` 的显式除法算法和欧几里得整环实例。
-/

namespace ZsqrtNegTwo

abbrev R := ℤ√(-2 : ℤ)

instance : Div R :=
  ⟨fun x y =>
    let n := (y.norm : ℚ)⁻¹
    let c := star y
    ⟨round ((x * c).re * n : ℚ), round ((x * c).im * n : ℚ)⟩⟩

theorem div_def (x y : R) :
    x / y = ⟨round ((x * star y).re / y.norm : ℚ), round ((x * star y).im / y.norm : ℚ)⟩ := by
  change Zsqrtd.mk _ _ = _
  simp [div_eq_mul_inv]

instance : Mod R :=
  ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : R) : x % y = x - y * (x / y) := rfl

theorem norm_pos {x : R} : 0 < x.norm ↔ x ≠ 0 := by
  constructor
  · intro h hx
    subst hx
    simp [Zsqrtd.norm] at h
  · intro hx
    have hnonneg : 0 ≤ x.norm := Zsqrtd.norm_nonneg (by norm_num : (-2 : ℤ) ≤ 0) x
    have hne : x.norm ≠ 0 := by
      intro h0
      exact hx ((Zsqrtd.norm_eq_zero_iff (by norm_num : (-2 : ℤ) < 0) x).mp h0)
    exact lt_of_le_of_ne hnonneg hne.symm

theorem abs_natCast_norm (x : R) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num : (-2 : ℤ) ≤ 0) x)

theorem rem_mul_conj_re (x y : R) :
    ((x % y) * star y).re = (x * star y).re - y.norm * (x / y).re := by
  simp [mod_def, Zsqrtd.norm]
  ring

theorem rem_mul_conj_im (x y : R) :
    ((x % y) * star y).im = (x * star y).im - y.norm * (x / y).im := by
  simp [mod_def, Zsqrtd.norm]
  ring

theorem norm_rem_mul_norm (x y : R) :
    (x % y).norm * y.norm =
      ((x * star y).re - y.norm * (x / y).re) ^ 2 +
        2 * ((x * star y).im - y.norm * (x / y).im) ^ 2 := by
  have hnorm := Zsqrtd.norm_mul (x % y) (star y)
  rw [Zsqrtd.norm_conj] at hnorm
  have hre := rem_mul_conj_re x y
  have him := rem_mul_conj_im x y
  calc
    (x % y).norm * y.norm = ((x % y) * star y).norm := hnorm.symm
    _ = ((x * star y).re - y.norm * (x / y).re) ^ 2 +
        2 * ((x * star y).im - y.norm * (x / y).im) ^ 2 := by
      simp [Zsqrtd.norm, hre, him]
      ring_nf

private lemma int_round_scaled_abs_le_half (A N : ℤ) (hN : 0 < N) :
    |(((A - N * round ((A : ℚ) / (N : ℚ)) : ℤ) : ℚ))| ≤ (N : ℚ) / 2 := by
  have hNnonneg : (0 : ℚ) ≤ N := by exact_mod_cast hN.le
  have hNne : (N : ℚ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast hN : (0 : ℚ) < N)
  have hround := abs_sub_round (((A : ℚ) / (N : ℚ)))
  calc
    |(((A - N * round ((A : ℚ) / (N : ℚ)) : ℤ) : ℚ))|
        = |(N : ℚ) *
            (((A : ℚ) / (N : ℚ)) - round ((A : ℚ) / (N : ℚ)))| := by
          congr 1
          calc
            (((A - N * round ((A : ℚ) / (N : ℚ)) : ℤ) : ℚ))
                = (A : ℚ) - (N : ℚ) * round ((A : ℚ) / (N : ℚ)) := by
                  norm_num
            _ = (N : ℚ) *
                (((A : ℚ) / (N : ℚ)) - round ((A : ℚ) / (N : ℚ))) := by
                  field_simp [hNne]
    _ = (N : ℚ) *
        |((A : ℚ) / (N : ℚ)) - round ((A : ℚ) / (N : ℚ))| := by
          rw [abs_mul, abs_of_nonneg hNnonneg]
    _ ≤ (N : ℚ) * (1 / 2) := mul_le_mul_of_nonneg_left hround hNnonneg
    _ = (N : ℚ) / 2 := by ring

theorem round_re_bound (x y : R) (hy : y ≠ 0) :
    |(((x * star y).re - y.norm * (x / y).re : ℤ) : ℚ)| ≤ (y.norm : ℚ) / 2 := by
  have hNpos : 0 < y.norm := norm_pos.mpr hy
  let A : ℤ := (x * star y).re
  change |(((A - y.norm * (x / y).re : ℤ) : ℚ))| ≤ (y.norm : ℚ) / 2
  rw [div_def]
  change |(((A - y.norm * round ((A : ℚ) / (y.norm : ℚ)) : ℤ) : ℚ))| ≤
    (y.norm : ℚ) / 2
  exact int_round_scaled_abs_le_half A y.norm hNpos

theorem round_im_bound (x y : R) (hy : y ≠ 0) :
    |(((x * star y).im - y.norm * (x / y).im : ℤ) : ℚ)| ≤ (y.norm : ℚ) / 2 := by
  have hNpos : 0 < y.norm := norm_pos.mpr hy
  let B : ℤ := (x * star y).im
  change |(((B - y.norm * (x / y).im : ℤ) : ℚ))| ≤ (y.norm : ℚ) / 2
  rw [div_def]
  change |(((B - y.norm * round ((B : ℚ) / (y.norm : ℚ)) : ℤ) : ℚ))| ≤
    (y.norm : ℚ) / 2
  exact int_round_scaled_abs_le_half B y.norm hNpos

theorem norm_mod_lt (x : R) {y : R} (hy : y ≠ 0) : (x % y).norm < y.norm := by
  let A : ℤ := (x * star y).re - y.norm * (x / y).re
  let B : ℤ := (x * star y).im - y.norm * (x / y).im
  have hNpos : 0 < y.norm := norm_pos.mpr hy
  have hNposQ : (0 : ℚ) < y.norm := by exact_mod_cast hNpos
  have hAabs : |(A : ℚ)| ≤ (y.norm : ℚ) / 2 := by
    simpa [A] using round_re_bound x y hy
  have hBabs : |(B : ℚ)| ≤ (y.norm : ℚ) / 2 := by
    simpa [B] using round_im_bound x y hy
  have hAnonneg : (0 : ℚ) ≤ (y.norm : ℚ) / 2 := by positivity
  have hAsq : (A : ℚ) ^ 2 ≤ ((y.norm : ℚ) / 2) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hAnonneg] using hAabs
  have hBsq : (B : ℚ) ^ 2 ≤ ((y.norm : ℚ) / 2) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hAnonneg] using hBabs
  have hsum : ((A ^ 2 + 2 * B ^ 2 : ℤ) : ℚ) < ((y.norm : ℤ) : ℚ) ^ 2 := by
    norm_num [Int.cast_add, Int.cast_mul, Int.cast_pow]
    nlinarith [hAsq, hBsq, hNposQ]
  have hprod : ((x % y).norm * y.norm : ℤ) < y.norm * y.norm := by
    have hsum' : (((A ^ 2 + 2 * B ^ 2 : ℤ) : ℚ) < ((y.norm * y.norm : ℤ) : ℚ)) := by
      simpa [pow_two] using hsum
    have hEqAB : (x % y).norm * y.norm = A ^ 2 + 2 * B ^ 2 := by
      simpa [A, B] using norm_rem_mul_norm x y
    have hcast : (((x % y).norm * y.norm : ℤ) : ℚ) = ((A ^ 2 + 2 * B ^ 2 : ℤ) : ℚ) := by
      exact_mod_cast hEqAB
    have hprodQ : (((x % y).norm * y.norm : ℤ) : ℚ) < ((y.norm * y.norm : ℤ) : ℚ) := by
      rw [hcast]
      exact hsum'
    exact_mod_cast hprodQ
  nlinarith [hprod, hNpos]

theorem natAbs_norm_mod_lt (x : R) {y : R} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs :=
  Int.ofNat_lt.1 <| by simpa [abs_natCast_norm] using norm_mod_lt x hy

theorem norm_le_norm_mul_left (x : R) {y : R} (hy : y ≠ 0) :
    x.norm.natAbs ≤ (x * y).norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  have hypos : 0 < y.norm := norm_pos.mpr hy
  have hyge : 1 ≤ y.norm.natAbs := by
    apply Int.ofNat_le.mp
    rw [abs_natCast_norm]
    omega
  exact le_mul_of_one_le_right (Nat.zero_le _) hyge

instance instNontrivial : Nontrivial R :=
  ⟨⟨0, 1, by decide⟩⟩

instance : EuclideanDomain R :=
  { (inferInstance : CommRing R), ZsqrtNegTwo.instNontrivial with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by simp [div_def]; rfl
    quotient_mul_add_remainder_eq := fun _ _ => by simp [mod_def]
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a _ hb0 => not_lt_of_ge <| norm_le_norm_mul_left a hb0 }

end ZsqrtNegTwo
