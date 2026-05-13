import Mordell.ZsqrtdBasic

open Zsqrtd
open scoped nonZeroDivisors

namespace Mordell

lemma rat_sub_round_sq_le_quarter (a : ℚ) :
    (a - round a) ^ 2 ≤ 1 / 4 := by
  have h := abs_sub_round a
  have hnonneg : (0 : ℚ) ≤ 1 / 2 := by norm_num
  have hsq : (a - round a) ^ 2 ≤ (1 / 2 : ℚ) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hnonneg] using h
  norm_num at hsq ⊢
  exact hsq

lemma int_round_scaled_sq_le_quarter (A N r : ℤ) (hN : 0 < N) :
    (((r * A - N * round ((((r * A : ℤ) : ℚ) / (N : ℚ))) : ℤ) : ℚ) ^ 2)
      ≤ (N : ℚ) ^ 2 / 4 := by
  let x : ℚ := (((r * A : ℤ) : ℚ) / (N : ℚ))
  have h := rat_sub_round_sq_le_quarter x
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg (N : ℚ))
  calc
    (((r * A - N * round x : ℤ) : ℚ) ^ 2)
        = (N : ℚ) ^ 2 * (x - round x) ^ 2 := by
          dsimp [x]
          norm_num [Int.cast_sub, Int.cast_mul]
          field_simp [ne_of_gt hNq]
    _ ≤ (N : ℚ) ^ 2 * (1 / 4) := hmul
    _ = (N : ℚ) ^ 2 / 4 := by ring

lemma int_scaled_sub_sq_le (B N r m : ℤ) (hN : 0 < N) {C : ℚ}
    (h : ((((r * B : ℤ) : ℚ) / (N : ℚ) - (m : ℚ)) ^ 2) ≤ C) :
    (((r * B - N * m : ℤ) : ℚ) ^ 2) ≤ (N : ℚ) ^ 2 * C := by
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg (N : ℚ))
  calc
    (((r * B - N * m : ℤ) : ℚ) ^ 2)
        = (N : ℚ) ^ 2 * ((((r * B : ℤ) : ℚ) / (N : ℚ) - (m : ℚ)) ^ 2) := by
          norm_num [Int.cast_sub, Int.cast_mul]
          field_simp [ne_of_gt hNq]
    _ ≤ (N : ℚ) ^ 2 * C := hmul

lemma exists_int_two_mul_sub_sq_le_one_nine (x : ℚ) (m : ℤ)
    (hround : |x - m| ≤ (1 / 2 : ℚ))
    (hnot : ¬ (x - m) ^ 2 ≤ (1 / 9 : ℚ)) :
    ∃ m' : ℤ, (2 * x - m') ^ 2 ≤ (1 / 9 : ℚ) := by
  obtain ⟨half_le, le_half⟩ :
      - (1 / 2 : ℚ) ≤ x - m ∧ x - m ≤ 1 / 2 := abs_le.mp hround
  have third_sq : (1 / 3 : ℚ) ^ 2 = 1 / 9 := by norm_num
  have abs_third : |(1 / 3 : ℚ)| = 1 / 3 := by norm_num
  simp only [← third_sq, abs_third, sq_le_sq, abs_le] at ⊢
  simp only [not_le, ← third_sq, abs_third, sq_lt_sq, lt_abs] at hnot
  rcases hnot with hlt | hgt
  · use 2 * m + 1
    norm_num [Int.cast_mul, Int.cast_add, sub_sub, mul_sub]
    constructor <;> linarith
  · use 2 * m - 1
    norm_num [Int.cast_mul, Int.cast_sub, sub_add, mul_sub]
    constructor <;> linarith

lemma rat_sq_le_of_abs_le {x c : ℚ} (hc : 0 ≤ c) (h : |x| ≤ c) :
    x ^ 2 ≤ c ^ 2 := by
  rw [sq_le_sq]
  simpa [abs_of_nonneg hc] using h

lemma exists_int_mul_sub_sq_le_one_twentyfive (x : ℚ) (m : ℤ)
    (hround : |x - m| ≤ (1 / 2 : ℚ)) :
    ∃ (r n : ℤ), r ∈ ({1, 2, 3, 4} : Finset ℤ) ∧
      (r * x - n) ^ 2 ≤ (1 / 25 : ℚ) := by
  let t : ℚ := x - m
  have ht : -(1 / 2 : ℚ) ≤ t ∧ t ≤ 1 / 2 := by
    simpa [t] using abs_le.mp hround
  have hnonneg_or_neg : 0 ≤ t ∨ t < 0 := le_or_gt 0 t
  rcases hnonneg_or_neg with ht0 | htneg
  · by_cases h1 : t ≤ 1 / 5
    · refine ⟨1, m, by simp, ?_⟩
      have habs : |t| ≤ (1 / 5 : ℚ) := abs_le.mpr ⟨by linarith, h1⟩
      have hsq := rat_sq_le_of_abs_le (by norm_num : (0 : ℚ) ≤ 1 / 5) habs
      simpa [t] using hsq
    · by_cases h2 : t ≤ 3 / 10
      · refine ⟨4, 4 * m + 1, by simp, ?_⟩
        have ht_lower : (1 / 5 : ℚ) ≤ t := le_of_lt (lt_of_not_ge h1)
        have habs : |4 * t - 1| ≤ (1 / 5 : ℚ) := abs_le.mpr ⟨by linarith, by linarith⟩
        have hsq := rat_sq_le_of_abs_le (by norm_num : (0 : ℚ) ≤ 1 / 5) habs
        norm_num at hsq ⊢
        convert hsq using 1
        dsimp [t]
        ring
      · by_cases h3 : t ≤ 2 / 5
        · refine ⟨3, 3 * m + 1, by simp, ?_⟩
          have ht_lower : (3 / 10 : ℚ) ≤ t := le_of_lt (lt_of_not_ge h2)
          have habs : |3 * t - 1| ≤ (1 / 5 : ℚ) := abs_le.mpr ⟨by linarith, by linarith⟩
          have hsq := rat_sq_le_of_abs_le (by norm_num : (0 : ℚ) ≤ 1 / 5) habs
          norm_num at hsq ⊢
          convert hsq using 1
          dsimp [t]
          ring
        · refine ⟨2, 2 * m + 1, by simp, ?_⟩
          have ht_lower : (2 / 5 : ℚ) ≤ t := le_of_lt (lt_of_not_ge h3)
          have habs : |2 * t - 1| ≤ (1 / 5 : ℚ) := abs_le.mpr ⟨by linarith, by linarith⟩
          have hsq := rat_sq_le_of_abs_le (by norm_num : (0 : ℚ) ≤ 1 / 5) habs
          norm_num at hsq ⊢
          convert hsq using 1
          dsimp [t]
          ring
  · by_cases h1 : -(1 / 5 : ℚ) ≤ t
    · refine ⟨1, m, by simp, ?_⟩
      have habs : |t| ≤ (1 / 5 : ℚ) := abs_le.mpr ⟨h1, by linarith⟩
      have hsq := rat_sq_le_of_abs_le (by norm_num : (0 : ℚ) ≤ 1 / 5) habs
      simpa [t] using hsq
    · by_cases h2 : -(3 / 10 : ℚ) ≤ t
      · refine ⟨4, 4 * m - 1, by simp, ?_⟩
        have ht_upper : t ≤ -(1 / 5 : ℚ) := le_of_lt (lt_of_not_ge h1)
        have habs : |4 * t + 1| ≤ (1 / 5 : ℚ) := abs_le.mpr ⟨by linarith, by linarith⟩
        have hsq := rat_sq_le_of_abs_le (by norm_num : (0 : ℚ) ≤ 1 / 5) habs
        norm_num at hsq ⊢
        convert hsq using 1
        dsimp [t]
        ring
      · by_cases h3 : -(2 / 5 : ℚ) ≤ t
        · refine ⟨3, 3 * m - 1, by simp, ?_⟩
          have ht_upper : t ≤ -(3 / 10 : ℚ) := le_of_lt (lt_of_not_ge h2)
          have habs : |3 * t + 1| ≤ (1 / 5 : ℚ) := abs_le.mpr ⟨by linarith, by linarith⟩
          have hsq := rat_sq_le_of_abs_le (by norm_num : (0 : ℚ) ≤ 1 / 5) habs
          norm_num at hsq ⊢
          convert hsq using 1
          dsimp [t]
          ring
        · refine ⟨2, 2 * m - 1, by simp, ?_⟩
          have ht_upper : t ≤ -(2 / 5 : ℚ) := le_of_lt (lt_of_not_ge h3)
          have habs : |2 * t + 1| ≤ (1 / 5 : ℚ) := abs_le.mpr ⟨by linarith, by linarith⟩
          have hsq := rat_sq_le_of_abs_le (by norm_num : (0 : ℚ) ≤ 1 / 5) habs
          norm_num at hsq ⊢
          convert hsq using 1
          dsimp [t]
          ring

lemma norm_approx_mul_norm (d r : ℤ) (a b : ℤ√d) (qre qim : ℤ) :
    ((r : ℤ) • a - (⟨qre, qim⟩ : ℤ√d) * b).norm * b.norm =
      (r * (a * star b).re - b.norm * qre) ^ 2 -
        d * (r * (a * star b).im - b.norm * qim) ^ 2 := by
  have hnorm := Zsqrtd.norm_mul (((r : ℤ) • a - (⟨qre, qim⟩ : ℤ√d) * b)) (star b)
  rw [Zsqrtd.norm_conj] at hnorm
  rw [← hnorm]
  simp [Zsqrtd.norm]
  ring

lemma approx_norm_expr_lt (d X Y N : ℤ)
    (hd_nonpos : d ≤ 0) (hd_ge : -6 ≤ d) (hNpos : 0 < N)
    (hX : ((X : ℚ) ^ 2) ≤ (N : ℚ) ^ 2 / 4)
    (hY : ((Y : ℚ) ^ 2) ≤ (N : ℚ) ^ 2 / 9) :
    (X ^ 2 - d * Y ^ 2 : ℤ) < N * N := by
  have hNposQ : (0 : ℚ) < N := by exact_mod_cast hNpos
  have hdneg_nonneg : (0 : ℚ) ≤ -(d : ℚ) := by
    exact_mod_cast (neg_nonneg.mpr hd_nonpos)
  have hdneg_le : -(d : ℚ) ≤ 6 := by
    exact_mod_cast (neg_le_of_neg_le (by simpa using hd_ge) : -d ≤ 6)
  have hYnonneg : (0 : ℚ) ≤ (Y : ℚ) ^ 2 := sq_nonneg _
  have hterm : -(d : ℚ) * (Y : ℚ) ^ 2 ≤ 6 * ((N : ℚ) ^ 2 / 9) := by
    exact mul_le_mul hdneg_le hY hYnonneg (by norm_num)
  have hQ : (((X ^ 2 - d * Y ^ 2 : ℤ) : ℚ) < ((N * N : ℤ) : ℚ)) := by
    norm_num [Int.cast_sub, Int.cast_mul, Int.cast_pow]
    nlinarith [hX, hterm, hNposQ]
  exact_mod_cast hQ

lemma approx_norm_expr_lt_neg_thirteen (X Y N : ℤ)
    (hNpos : 0 < N)
    (hX : ((X : ℚ) ^ 2) ≤ (N : ℚ) ^ 2 / 4)
    (hY : ((Y : ℚ) ^ 2) ≤ (N : ℚ) ^ 2 / 25) :
    (X ^ 2 - (-13 : ℤ) * Y ^ 2 : ℤ) < N * N := by
  have hNposQ : (0 : ℚ) < N := by exact_mod_cast hNpos
  have hQ : (((X ^ 2 - (-13 : ℤ) * Y ^ 2 : ℤ) : ℚ) <
      ((N * N : ℤ) : ℚ)) := by
    norm_num [Int.cast_sub, Int.cast_mul, Int.cast_pow]
    nlinarith [hX, hY, hNposQ]
  exact_mod_cast hQ

lemma exists_q_r_of_neg_six_le (d : ℤ) (hd_neg : d < 0) (hd_ge : -6 ≤ d)
    (a : ℤ√d) {b : ℤ√d} (hb : b ≠ 0) :
    ∃ (q : ℤ√d) (r : ℤ), r ∈ ({1, 2} : Finset ℤ) ∧
      AbsoluteValue.abs (Algebra.norm ℤ ((r : ℤ) • a - q * b)) <
        AbsoluteValue.abs (Algebra.norm ℤ b) := by
  let N : ℤ := b.norm
  let A : ℤ := (a * star b).re
  let B : ℤ := (a * star b).im
  have hd_nonpos : d ≤ 0 := le_of_lt hd_neg
  have hNpos : 0 < N := by
    have hnonneg : 0 ≤ b.norm := Zsqrtd.norm_nonneg hd_nonpos b
    have hne : b.norm ≠ 0 := by
      intro h0
      exact hb ((Zsqrtd.norm_eq_zero_iff hd_neg b).mp h0)
    exact lt_of_le_of_ne hnonneg hne.symm
  let xB : ℚ := (B : ℚ) / (N : ℚ)
  let mB : ℤ := round xB
  by_cases hsmall : (xB - (mB : ℚ)) ^ 2 ≤ (1 / 9 : ℚ)
  · let qre : ℤ := round (((1 * A : ℤ) : ℚ) / (N : ℚ))
    let q : ℤ√d := ⟨qre, mB⟩
    refine ⟨q, 1, by simp, ?_⟩
    let c : ℤ√d := ((1 : ℤ) : ℤ) • a - q * b
    have hX :
        ((((1 * A - N * qre : ℤ) : ℚ) ^ 2)) ≤ (N : ℚ) ^ 2 / 4 := by
      simpa [qre] using int_round_scaled_sq_le_quarter A N 1 hNpos
    have hY :
        ((((1 * B - N * mB : ℤ) : ℚ) ^ 2)) ≤ (N : ℚ) ^ 2 / 9 := by
      have h := int_scaled_sub_sq_le B N 1 mB hNpos (C := (1 / 9 : ℚ))
        (by simpa [xB] using hsmall)
      simpa [one_mul] using h
    have hexpr :
        ((1 * A - N * qre) ^ 2 - d * (1 * B - N * mB) ^ 2 : ℤ) < N * N :=
      approx_norm_expr_lt d (1 * A - N * qre) (1 * B - N * mB) N
        hd_nonpos hd_ge hNpos hX hY
    have hprod :
        c.norm * N = (1 * A - N * qre) ^ 2 - d * (1 * B - N * mB) ^ 2 := by
      simpa [c, q, qre, mB, A, B, N] using norm_approx_mul_norm d 1 a b qre mB
    have hc_lt : c.norm < N := by
      have hprod_lt : c.norm * N < N * N := by
        rw [hprod]
        exact hexpr
      nlinarith [hprod_lt, hNpos]
    have hc_nonneg : 0 ≤ c.norm := Zsqrtd.norm_nonneg hd_nonpos c
    change AbsoluteValue.abs (Algebra.norm ℤ c) < AbsoluteValue.abs (Algebra.norm ℤ b)
    change |Algebra.norm ℤ c| < |Algebra.norm ℤ b|
    rw [zsqrtd_algebra_norm d c, zsqrtd_algebra_norm d b,
      abs_of_nonneg hc_nonneg, abs_of_nonneg hNpos.le]
    exact hc_lt
  · obtain ⟨m', hm'⟩ := exists_int_two_mul_sub_sq_le_one_nine xB mB
      (abs_sub_round xB) hsmall
    let qre : ℤ := round (((2 * A : ℤ) : ℚ) / (N : ℚ))
    let q : ℤ√d := ⟨qre, m'⟩
    refine ⟨q, 2, by simp, ?_⟩
    let c : ℤ√d := ((2 : ℤ) : ℤ) • a - q * b
    have hX :
        ((((2 * A - N * qre : ℤ) : ℚ) ^ 2)) ≤ (N : ℚ) ^ 2 / 4 := by
      simpa [qre] using int_round_scaled_sq_le_quarter A N 2 hNpos
    have hm'' :
        ((((2 * B : ℤ) : ℚ) / (N : ℚ) - (m' : ℚ)) ^ 2) ≤ (1 / 9 : ℚ) := by
      have harg : (((2 * B : ℤ) : ℚ) / (N : ℚ) - (m' : ℚ)) = 2 * xB - (m' : ℚ) := by
        dsimp [xB]
        norm_num [Int.cast_mul]
        ring
      rw [harg]
      exact hm'
    have hY :
        ((((2 * B - N * m' : ℤ) : ℚ) ^ 2)) ≤ (N : ℚ) ^ 2 / 9 := by
      have h := int_scaled_sub_sq_le B N 2 m' hNpos (C := (1 / 9 : ℚ)) hm''
      simpa using h
    have hexpr :
        ((2 * A - N * qre) ^ 2 - d * (2 * B - N * m') ^ 2 : ℤ) < N * N :=
      approx_norm_expr_lt d (2 * A - N * qre) (2 * B - N * m') N
        hd_nonpos hd_ge hNpos hX hY
    have hprod :
        c.norm * N = (2 * A - N * qre) ^ 2 - d * (2 * B - N * m') ^ 2 := by
      simpa [c, q, qre, A, B, N] using norm_approx_mul_norm d 2 a b qre m'
    have hc_lt : c.norm < N := by
      have hprod_lt : c.norm * N < N * N := by
        rw [hprod]
        exact hexpr
      nlinarith [hprod_lt, hNpos]
    have hc_nonneg : 0 ≤ c.norm := Zsqrtd.norm_nonneg hd_nonpos c
    change AbsoluteValue.abs (Algebra.norm ℤ c) < AbsoluteValue.abs (Algebra.norm ℤ b)
    change |Algebra.norm ℤ c| < |Algebra.norm ℤ b|
    rw [zsqrtd_algebra_norm d c, zsqrtd_algebra_norm d b,
      abs_of_nonneg hc_nonneg, abs_of_nonneg hNpos.le]
    exact hc_lt

lemma exists_q_r_of_neg_thirteen
    (a : ℤ√(-13 : ℤ)) {b : ℤ√(-13 : ℤ)} (hb : b ≠ 0) :
    ∃ (q : ℤ√(-13 : ℤ)) (r : ℤ), r ∈ ({1, 2, 3, 4} : Finset ℤ) ∧
      AbsoluteValue.abs (Algebra.norm ℤ ((r : ℤ) • a - q * b)) <
        AbsoluteValue.abs (Algebra.norm ℤ b) := by
  let N : ℤ := b.norm
  let A : ℤ := (a * star b).re
  let B : ℤ := (a * star b).im
  have hNpos : 0 < N := by
    have hnonneg : 0 ≤ b.norm := Zsqrtd.norm_nonneg (by norm_num : (-13 : ℤ) ≤ 0) b
    have hne : b.norm ≠ 0 := by
      intro h0
      exact hb ((Zsqrtd.norm_eq_zero_iff (by norm_num : (-13 : ℤ) < 0) b).mp h0)
    exact lt_of_le_of_ne hnonneg hne.symm
  let xB : ℚ := (B : ℚ) / (N : ℚ)
  let mB : ℤ := round xB
  obtain ⟨r, m', hr, hm'⟩ :=
    exists_int_mul_sub_sq_le_one_twentyfive xB mB (abs_sub_round xB)
  let qre : ℤ := round (((r * A : ℤ) : ℚ) / (N : ℚ))
  let q : ℤ√(-13 : ℤ) := ⟨qre, m'⟩
  refine ⟨q, r, hr, ?_⟩
  let c : ℤ√(-13 : ℤ) := ((r : ℤ) : ℤ) • a - q * b
  have hX :
      ((((r * A - N * qre : ℤ) : ℚ) ^ 2)) ≤ (N : ℚ) ^ 2 / 4 := by
    simpa [qre] using int_round_scaled_sq_le_quarter A N r hNpos
  have hm'' :
      ((((r * B : ℤ) : ℚ) / (N : ℚ) - (m' : ℚ)) ^ 2) ≤ (1 / 25 : ℚ) := by
    have harg : (((r * B : ℤ) : ℚ) / (N : ℚ) - (m' : ℚ)) =
        (r : ℚ) * xB - (m' : ℚ) := by
      dsimp [xB]
      norm_num [Int.cast_mul]
      ring
    rw [harg]
    exact hm'
  have hY :
      ((((r * B - N * m' : ℤ) : ℚ) ^ 2)) ≤ (N : ℚ) ^ 2 / 25 := by
    have h := int_scaled_sub_sq_le B N r m' hNpos (C := (1 / 25 : ℚ)) hm''
    simpa using h
  have hexpr :
      ((r * A - N * qre) ^ 2 - (-13 : ℤ) * (r * B - N * m') ^ 2 : ℤ) < N * N :=
    approx_norm_expr_lt_neg_thirteen (r * A - N * qre) (r * B - N * m') N
      hNpos hX hY
  have hprod :
      c.norm * N =
        (r * A - N * qre) ^ 2 - (-13 : ℤ) * (r * B - N * m') ^ 2 := by
    simpa [c, q, qre, A, B, N] using norm_approx_mul_norm (-13) r a b qre m'
  have hc_lt : c.norm < N := by
    have hprod_lt : c.norm * N < N * N := by
      rw [hprod]
      exact hexpr
    nlinarith [hprod_lt, hNpos]
  have hc_nonneg : 0 ≤ c.norm := Zsqrtd.norm_nonneg (by norm_num : (-13 : ℤ) ≤ 0) c
  change AbsoluteValue.abs (Algebra.norm ℤ c) < AbsoluteValue.abs (Algebra.norm ℤ b)
  change |Algebra.norm ℤ c| < |Algebra.norm ℤ b|
  rw [zsqrtd_algebra_norm (-13) c, zsqrtd_algebra_norm (-13) b,
    abs_of_nonneg hc_nonneg, abs_of_nonneg hNpos.le]
  exact hc_lt

end Mordell
