import Mordell.ClassGroupApprox
import Mordell.Dedekind

open Zsqrtd
open scoped nonZeroDivisors

namespace Mordell

private lemma cube_re (a b d : ℤ) :
    ((⟨a, b⟩ : ℤ√d) ^ 3).re = a * (3 * d * b ^ 2 + a ^ 2) := by
  simp [pow_succ]
  ring

private lemma cube_im (a b d : ℤ) :
    ((⟨a, b⟩ : ℤ√d) ^ 3).im = b * (d * b ^ 2 + 3 * a ^ 2) := by
  simp [pow_succ]
  ring

private lemma int_eq_one_or_neg_one_of_mul_eq_one {a b : ℤ} (h : a * b = 1) :
    a = 1 ∨ a = -1 := by
  have hunit : IsUnit a := ⟨⟨a, b, h, by simpa [mul_comm] using h⟩, rfl⟩
  simpa [Int.isUnit_iff] using hunit

lemma int_eq_of_cube_eq {x n : ℤ} (h : x ^ 3 = n ^ 3) : x = n := by
  exact (show Odd (3 : ℕ) by decide).pow_injective h

/-- 理想下降背后的初等分解。 -/
theorem factor_y_sq_sub_d (d y : ℤ) :
    ((y ^ 2 - d : ℤ) : ℤ√d) = (⟨y, 1⟩ : ℤ√d) * ⟨y, -1⟩ := by
  ext
  · simp [pow_two]
    ring
  · simp [pow_two]

/-- `ℤ√(-1)` 中的单位 `√-1`。 -/
def sqrtNegOneUnit : (ℤ√(-1 : ℤ))ˣ where
  val := ⟨0, 1⟩
  inv := ⟨0, -1⟩
  val_inv := by
    ext <;> simp
  inv_val := by
    ext <;> simp

/-- `ℤ√(-1)` 中的单位 `-√-1`。 -/
def negSqrtNegOneUnit : (ℤ√(-1 : ℤ))ˣ where
  val := ⟨0, -1⟩
  inv := ⟨0, 1⟩
  val_inv := by
    ext <;> simp
  inv_val := by
    ext <;> simp

theorem zsqrtd_units_eq_one_or_neg_one {d : ℤ} (hd : d ≤ -2) (u : (ℤ√d)ˣ) :
    u = 1 ∨ u = -1 := by
  let a : ℤ := (u : ℤ√d).re
  let b : ℤ := (u : ℤ√d).im
  have hnorm : (u : ℤ√d).norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (by linarith) (u : ℤ√d)).mpr u.isUnit
  have hnorm' : a * a - d * b * b = 1 := by
    simpa [a, b, Zsqrtd.norm, mul_assoc] using hnorm
  have hb : b = 0 := by
    by_contra hb
    have hbpos : 0 < b * b := mul_self_pos.mpr hb
    nlinarith
  have ha_sq : a * a = 1 := by
    rw [hb] at hnorm'
    nlinarith
  have ha_cases : a = 1 ∨ a = -1 :=
    int_eq_one_or_neg_one_of_mul_eq_one ha_sq
  rcases ha_cases with ha | ha
  · left
    ext <;> simp [a, b, ha, hb]
  · right
    ext <;> simp [a, b, ha, hb]

theorem zsqrtd_units_neg_one_cases (u : (ℤ√(-1 : ℤ))ˣ) :
    u = 1 ∨ u = -1 ∨ u = sqrtNegOneUnit ∨ u = negSqrtNegOneUnit := by
  let a : ℤ := (u : ℤ√(-1 : ℤ)).re
  let b : ℤ := (u : ℤ√(-1 : ℤ)).im
  have hnorm : (u : ℤ√(-1 : ℤ)).norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (by norm_num) (u : ℤ√(-1 : ℤ))).mpr u.isUnit
  have hnorm' : a * a + b * b = 1 := by
    simpa [a, b, Zsqrtd.norm, mul_assoc] using hnorm
  have hb_le : b ≤ 1 := by nlinarith [sq_nonneg a]
  have hb_ge : -1 ≤ b := by nlinarith [sq_nonneg a]
  have hb_cases : b = -1 ∨ b = 0 ∨ b = 1 := by omega
  rcases hb_cases with hb | hb | hb
  · rw [hb] at hnorm'
    have ha : a = 0 := by nlinarith [sq_nonneg a]
    right; right; right
    ext <;> simp [a, b, ha, hb, negSqrtNegOneUnit]
  · rw [hb] at hnorm'
    have ha_sq : a * a = 1 := by nlinarith
    rcases int_eq_one_or_neg_one_of_mul_eq_one ha_sq with ha | ha
    · left
      ext <;> simp [a, b, ha, hb]
    · right; left
      ext <;> simp [a, b, ha, hb]
  · rw [hb] at hnorm'
    have ha : a = 0 := by nlinarith [sq_nonneg a]
    right; right; left
    ext <;> simp [a, b, ha, hb, sqrtNegOneUnit]

/-- 对 `d ≤ -1`，`ℤ√d` 的每个单位都是立方。 -/
theorem zsqrtd_units_cubes {d : ℤ} (hd : d ≤ -1) (u : (ℤ√d)ˣ) :
    ∃ v : (ℤ√d)ˣ, u = v ^ 3 := by
  rcases lt_or_eq_of_le hd with hdlt | rfl
  · have hd2 : d ≤ -2 := by omega
    rcases zsqrtd_units_eq_one_or_neg_one hd2 u with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by ext <;> simp [pow_succ]⟩
  · use u⁻¹
    rcases zsqrtd_units_neg_one_cases u with rfl | rfl | rfl | rfl
    · ext <;> simp
    · ext <;> simp [pow_succ]
    · ext <;> simp [sqrtNegOneUnit, pow_succ]
    · ext <;> simp [negSqrtNegOneUnit, pow_succ]

/--
Mordell 下降法中的类群消去。

如果类数与 `3` 互素，那么一个立方为主理想的理想本身也是主理想。
这一步独立于具体二次阶的计算，是 Lean3 论证中可复用部分的 Lean4 版本。
-/
theorem ideal_isPrincipal_of_cube_isPrincipal
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {I : Ideal R} (hI0 : I ∈ (Ideal R)⁰)
    (hcl : Nat.gcd 3 (Nat.card (ClassGroup R)) = 1)
    (hI3 : (I ^ 3).IsPrincipal) :
    I.IsPrincipal := by
  have hI_ne : I ≠ 0 := by
    simpa [mem_nonZeroDivisors_iff_ne_zero] using hI0
  have hI3_0 : I ^ 3 ∈ (Ideal R)⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact pow_ne_zero 3 hI_ne
  let C : ClassGroup R := ClassGroup.mk0 ⟨I, hI0⟩
  have hC3 : C ^ 3 = 1 := by
    change ClassGroup.mk0 ⟨I, hI0⟩ ^ 3 = 1
    rw [← map_pow (ClassGroup.mk0 : (Ideal R)⁰ →* ClassGroup R)]
    exact (ClassGroup.mk0_eq_one_iff hI3_0).mpr hI3
  have hCgcd : C ^ Nat.gcd 3 (Nat.card (ClassGroup R)) = 1 := by
    have hC3_dvd : orderOf C ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hC3
    have hCcard_dvd : orderOf C ∣ Nat.card (ClassGroup R) := orderOf_dvd_natCard C
    exact orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_gcd hC3_dvd hCcard_dvd)
  have hC : C = 1 := by
    simpa [hcl] using hCgcd
  exact (ClassGroup.mk0_eq_one_iff hI0).mp hC

/--
如果由 `y + √d` 生成的理想是某个主理想的立方，那么 `y + √d` 本身也是立方。
唯一涉及单位的问题由 `zsqrtd_units_cubes` 处理。
-/
theorem cube_root_of_principal_cube_span (d : ℤ) (hd : d ≤ -1) (y : ℤ)
    [IsDomain (ℤ√d)]
    {I : Ideal (ℤ√d)}
    (hI : Ideal.span ({(⟨y, 1⟩ : ℤ√d)} : Set (ℤ√d)) = I ^ 3)
    (hI_principal : I.IsPrincipal) :
    ∃ z : ℤ√d, z ^ 3 = (⟨y, 1⟩ : ℤ√d) := by
  letI : I.IsPrincipal := hI_principal
  let w : ℤ√d := Submodule.IsPrincipal.generator I
  have hw : Ideal.span ({w} : Set (ℤ√d)) = I := by
    simp [w]
  have hspan :
      Ideal.span ({(⟨y, 1⟩ : ℤ√d)} : Set (ℤ√d)) =
        Ideal.span ({w ^ 3} : Set (ℤ√d)) := by
    calc
      Ideal.span ({(⟨y, 1⟩ : ℤ√d)} : Set (ℤ√d)) = I ^ 3 := hI
      _ = (Ideal.span ({w} : Set (ℤ√d))) ^ 3 := by rw [hw]
      _ = Ideal.span ({w ^ 3} : Set (ℤ√d)) := by rw [Ideal.span_singleton_pow]
  have hassoc : Associated (⟨y, 1⟩ : ℤ√d) (w ^ 3) :=
    (Ideal.span_singleton_eq_span_singleton).mp hspan
  rcases hassoc with ⟨u, hu⟩
  rcases zsqrtd_units_cubes hd u with ⟨v, hv⟩
  subst u
  refine ⟨w * ↑(v⁻¹), ?_⟩
  calc
    (w * ↑(v⁻¹)) ^ 3 = w ^ 3 * ↑((v⁻¹) ^ 3) := by
      simp [mul_pow]
    _ = ((⟨y, 1⟩ : ℤ√d) * ↑(v ^ 3)) * ↑((v⁻¹) ^ 3) := by
      rw [← hu]
    _ = (⟨y, 1⟩ : ℤ√d) := by
      have hvv : (↑(v ^ 3) : ℤ√d) * ↑((v⁻¹) ^ 3) = 1 := by
        rw [← Units.val_mul]
        simp
      rw [mul_assoc, hvv, mul_one]

/--
Mordell 下降法中理想论层面的立方步骤。

如果由 `y + √d` 与 `y - √d` 生成的两个主理想互素，那么分解
`(y + √d)(y - √d) = x^3` 会迫使 `span {y + √d}` 成为某个理想的立方。
-/
theorem span_y_add_sqrtd_eq_ideal_cube_of_coprime
    (d x y : ℤ) [IsDomain (ℤ√d)] [IsDedekindDomain (ℤ√d)]
    (hcop : IsCoprime
      (Ideal.span ({(⟨y, 1⟩ : ℤ√d)} : Set (ℤ√d)))
      (Ideal.span ({(⟨y, -1⟩ : ℤ√d)} : Set (ℤ√d))))
    (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ I : Ideal (ℤ√d),
      Ideal.span ({(⟨y, 1⟩ : ℤ√d)} : Set (ℤ√d)) = I ^ 3 := by
  have hsub : y ^ 2 - d = x ^ 3 := by linarith
  have hmul_elem :
      (⟨y, 1⟩ : ℤ√d) * ⟨y, -1⟩ = (x : ℤ√d) ^ 3 := by
    rw [← factor_y_sq_sub_d]
    exact_mod_cast hsub
  have hmul_ideal :
      Ideal.span ({(⟨y, 1⟩ : ℤ√d)} : Set (ℤ√d)) *
        Ideal.span ({(⟨y, -1⟩ : ℤ√d)} : Set (ℤ√d)) =
          (Ideal.span ({(x : ℤ√d)} : Set (ℤ√d))) ^ 3 := by
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_pow, hmul_elem]
  exact exists_eq_pow_of_mul_eq_pow_of_coprime hcop hmul_ideal

/--
一个可复用、非公理化的下降法接口。

该定理封装了目前 Lean4 中已经可用的所有通用代数数论部分：理想分解、
类群消去以及单位的立方。要把它用于具体的 `d`，还需要证明 `ℤ√d` 的
Dedekind 整环实例和理想互素假设。
-/
theorem exists_cube_root_y_add_sqrtd_of_ideal_coprime
    (d : ℤ) (hd : d ≤ -1)
    [IsDomain (ℤ√d)] [IsDedekindDomain (ℤ√d)]
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (x y : ℤ)
    (hcop : IsCoprime
      (Ideal.span ({(⟨y, 1⟩ : ℤ√d)} : Set (ℤ√d)))
      (Ideal.span ({(⟨y, -1⟩ : ℤ√d)} : Set (ℤ√d))))
    (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ z : ℤ√d, z ^ 3 = (⟨y, 1⟩ : ℤ√d) := by
  obtain ⟨I, hI⟩ := span_y_add_sqrtd_eq_ideal_cube_of_coprime d x y hcop h_eqn
  have hy_ne : (⟨y, 1⟩ : ℤ√d) ≠ 0 := by
    intro h
    have := congrArg Zsqrtd.im h
    norm_num at this
  have hI0 : I ∈ (Ideal (ℤ√d))⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hzero
    have hspan_zero :
        Ideal.span ({(⟨y, 1⟩ : ℤ√d)} : Set (ℤ√d)) = 0 := by
      simpa [hzero] using hI
    exact hy_ne (Ideal.span_singleton_eq_bot.mp hspan_zero)
  have hI3_principal : (I ^ 3).IsPrincipal := by
    rw [← hI]
    infer_instance
  have hcl' : Nat.gcd 3 (Nat.card (ClassGroup (ℤ√d))) = 1 := by
    have hdlt : d < 0 := by omega
    have hcard : quadClassNumber d = Nat.card (ClassGroup (ℤ√d)) := by
      simp [quadClassNumber, hdlt]
    rw [hcard] at hcl
    rwa [Nat.gcd_comm] at hcl
  have hI_principal : I.IsPrincipal :=
    ideal_isPrincipal_of_cube_isPrincipal hI0 hcl' hI3_principal
  exact cube_root_of_principal_cube_span d hd y hI hI_principal

/--
当 `d mod 8 ∈ {2,3,5,6,7}` 时，不存在偶数 `x` 满足 `y^2 - d = x^3`。
-/
lemma x_odd_two_three_aux {x y d : ℤ}
    (hd : (d : ZMod 8) ∈ ({2, 3, 5, 6, 7} : Finset (ZMod 8)))
    (h_eqn : y ^ 2 - d = x ^ 3) :
    ¬ Even x := by
  rintro ⟨X, rfl⟩
  have h_int : y ^ 2 - d = (2 * X) ^ 3 := by
    simpa [two_mul] using h_eqn
  have hcast : ((y ^ 2 - d : ℤ) : ZMod 8) = (((2 * X) ^ 3 : ℤ) : ZMod 8) := by
    rw [h_int]
  have h_eqn_mod :
      (y : ZMod 8) ^ 2 - (d : ZMod 8) = (2 * (X : ZMod 8)) ^ 3 := by
    simpa [Int.cast_sub, Int.cast_pow, Int.cast_mul] using hcast
  have hbad : ¬ ∃ Y XX D : ZMod 8,
      D ∈ ({2, 3, 5, 6, 7} : Finset (ZMod 8)) ∧
        Y ^ 2 - D = (2 * XX) ^ 3 := by
    decide
  exact hbad ⟨(y : ZMod 8), (X : ZMod 8), (d : ZMod 8), hd, h_eqn_mod⟩

/-- 若 `d % 4 = 2 ∨ d % 4 = 3`，则不存在偶数 `x` 满足 `y^2 - d = x^3`。 -/
lemma x_odd_two_three {x y d : ℤ}
    (hd : d % 4 = 2 ∨ d % 4 = 3)
    (h_eqn : y ^ 2 - d = x ^ 3) :
    ¬ Even x := by
  refine x_odd_two_three_aux ?_ h_eqn
  rcases hd with hd | hd
  · have hmem : ∀ D : ZMod 8,
        4 * D + 2 ∈ ({2, 3, 5, 6, 7} : Finset (ZMod 8)) := by
      decide
    rw [← Int.mul_ediv_add_emod d 4, hd]
    simpa [Int.cast_add, Int.cast_mul] using hmem ((d / 4 : ℤ) : ZMod 8)
  · have hmem : ∀ D : ZMod 8,
        4 * D + 3 ∈ ({2, 3, 5, 6, 7} : Finset (ZMod 8)) := by
      decide
    rw [← Int.mul_ediv_add_emod d 4, hd]
    simpa [Int.cast_add, Int.cast_mul] using hmem ((d / 4 : ℤ) : ZMod 8)

/--
理想互素证明所需的纯整数输入。

如果一个整数同时整除 `4d` 和 `y^2 - d = x^3`，那么它是单位。
-/
lemma int_isUnit_of_dvd_four_mul_d_of_dvd_y_sq_sub_d {x y d n : ℤ}
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (h_eqn : y ^ 2 - d = x ^ 3)
    (hd4 : n ∣ d * 2 ^ 2)
    (hyd : n ∣ y ^ 2 - d) :
    IsUnit n := by
  have hnot_even_rhs : ¬ Even (y ^ 2 - d) := by
    have hxodd : ¬ Even x := x_odd_two_three h_mod h_eqn
    rw [h_eqn]
    intro hx3_even
    have hx3_dvd : (2 : ℤ) ∣ x ^ 3 := even_iff_two_dvd.mp hx3_even
    have hx_dvd : (2 : ℤ) ∣ x := Prime.dvd_of_dvd_pow Int.prime_two hx3_dvd
    exact hxodd (even_iff_two_dvd.mpr hx_dvd)
  have hn_not_two : ¬ (2 : ℤ) ∣ n := by
    intro hn2
    exact hnot_even_rhs (Dvd.dvd.even (hn2.trans hyd) (by norm_num : Even (2 : ℤ)))
  have hn_coprime_two : IsCoprime n (2 : ℤ) := by
    exact (Int.prime_two.coprime_iff_not_dvd.mpr hn_not_two).symm
  have hn_d : n ∣ d := by
    have hn_coprime_four : IsCoprime n ((2 : ℤ) ^ 2) := hn_coprime_two.pow_right
    exact hn_coprime_four.dvd_of_dvd_mul_right
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hd4)
  have hn_squarefree : Squarefree n :=
    Squarefree.squarefree_of_dvd hn_d h_sqf
  have hn_y_sq : n ∣ y ^ 2 := by
    have hsum : n ∣ (y ^ 2 - d) + d := dvd_add hyd hn_d
    simpa using hsum
  have hn_y : n ∣ y :=
    (hn_squarefree.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp hn_y_sq
  have hn_x_cube : n ∣ x ^ 3 := by
    simpa [h_eqn] using hyd
  have hn_x : n ∣ x :=
    (hn_squarefree.dvd_pow_iff_dvd (by norm_num : (3 : ℕ) ≠ 0)).mp hn_x_cube
  have hn_sq_y_sq : n ^ 2 ∣ y ^ 2 :=
    pow_dvd_pow_of_dvd hn_y 2
  have hn_sq_x_cube : n ^ 2 ∣ x ^ 3 :=
    (pow_dvd_pow_of_dvd hn_x 2).trans (pow_dvd_pow x (by norm_num : 2 ≤ 3))
  have hn_sq_d : n ^ 2 ∣ d := by
    have hsub : n ^ 2 ∣ y ^ 2 - x ^ 3 := dvd_sub hn_sq_y_sq hn_sq_x_cube
    convert hsub using 1
    nlinarith
  exact h_sqf n (by simpa [pow_two] using hn_sq_d)

/--
把整数公共因子计算表述为 Bezout 命题。

在 Mordell 同余条件和无平方因子假设下，`4d` 与 `y^2 - d` 在 `ℤ` 中互素。
-/
lemma int_isCoprime_four_mul_d_y_sq_sub_d {x y d : ℤ}
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (h_eqn : y ^ 2 - d = x ^ 3) :
    IsCoprime (d * 2 ^ 2) (y ^ 2 - d) := by
  refine EuclideanDomain.isCoprime_of_dvd ?_ ?_
  · rintro ⟨hd4, _⟩
    have hd : d = 0 := by nlinarith
    subst d
    norm_num at h_mod
  · intro z hz_nonunit _ hz_d hz_y
    exact (mem_nonunits_iff.mp hz_nonunit)
      (int_isUnit_of_dvd_four_mul_d_of_dvd_y_sq_sub_d h_mod h_sqf h_eqn hz_d hz_y)

/--
由 `y + √d` 与 `y - √d` 生成的主理想互素。

证明把理想命题化归为 `4d` 与 `y^2 - d` 的整数 Bezout 组合：
理想和包含这两个整数元素，因此也包含 `1`。
-/
theorem span_y_add_sqrtd_coprime
    (d x y : ℤ)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (h_eqn : y ^ 2 = x ^ 3 + d) :
    IsCoprime
      (Ideal.span ({(⟨y, 1⟩ : ℤ√d)} : Set (ℤ√d)))
      (Ideal.span ({(⟨y, -1⟩ : ℤ√d)} : Set (ℤ√d))) := by
  let R := ℤ√d
  let I : Ideal R := Ideal.span ({(⟨y, 1⟩ : R)} : Set R)
  let J : Ideal R := Ideal.span ({(⟨y, -1⟩ : R)} : Set R)
  let K : Ideal R := I ⊔ J
  have hsub : y ^ 2 - d = x ^ 3 := by linarith
  obtain ⟨u, v, huv⟩ := int_isCoprime_four_mul_d_y_sq_sub_d h_mod h_sqf hsub
  rw [Ideal.isCoprime_iff_sup_eq]
  change K = ⊤
  refine K.eq_top_iff_one.mpr ?_
  have haI : (⟨y, 1⟩ : R) ∈ I := by
    exact Ideal.subset_span (by simp)
  have hbJ : (⟨y, -1⟩ : R) ∈ J := by
    exact Ideal.subset_span (by simp)
  have haK : (⟨y, 1⟩ : R) ∈ K := Ideal.mem_sup_left haI
  have hbK : (⟨y, -1⟩ : R) ∈ K := Ideal.mem_sup_right hbJ
  have hdiff : (⟨0, 2⟩ : R) ∈ K := by
    convert K.sub_mem haK hbK using 1
    ext
    all_goals dsimp [R]
    all_goals simp
  have hfour_d : (((d * 2 ^ 2 : ℤ) : R)) ∈ K := by
    have hmul : (⟨0, 2⟩ : R) * (⟨0, 2⟩ : R) ∈ K :=
      K.mul_mem_left _ hdiff
    have hfour_eq :
        (((d * 2 ^ 2 : ℤ) : R)) = (⟨0, 2⟩ : R) * (⟨0, 2⟩ : R) := by
      ext
      all_goals dsimp [R]
      all_goals simp
      all_goals ring_nf
    rwa [hfour_eq]
  have hyd : (((y ^ 2 - d : ℤ) : R)) ∈ K := by
    have hmul : (⟨y, 1⟩ : R) * (⟨y, -1⟩ : R) ∈ K :=
      K.mul_mem_left _ hbK
    rw [factor_y_sq_sub_d]
    exact hmul
  have hleft : (u : R) * ((d * 2 ^ 2 : ℤ) : R) ∈ K :=
    K.mul_mem_left _ hfour_d
  have hright : (v : R) * ((y ^ 2 - d : ℤ) : R) ∈ K :=
    K.mul_mem_left _ hyd
  have hsum :
      (u : R) * ((d * 2 ^ 2 : ℤ) : R) +
        (v : R) * ((y ^ 2 - d : ℤ) : R) ∈ K :=
    K.add_mem hleft hright
  have hcomb_eq :
      (u : R) * ((d * 2 ^ 2 : ℤ) : R) +
        (v : R) * ((y ^ 2 - d : ℤ) : R) = 1 := by
    ext
    · dsimp [R]
      simpa [pow_two, Int.cast_add, Int.cast_mul] using huv
    · dsimp [R]
      simp [pow_two]
  rwa [hcomb_eq] at hsum

/--
假设已有 `ℤ√d` 的 Dedekind 整环实例时，不使用 Mordell 专用公理的通用立方根下降。
-/
theorem exists_cube_root_y_add_sqrtd_of_dedekind
    (d : ℤ) (hd : d ≤ -1)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    [IsDomain (ℤ√d)] [IsDedekindDomain (ℤ√d)]
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ z : ℤ√d, z ^ 3 = (⟨y, 1⟩ : ℤ√d) := by
  exact exists_cube_root_y_add_sqrtd_of_ideal_coprime d hd hcl x y
    (span_y_add_sqrtd_coprime d x y h_mod h_sqf h_eqn) h_eqn


theorem exists_cube_root_y_add_sqrtd (d : ℤ) (hd : d ≤ -1)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ z : ℤ√d, z ^ 3 = (⟨y, 1⟩ : ℤ√d) := by
  haveI : IsDedekindDomain (ℤ√d) :=
    zsqrtd_isDedekindDomain_of_squarefree_mod d h_mod h_sqf
  exact exists_cube_root_y_add_sqrtd_of_dedekind d hd h_mod h_sqf hcl x y h_eqn

/--
Mordell 下降法最后的系数比较步骤。

如果 `y + √d` 在 `ℤ√d` 中是立方，那么该立方的实部给出参数 `m`，
而虚部方程迫使另一个系数为 `±1`。
-/
theorem mordell_arithmetic_of_cube {d y : ℤ} {z : ℤ√d}
    (hz : z ^ 3 = (⟨y, 1⟩ : ℤ√d)) :
    ∃ m : ℤ, (d = 1 - 3 * m ^ 2 ∨ d = -1 - 3 * m ^ 2) ∧
      y = m * (3 * d + m ^ 2) := by
  let m : ℤ := z.re
  let n : ℤ := z.im
  have hz' : (⟨m, n⟩ : ℤ√d) ^ 3 = (⟨y, 1⟩ : ℤ√d) := by
    simpa [m, n] using hz
  have h_re : m * (3 * d * n ^ 2 + m ^ 2) = y := by
    simpa [cube_re m n d] using congrArg (fun w : ℤ√d => w.re) hz'
  have h_im : n * (d * n ^ 2 + 3 * m ^ 2) = 1 := by
    simpa [cube_im m n d] using congrArg (fun w : ℤ√d => w.im) hz'
  rcases int_eq_one_or_neg_one_of_mul_eq_one h_im with hn | hn
  · refine ⟨m, Or.inl ?_, ?_⟩
    · rw [hn] at h_im
      nlinarith
    · rw [hn] at h_re
      nlinarith
  · refine ⟨m, Or.inr ?_, ?_⟩
    · rw [hn] at h_im
      nlinarith
    · rw [hn] at h_re
      nlinarith

/--
Mordell 方程 `y^2 = x^3 + d` 的整数解。

如果类数不被 `3` 整除，那么解的形式必定为
`y = m(3d + m^2)`，其中 `m : ℤ` 满足 `d = -3m^2 ± 1`。
-/
theorem mordell_d (d : ℤ) (hd : d ≤ -1)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ m : ℤ, (d = 1 - 3 * m ^ 2 ∨ d = -1 - 3 * m ^ 2) ∧
      y = m * (3 * d + m ^ 2) := by
  obtain ⟨z, hz⟩ := exists_cube_root_y_add_sqrtd d hd h_mod h_sqf hcl x y h_eqn
  exact mordell_arithmetic_of_cube hz

/--
在已有理想互素性时，一个非公理化的 Mordell 下降定理。

对于已经证明类群消去输入，以及 `span {y + √d}` 与 `span {y - √d}` 互素性的
具体 `d`，应使用这个版本。
-/
theorem mordell_d_of_ideal_coprime (d : ℤ) (hd : d ≤ -1)
    [IsDomain (ℤ√d)] [IsDedekindDomain (ℤ√d)]
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (x y : ℤ)
    (hcop : IsCoprime
      (Ideal.span ({(⟨y, 1⟩ : ℤ√d)} : Set (ℤ√d)))
      (Ideal.span ({(⟨y, -1⟩ : ℤ√d)} : Set (ℤ√d))))
    (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ m : ℤ, (d = 1 - 3 * m ^ 2 ∨ d = -1 - 3 * m ^ 2) ∧
      y = m * (3 * d + m ^ 2) := by
  obtain ⟨z, hz⟩ :=
    exists_cube_root_y_add_sqrtd_of_ideal_coprime d hd hcl x y hcop h_eqn
  exact mordell_arithmetic_of_cube hz

/--
当已知 `ℤ√d` 是 Dedekind 整环时，`mordell_d` 的无公理版本。
-/
theorem mordell_d_of_dedekind (d : ℤ) (hd : d ≤ -1)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    [IsDomain (ℤ√d)] [IsDedekindDomain (ℤ√d)]
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ m : ℤ, (d = 1 - 3 * m ^ 2 ∨ d = -1 - 3 * m ^ 2) ∧
      y = m * (3 * d + m ^ 2) := by
  exact mordell_d_of_ideal_coprime d hd hcl x y
    (span_y_add_sqrtd_coprime d x y h_mod h_sqf h_eqn) h_eqn

/-- `mordell_d` 找到的参数化取值确实满足方程。 -/
theorem mordell_param_solution {R : Type*} [CommRing R] (d m : R)
    (hd : d = 1 - 3 * m ^ 2 ∨ d = -1 - 3 * m ^ 2) :
    (m * (3 * d + m ^ 2)) ^ 2 = (m ^ 2 - d) ^ 3 + d := by
  rcases hd with rfl | rfl <;> ring

/--
可复用 Mordell 定理的完整解形式。

前面的下降定理给出了参数 `m` 以及 `y` 的公式。再与通用参数恒等式比较，
也能确定 `x = m^2 - d`。
-/
theorem mordell_d_solution_of_eq (d : ℤ) (hd : d ≤ -1)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ m : ℤ,
      (d = 1 - 3 * m ^ 2 ∨ d = -1 - 3 * m ^ 2) ∧
        x = m ^ 2 - d ∧ y = m * (3 * d + m ^ 2) := by
  obtain ⟨m, hm_d, hm_y⟩ := mordell_d d hd h_mod h_sqf hcl x y h_eqn
  refine ⟨m, hm_d, ?_, hm_y⟩
  have hparam :
      (m * (3 * d + m ^ 2)) ^ 2 = (m ^ 2 - d) ^ 3 + d :=
    mordell_param_solution (d := d) (m := m) hm_d
  have hx3 : x ^ 3 = (m ^ 2 - d) ^ 3 := by
    have hsame : x ^ 3 + d = (m ^ 2 - d) ^ 3 + d := by
      calc
        x ^ 3 + d = y ^ 2 := h_eqn.symm
        _ = (m * (3 * d + m ^ 2)) ^ 2 := by rw [hm_y]
        _ = (m ^ 2 - d) ^ 3 + d := hparam
    exact add_right_cancel hsame
  exact int_eq_of_cube_eq hx3

/--
整个可复用族的参数化充要条件表述。

这对新的例子很有用：一旦有了类数输入，整数解就恰好是这些有限的参数候选。
-/
theorem mordell_d_solution_iff (d : ℤ) (hd : d ≤ -1)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (x y : ℤ) :
    y ^ 2 = x ^ 3 + d ↔
      ∃ m : ℤ,
        (d = 1 - 3 * m ^ 2 ∨ d = -1 - 3 * m ^ 2) ∧
          x = m ^ 2 - d ∧ y = m * (3 * d + m ^ 2) := by
  constructor
  · exact mordell_d_solution_of_eq d hd h_mod h_sqf hcl x y
  · rintro ⟨m, hm_d, rfl, rfl⟩
    exact mordell_param_solution (d := d) (m := m) hm_d

/--
一个可复用的无解判别准则：在标准 Mordell 假设下，只需排除关于 `d` 的两个参数方程。
-/
theorem mordell_d_no_solution_of_no_param (d : ℤ) (hd : d ≤ -1)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (hno : ∀ m : ℤ, d ≠ 1 - 3 * m ^ 2 ∧ d ≠ -1 - 3 * m ^ 2)
    (x y : ℤ) :
    ¬ y ^ 2 = x ^ 3 + d := by
  intro h_eqn
  obtain ⟨m, hm_d, _hx, _hy⟩ :=
    mordell_d_solution_of_eq d hd h_mod h_sqf hcl x y h_eqn
  rcases hm_d with hm_d | hm_d
  · exact (hno m).1 hm_d
  · exact (hno m).2 hm_d

/--
在所覆盖的族中，当 `3 ∣ d` 时不可能出现参数化解。对于具体的 `d`，
一旦证明了类数假设，这就给出了一种简洁方式来推出新的无解推论。
-/
theorem mordell_d_no_solution_of_three_dvd (d : ℤ) (hd : d ≤ -1)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (h3 : (3 : ℤ) ∣ d)
    (x y : ℤ) :
    ¬ y ^ 2 = x ^ 3 + d := by
  refine mordell_d_no_solution_of_no_param d hd h_mod h_sqf hcl ?_ x y
  rintro m
  rcases h3 with ⟨k, hk⟩
  constructor
  · intro hm
    omega
  · intro hm
    omega

end Mordell
