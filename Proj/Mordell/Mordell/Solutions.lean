import Mordell.ZomegaBasic
import Mordell.ClassNumber.Common
import Mordell.ClassNumber.NegFive
import Mordell.ClassNumber.NegSix
import Mordell.ClassNumber.NegThirteen
import Mathlib.Tactic

open Mordell

/-!
# 具体 Mordell 方程的解

本文件包含若干具体 Mordell 方程的最终整数解表述。
-/

theorem mordell_minus1 (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 - 1) : y = 0 := by
  have h_eqn' : y ^ 2 = x ^ 3 + (-1 : ℤ) := by
    simpa [sub_eq_add_neg] using h_eqn
  obtain ⟨z, hz⟩ := Mordell.exists_cube_root_y_add_sqrtd_neg_one x y h_eqn'
  have ⟨m, hm_d, hm_y⟩ := Mordell.mordell_arithmetic_of_cube hz
  rcases hm_d with h | h
  · have hm : 3 * m ^ 2 = 2 := by linarith
    have hmod := congrArg (fun t : ℤ => t % 3) hm
    norm_num at hmod
  · have hm : m = 0 := by nlinarith [sq_nonneg m, h]
    subst m
    simpa using hm_y

theorem mordell_minus1_solution (x y : ℤ)
    (h_eqn : y ^ 2 = x ^ 3 - 1) : x = 1 ∧ y = 0 := by
  have hy : y = 0 := mordell_minus1 x y h_eqn
  have hx3 : x ^ 3 = (1 : ℤ) ^ 3 := by
    rw [hy] at h_eqn
    norm_num at h_eqn ⊢
    omega
  exact ⟨Mordell.int_eq_of_cube_eq hx3, hy⟩

theorem mordell_minus1_solution_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 1 ↔ x = 1 ∧ y = 0 := by
  constructor
  · exact mordell_minus1_solution x y
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem mordell_minus2 (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 - 2) : y = 5 ∨ y = -5 := by
  have h_eqn' : y ^ 2 = x ^ 3 + (-2 : ℤ) := by
    simpa [sub_eq_add_neg] using h_eqn
  obtain ⟨z, hz⟩ := Mordell.exists_cube_root_y_add_sqrtd_neg_two x y h_eqn'
  have ⟨m, hm_d, hm_y⟩ := Mordell.mordell_arithmetic_of_cube hz
  rcases hm_d with h | h
  · have hm_sq : m ^ 2 = 1 := by omega
    have hm_fac : (m - 1) * (m + 1) = 0 := by nlinarith
    have : m = 1 ∨ m = -1 := by
      rcases mul_eq_zero.mp hm_fac with hm | hm
      · left
        omega
      · right
        omega
    rcases this with rfl | rfl
    · right
      linarith [hm_y]
    · left
      linarith [hm_y]
  · have hm : 3 * m ^ 2 = 1 := by linarith
    have hmod := congrArg (fun t : ℤ => t % 3) hm
    norm_num at hmod

theorem mordell_minus2_solutions (x y : ℤ)
    (h_eqn : y ^ 2 = x ^ 3 - 2) :
    (x = 3 ∧ y = 5) ∨ (x = 3 ∧ y = -5) := by
  rcases mordell_minus2 x y h_eqn with hy | hy
  · left
    have hx3 : x ^ 3 = (3 : ℤ) ^ 3 := by
      rw [hy] at h_eqn
      norm_num at h_eqn ⊢
      omega
    exact ⟨Mordell.int_eq_of_cube_eq hx3, hy⟩
  · right
    have hx3 : x ^ 3 = (3 : ℤ) ^ 3 := by
      rw [hy] at h_eqn
      norm_num at h_eqn ⊢
      omega
    exact ⟨Mordell.int_eq_of_cube_eq hx3, hy⟩

theorem mordell_minus2_solutions_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 2 ↔ (x = 3 ∧ y = 5) ∨ (x = 3 ∧ y = -5) := by
  constructor
  · exact mordell_minus2_solutions x y
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

theorem mordell_minus13 (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 - 13) : y = 70 ∨ y = -70 := by
  have h1 : (-13 : ℤ) ≤ -1 := by decide
  have h2 : (-13 : ℤ) % 4 = 2 ∨ (-13 : ℤ) % 4 = 3 := Or.inr (by decide)
  have h3 : Squarefree (-13 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact (by norm_num : Nat.Prime 13).squarefree
  have h4 : Nat.gcd (Mordell.quadClassNumber (-13)) 3 = 1 :=
    Mordell.classNumber_gcd_three_neg_thirteen
  have h_eqn' : y ^ 2 = x ^ 3 + (-13 : ℤ) := by
    simpa [sub_eq_add_neg] using h_eqn
  have ⟨m, hm_d, hm_y⟩ := mordell_d (-13) h1 h2 h3 h4 x y h_eqn'
  rcases hm_d with h | h
  · have hm : 3 * m ^ 2 = 14 := by linarith
    have hmod := congrArg (fun t : ℤ => t % 3) hm
    norm_num at hmod
  · have hm_sq : m ^ 2 = 4 := by omega
    have hm_fac : (m - 2) * (m + 2) = 0 := by nlinarith
    have : m = 2 ∨ m = -2 := by
      rcases mul_eq_zero.mp hm_fac with hm | hm
      · left
        omega
      · right
        omega
    rcases this with rfl | rfl
    · right
      linarith [hm_y]
    · left
      linarith [hm_y]

theorem mordell_minus13_solutions (x y : ℤ)
    (h_eqn : y ^ 2 = x ^ 3 - 13) :
    (x = 17 ∧ y = 70) ∨ (x = 17 ∧ y = -70) := by
  rcases mordell_minus13 x y h_eqn with hy | hy
  · left
    have hx3 : x ^ 3 = (17 : ℤ) ^ 3 := by
      rw [hy] at h_eqn
      norm_num at h_eqn ⊢
      omega
    exact ⟨Mordell.int_eq_of_cube_eq hx3, hy⟩
  · right
    have hx3 : x ^ 3 = (17 : ℤ) ^ 3 := by
      rw [hy] at h_eqn
      norm_num at h_eqn ⊢
      omega
    exact ⟨Mordell.int_eq_of_cube_eq hx3, hy⟩

theorem mordell_minus13_solutions_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 13 ↔ (x = 17 ∧ y = 70) ∨ (x = 17 ∧ y = -70) := by
  constructor
  · exact mordell_minus13_solutions x y
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

theorem mordell_minus5 (x y : ℤ) : ¬ (y ^ 2 = x ^ 3 - 5) := by
  intro h_eqn
  have h1 : (-5 : ℤ) ≤ -1 := by decide
  have h2 : (-5 : ℤ) % 4 = 2 ∨ (-5 : ℤ) % 4 = 3 := Or.inr (by decide)
  have h3 : Squarefree (-5 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact (by norm_num : Nat.Prime 5).squarefree
  have h4 : Nat.gcd (Mordell.quadClassNumber (-5)) 3 = 1 :=
    Mordell.classNumber_gcd_three_neg_five
  have h_eqn' : y ^ 2 = x ^ 3 + (-5 : ℤ) := by
    simpa [sub_eq_add_neg] using h_eqn
  have ⟨m, hm_d, _⟩ := mordell_d (-5) h1 h2 h3 h4 x y h_eqn'
  rcases hm_d with h | h
  · have hm_sq : m ^ 2 = 2 := by omega
    have hmz : ((m : ZMod 4) ^ 2) = (2 : ZMod 4) := by
      simpa using congrArg (fun t : ℤ => (t : ZMod 4)) hm_sq
    have hbad : ¬ ∃ mz : ZMod 4, mz ^ 2 = (2 : ZMod 4) := by
      decide
    exact hbad ⟨(m : ZMod 4), hmz⟩
  · have hm : 3 * m ^ 2 = 4 := by linarith
    have hmod := congrArg (fun t : ℤ => t % 3) hm
    norm_num at hmod

theorem mordell_minus6 (x y : ℤ) : ¬ (y ^ 2 = x ^ 3 - 6) := by
  intro h_eqn
  have h1 : (-6 : ℤ) ≤ -1 := by decide
  have h2 : (-6 : ℤ) % 4 = 2 ∨ (-6 : ℤ) % 4 = 3 := Or.inl (by decide)
  have h3 : Squarefree (-6 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact (Nat.squarefree_mul (by norm_num : Nat.Coprime 2 3)).mpr
      ⟨Nat.prime_two.squarefree, (by norm_num : Nat.Prime 3).squarefree⟩
  have h4 : Nat.gcd (Mordell.quadClassNumber (-6)) 3 = 1 :=
    Mordell.classNumber_gcd_three_neg_six
  have h_eqn' : y ^ 2 = x ^ 3 + (-6 : ℤ) := by
    simpa [sub_eq_add_neg] using h_eqn
  have ⟨m, hm_d, _⟩ := mordell_d (-6) h1 h2 h3 h4 x y h_eqn'
  rcases hm_d with h | h
  · have hm : 3 * m ^ 2 = 7 := by linarith
    have hmod := congrArg (fun t : ℤ => t % 3) hm
    norm_num at hmod
  · have hm : 3 * m ^ 2 = 5 := by linarith
    have hmod := congrArg (fun t : ℤ => t % 3) hm
    norm_num at hmod
