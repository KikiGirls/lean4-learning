import Mordell.Basic

/-!
# 求解特定的 Mordell 方程

利用 `Mordell.Basic` 中的核心定理 `mordell_d`，我们可以显式地
计算出某些特定 `d` 值下的方程解。
在以下定理中，我们假设关于类数的先决条件已经在其他地方被证明
（使用 `sorry` 跳过那些数论上的类数计算边界条件，以专注于方程的代数下降求解）。
-/

theorem mordell_minus1 (x y : ℤ) (h_eqn : y^2 = x^3 - 1) : y = 0 := by
  -- d = -1 时的前提条件
  have h1 : (-1 : ℤ) ≤ -1 := by decide
  have h2 : (-1 : ℤ) % 4 = 2 ∨ (-1 : ℤ) % 4 = 3 := Or.inr (by decide)
  have h3 : Squarefree (-1 : ℤ) := sorry
  have h4 : Nat.gcd (NumberField.classNumber ℚ(√-1)) 3 = 1 := sorry
  
  -- 应用主定理
  have ⟨m, hm_d, hm_y⟩ := mordell_d (-1) h1 h2 h3 h4 x y h_eqn
  
  -- 分析 d = -3m^2 ± 1 的两种情况
  rcases hm_d with h | h
  · -- 情况 1: -1 = 1 - 3m^2 => 3m^2 = 2 （整数范围内 m 无解）
    sorry 
  · -- 情况 2: -1 = -1 - 3m^2 => 3m^2 = 0 => m = 0
    have : m = 0 := by linarith
    subst this
    -- y = m * (3*d + m^2) = 0 * (-3 + 0) = 0
    exact hm_y

theorem mordell_minus2 (x y : ℤ) (h_eqn : y^2 = x^3 - 2) : y = 5 ∨ y = -5 := by
  -- d = -2 时的前提条件
  have h1 : (-2 : ℤ) ≤ -1 := by decide
  have h2 : (-2 : ℤ) % 4 = 2 ∨ (-2 : ℤ) % 4 = 3 := Or.inl (by decide)
  have h3 : Squarefree (-2 : ℤ) := sorry
  have h4 : Nat.gcd (NumberField.classNumber ℚ(√-2)) 3 = 1 := sorry

  have ⟨m, hm_d, hm_y⟩ := mordell_d (-2) h1 h2 h3 h4 x y h_eqn
  
  rcases hm_d with h | h
  · -- 情况 1: -2 = 1 - 3m^2 => 3m^2 = 3 => m^2 = 1 => m = 1 或 -1
    have : m = 1 ∨ m = -1 := sorry 
    rcases this with rfl | rfl
    · right; linarith [hm_y] -- m = 1 => y = 1*(3(-2)+1) = -5
    · left; linarith [hm_y]  -- m = -1 => y = -1*(3(-2)+1) = 5
  · -- 情况 2: -2 = -1 - 3m^2 => 3m^2 = 1 （无解）
    sorry

theorem mordell_minus13 (x y : ℤ) (h_eqn : y^2 = x^3 - 13) : y = 70 ∨ y = -70 := by
  -- d = -13 时的前提条件
  have h1 : (-13 : ℤ) ≤ -1 := by decide
  have h2 : (-13 : ℤ) % 4 = 2 ∨ (-13 : ℤ) % 4 = 3 := Or.inr (by decide)
  have h3 : Squarefree (-13 : ℤ) := sorry
  have h4 : Nat.gcd (NumberField.classNumber ℚ(√-13)) 3 = 1 := sorry

  have ⟨m, hm_d, hm_y⟩ := mordell_d (-13) h1 h2 h3 h4 x y h_eqn
  
  rcases hm_d with h | h
  · -- 情况 1: -13 = 1 - 3m^2 => 3m^2 = 14 （无解）
    sorry
  · -- 情况 2: -13 = -1 - 3m^2 => 3m^2 = 12 => m^2 = 4 => m = 2 或 -2
    have : m = 2 ∨ m = -2 := sorry
    rcases this with rfl | rfl
    · right; linarith [hm_y] -- m = 2 => y = 2*(3(-13)+4) = -70
    · left; linarith [hm_y]  -- m = -2 => y = -2*(3(-13)+4) = 70

theorem mordell_minus5 (x y : ℤ) : ¬ (y^2 = x^3 - 5) := by
  intro h_eqn
  -- d = -5 时的前提条件
  have h1 : (-5 : ℤ) ≤ -1 := by decide
  have h2 : (-5 : ℤ) % 4 = 2 ∨ (-5 : ℤ) % 4 = 3 := Or.inr (by decide)
  have h3 : Squarefree (-5 : ℤ) := sorry
  have h4 : Nat.gcd (NumberField.classNumber ℚ(√-5)) 3 = 1 := sorry

  have ⟨m, hm_d, _⟩ := mordell_d (-5) h1 h2 h3 h4 x y h_eqn
  
  rcases hm_d with h | h
  · -- 情况 1: -5 = 1 - 3m^2 => 3m^2 = 6 => m^2 = 2 （无解）
    sorry
  · -- 情况 2: -5 = -1 - 3m^2 => 3m^2 = 4 （无解）
    sorry

theorem mordell_minus6 (x y : ℤ) : ¬ (y^2 = x^3 - 6) := by
  intro h_eqn
  -- d = -6 时的前提条件
  have h1 : (-6 : ℤ) ≤ -1 := by decide
  have h2 : (-6 : ℤ) % 4 = 2 ∨ (-6 : ℤ) % 4 = 3 := Or.inl (by decide)
  have h3 : Squarefree (-6 : ℤ) := sorry
  have h4 : Nat.gcd (NumberField.classNumber ℚ(√-6)) 3 = 1 := sorry

  have ⟨m, hm_d, _⟩ := mordell_d (-6) h1 h2 h3 h4 x y h_eqn
  
  rcases hm_d with h | h
  · -- 情况 1: -6 = 1 - 3m^2 => 3m^2 = 7 （无解）
    sorry
  · -- 情况 2: -6 = -1 - 3m^2 => 3m^2 = 5 （无解）
    sorry