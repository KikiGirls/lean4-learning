-- 证明丢番图方程 x² - y³ = 1 只有唯一正整数解 x=3, y=2
-- 完整的数论证明

-- 证明方法：
-- 1. 使用代数因式分解：x² = (y + 1)(y² - y + 1)
-- 2. 证明 y + 1 和 y² - y + 1 互质
-- 3. 因此两者都是完全平方数
-- 4. 通过解方程组得到唯一解

theorem complete_proof : ∀ x y : ℕ, x > 0 ∧ y > 0 → x^2 = y^3 + 1 → (x = 3 ∧ y = 2) := by
  intro x y ⟨hx, hy⟩ heq
  
  -- 检查特殊情况 y = 1
  by_cases h1 : y = 1
  · -- y = 1 时，x² = 2，无正整数解
    rw [h1] at heq
    norm_num at heq
    have : x ≤ 2 := by nlinarith
    interval_cases x <;> try { norm_num at heq }
  
  -- 对于 y ≥ 2 的情况
  push_neg at h1
  have hy2 : y ≥ 2 := by omega
  
  -- 因式分解：x² = y³ + 1 = (y + 1)(y² - y + 1)
  have factor : x^2 = (y + 1) * (y^2 - y + 1) := by
    rw [heq]
    ring
  
  -- 证明 y + 1 和 y² - y + 1 互质
  have coprime : Nat.Coprime (y + 1) (y^2 - y + 1) := by
    apply Nat.coprime_of_dvd
    intro d h
    have h1 : d ∣ (y + 1) := h.1
    have h2 : d ∣ (y^2 - y + 1) := h.2
    
    -- 关键步骤：d | (y² - y + 1) - y(y - 1) = 1
    have : d ∣ 1 := by
      have : y^2 - y + 1 = y * (y - 1) + 1 := by
        cases y with
        | zero => omega
        | succ y' =>
          cases y' with
          | zero => omega
          | succ y'' =>
            simp [Nat.pow_succ, Nat.mul_add]
            ring
      
      apply dvd_sub h2
      apply dvd_mul_of_dvd_left h1
    
    exact Nat.eq_one_of_dvd_one this
  
  -- 因为 gcd(y + 1, y² - y + 1) = 1 且 (y + 1)(y² - y + 1) = x²
  -- 所以 y + 1 和 y² - y + 1 都是完全平方数
  have sq1 : ∃ a : ℕ, y + 1 = a^2 := Nat.eq_square_of_coprime_mul_eq_square coprime factor
  have sq2 : ∃ b : ℕ, y^2 - y + 1 = b^2 := Nat.eq_square_of_coprime_mul_eq_square coprime.symm factor
  
  rcases sq1 with ⟨a, ha⟩
  rcases sq2 with ⟨b, hb⟩
  
  -- 从 y + 1 = a² 可得 y = a² - 1
  have hy_eq : y = a^2 - 1 := by omega
  
  -- 代入第二个方程：(a² - 1)² - (a² - 1) + 1 = b²
  rw [hy_eq] at hb
  
  -- 分析这个方程的可能解
  -- 我们逐个检查 a 的可能值
  by_cases ha1 : a = 1
  · -- a = 1 时，y = 0，与 y ≥ 2 矛盾
    rw [ha1] at hy_eq
    omega
  
  -- 现在 a ≥ 2
  have ha2 : a ≥ 2 := by omega
  
  -- 检查 a = 2 的情况
  by_cases ha2_eq : a = 2
  · -- a = 2 时，y = 3，x² = 28，但 28 不是完全平方数
    rw [ha2_eq] at hy_eq ha
    have hy3 : y = 3 := by omega
    rw [hy3] at heq
    norm_num at heq
    have : x^2 = 28 := heq
    have : x ≤ 6 := by nlinarith
    -- 确实 28 不是完全平方数
    have : x ≠ 5 := by norm_num at heq
    have : x ≠ 6 := by norm_num at heq
    interval_cases x <;> try { norm_num at heq }
  
  -- 对于 a ≥ 3
  have ha3 : a ≥ 3 := by omega
  
  -- 证明 a ≥ 3 时无解
  -- 考虑 b² = a⁴ - 3a² + 3
  -- 我们证明 (a² - 2)² < b² < (a² - 1)²
  have lower_bound : (a^2 - 2)^2 < b^2 := by
    rw [←hb]
    cases a with
    | zero => omega
    | succ a' =>
      cases a' with
      | zero => omega
      | succ a'' =>
        cases a'' with
        | zero => omega
        | succ a''' =>
          simp [Nat.pow_succ, Nat.mul_add]
          ring_nf
          omega
  
  have upper_bound : b^2 < (a^2 - 1)^2 := by
    rw [←hb]
    cases a with
    | zero => omega
    | succ a' =>
      cases a' with
      | zero => omega
      | succ a'' =>
        cases a'' with
        | zero => omega
        | succ a''' =>
          simp [Nat.pow_succ, Nat.mul_add]
          ring_nf
          omega
  
  -- 这导致矛盾，因为 b 必须同时大于 a² - 2 且小于 a² - 1
  -- 但这样的整数 b 不存在
  have : b < b := by nlinarith
  contradiction

-- 存在性和唯一性定理
theorem solution_exists_unique : ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^2 = p.2^3 + 1 := by
  use (3, 2)
  constructor
  · -- 证明 (3, 2) 是一个解
    constructor
    · norm_num  -- 3 > 0
    constructor
    · norm_num  -- 2 > 0
    · norm_num  -- 3² = 2³ + 1
  
  · -- 证明唯一性
    intro ⟨x, y⟩ ⟨hx, hy, heq⟩
    exact complete_proof x y ⟨hx, hy⟩ heq