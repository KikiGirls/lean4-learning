import Mathlib
import Mathlib.Data.Real.Irrational

-- Proof that √3 is irrational
theorem sqrt_three_irrational : Irrational (Real.sqrt 3) := by
  -- We can use the fact that if n is a natural number that is not a perfect square,
  -- then √n is irrational.
  -- 3 is not a perfect square, so √3 is irrational.
  exact Nat.prime_three.irrational_sqrt

-- Alternative proof using the standard irrationality proof technique
theorem sqrt_three_irrational_alt : Irrational (Real.sqrt 3) := by
  -- Assume √3 is rational, so √3 = p/q where p, q are coprime integers, q ≠ 0
  intro h
  -- Extract p and q from the irrationality hypothesis
  obtain ⟨p, q, hq, hcoprime, heq⟩ := h
  -- From √3 = p/q, we get 3 = p²/q², so 3q² = p²
  have h1 : (p : ℝ)^2 = 3 * (q : ℝ)^2 := by
    have := congr_arg (· ^ 2) heq
    simp only [pow_two] at this
    linarith
  -- This means p² is divisible by 3
  have h2 : p^2 % 3 = 0 := by
    have := Int.modEq_zero_iff_dvd.mpr (dvd_of_mul_right_eq (p^2) (by linarith : (3 : ℤ) * q^2 = p^2))
    exact this
  -- If p² is divisible by 3, then p is divisible by 3
  have h3 : p % 3 = 0 := by
    apply Int.modEq_zero_of_dvd_of_dvd_pow
    · exact Int.dvd_of_emod_eq_zero h2
    · norm_num
  -- So p = 3k for some k
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h3
  -- Substituting back: (3k)² = 3q², so 9k² = 3q², thus 3k² = q²
  have h4 : q^2 = 3 * k^2 := by
    rw [hk] at h1
    simp only [pow_two, Int.cast_mul, Int.cast_ofNat] at h1
    linarith
  -- This means q² is divisible by 3
  have h5 : q % 3 = 0 := by
    have hq2 : q^2 % 3 = 0 := Int.modEq_zero_iff_dvd.mpr (dvd_of_mul_right_eq (q^2) (by linarith : (3 : ℤ) * k^2 = q^2))
    apply Int.modEq_zero_of_dvd_of_dvd_pow
    · exact Int.dvd_of_emod_eq_zero hq2
    · norm_num
  -- So q is divisible by 3
  obtain ⟨m, hm⟩ := Int.modEq_zero_iff_dvd.mp h5
  -- But this contradicts hcoprime, since both p and q are divisible by 3
  have h6 : (3 : ℤ) ∣ Int.gcd p q := by
    apply Int.dvd_gcd
    · rw [hk]; apply dvd_mul_right
    · rw [hm]; apply dvd_mul_right
  -- Since gcd(p, q) = 1 and 3 divides it, we have 3 ∣ 1, which is false
  have h7 : Int.gcd p q = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcoprime
  rw [h7] at h6
  norm_num at h6
