import Mathlib

set_option maxHeartbeats 1600000

/-!
# Euler's special case of Catalan's conjecture

We prove that the only positive integer solution to x² - y³ = 1 is (x, y) = (3, 2).
Equivalently, x² = y³ + 1 with x, y > 0 implies x = 3 and y = 2.

## Proof structure:
1. If y is odd: (x-1)(x+1) = y³ with gcd(x-1,x+1) = 1, so both are cubes,
   but no two cubes differ by 2. (`no_solution_y_odd`)
2. If y ≡ 1 mod 3: y³+1 ≡ 2 mod 3, not a square. (`not_sq_of_y_eq_one_mod_three`)
3. For even y with y ≡ 0 or 2 mod 3: factor x² = (y+1)(y²-y+1),
   analyze gcd(y+1, y²-y+1) | 3.
   - gcd = 1: forces y = 1, contradiction.
   - gcd = 3: reduces to y = 3s²-1 with t² = 3s⁴-3s²+1.
4. For s = 1: y = 2, x = 3. ✓
5. For s ≥ 2: 3s⁴-3s²+1 is not a perfect square.
   (`not_sq_3s4_sub_3s2_add_1`)

## Status:
The proof is complete modulo `not_sq_3s4_sub_3s2_add_1`, which asserts that the
quartic polynomial 3s⁴ - 3s² + 1 is never a perfect square for s ≥ 2.
This is equivalent to saying the Pell equation X² - 3Y² = 1 has no solution
(X, Y) with X even and (Y+1)/2 a perfect square ≥ 4.

The classical proof of this fact uses unique factorization in the Eisenstein
integers ℤ[ω] (ω = e^{2πi/3}) or a covering system of congruences on the
associated Pell recurrence sequence. Formalizing either approach requires
substantial additional infrastructure beyond what is currently available
in Mathlib.
-/

/-- If y ≡ 1 mod 3, then y³ + 1 ≡ 2 mod 3, hence not a perfect square. -/
lemma not_sq_of_y_eq_one_mod_three {x y : ℤ} (hy : y % 3 = 1) : x ^ 2 ≠ y ^ 3 + 1 := by
  exact ne_of_apply_ne (· % 3)
    (by norm_num [pow_succ, Int.add_emod, Int.mul_emod, hy]
        have := Int.emod_nonneg x three_pos.ne'
        have := Int.emod_lt_of_pos x three_pos
        interval_cases x % 3 <;> trivial)

/-- No two positive perfect cubes differ by exactly 2 -/
lemma no_cubes_differ_by_two (a b : ℕ) (ha : 0 < a) : b ^ 3 ≠ a ^ 3 + 2 := by
  exact fun h => by cases le_or_gt b a <;> nlinarith [Nat.pow_le_pow_left ‹_› 2]

/-- If y is odd and positive, then x² ≠ y³ + 1 for any positive x -/
lemma no_solution_y_odd {x y : ℕ} (hx : 0 < x) (hy : 0 < y) (hodd : y % 2 = 1) :
    x ^ 2 ≠ y ^ 3 + 1 := by
  intro H
  have h_factor : (x - 1) * (x + 1) = y ^ 3 := by
    cases x <;> norm_num at * ; linarith
  obtain ⟨a, ha⟩ : ∃ a, x - 1 = a ^ 3 := by
    have h_coprime : Nat.gcd (x - 1) (x + 1) = 1 := by
      rcases x with (_ | _ | x) <;> simp_all +arith +decide
      norm_num [(by ring : x + 3 = x + 1 + 2)]
      replace h_factor := congr_arg Even h_factor; simp_all +decide [← Nat.odd_iff, parity_simps]
    exact exists_eq_pow_of_mul_eq_pow (by aesop) h_factor
  obtain ⟨b, hb⟩ : ∃ b, x + 1 = b ^ 3 := by
    use y / a
    rw [Nat.div_pow]
    · rw [← ha, ← h_factor,
        Nat.mul_div_cancel_left _
          (Nat.sub_pos_of_lt (lt_of_le_of_ne hx (Ne.symm (by aesop_cat))))]
    · exact Nat.pow_dvd_pow_iff (by decide) |>.1 (ha ▸ h_factor ▸ dvd_mul_right _ _)
  have h_diff : b ^ 3 - a ^ 3 = 2 := by omega
  rcases a with (_ | _ | a) <;> rcases b with (_ | _ | b) <;>
    simp_all +decide [Nat.pow_succ']
  · nlinarith [show y > 1 by contrapose! h_diff; interval_cases y; trivial]
  · rw [Nat.sub_eq_iff_eq_add] at h_diff
    · cases le_or_gt b a <;> nlinarith only [h_diff, ‹_›, pow_two (b - a : ℤ)]
    · exact le_of_lt (Nat.lt_of_sub_eq_succ h_diff)

/-- For s ≥ 2, 3s⁴ - 3s² + 1 is not a perfect square.

This is the core number-theoretic lemma. It is equivalent to saying the Pell equation
X² - 3Y² = 1 has no solution (X, Y) with X even and (Y+1)/2 a perfect square ≥ 4.
The classical proof uses unique factorization in the Eisenstein integers ℤ[ω]. -/
lemma not_sq_3s4_sub_3s2_add_1 (s : ℕ) (hs : 2 ≤ s) :
    ¬ IsSquare (3 * s ^ 4 - 3 * s ^ 2 + 1) := by
  intro h
  obtain ⟨t, ht⟩ := h
  -- Rewrite the equation in terms of Pell equation
  -- We have t² = 3s⁴ - 3s² + 1
  -- Multiply by 4: 4t² = 12s⁴ - 12s² + 4 = 3(4s⁴ - 4s²) + 4 = 3(2s² - 1)² + 1
  -- So: (2t)² - 3(2s² - 1)² = 1
  -- This is a Pell equation: U² - 3V² = 1 where U = 2t and V = 2s² - 1
  sorry

/-
Main theorem: The only positive integer solution to x² = y³ + 1 is (x,y) = (3,2).
-/
theorem euler_catalan (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (heq : x ^ 2 = y ^ 3 + 1) : x = 3 ∧ y = 2 := by
  -- If y is even, we need to check y mod 3. If y ≡ 1 mod 3, then y³ + 1 ≡ 2 mod 3, which isn't a square. So y must be 0 or 2 mod 3.
  by_cases hy_even : y % 2 = 0
  have h_mod3 : y % 3 ≠ 1 := by
    exact fun h => by have := congr_arg ( · % 3 ) heq; norm_num [ Nat.add_mod, Nat.pow_mod, h ] at this; have := Nat.mod_lt x three_pos; interval_cases x % 3 <;> contradiction;
  have h_mod3_cases : y % 3 = 0 ∨ y % 3 = 2 := by
    have := Nat.mod_lt y zero_lt_three; interval_cases y % 3 <;> trivial;
  by_cases h_gcd : Nat.gcd (y + 1) (y ^ 2 - y + 1) = 1;
  · -- If gcd(y+1, y²-y+1) = 1, then both y+1 and y²-y+1 are perfect squares.
    obtain ⟨u, hu⟩ : ∃ u : ℕ, y + 1 = u ^ 2 := by
      have h_factor : (y + 1) * (y ^ 2 - y + 1) = x ^ 2 := by
        nlinarith only [ Nat.sub_add_cancel ( by nlinarith : y ≤ y^2 ), heq ];
      exact exists_eq_pow_of_mul_eq_pow ( by aesop ) h_factor
    obtain ⟨v, hv⟩ : ∃ v : ℕ, y ^ 2 - y + 1 = v ^ 2 := by
      have h_factor : x ^ 2 = (y + 1) * (y ^ 2 - y + 1) := by
        nlinarith only [ Nat.sub_add_cancel ( by nlinarith only [ hy ] : y ≤ y^2 ), heq ];
      rw [ hu ] at h_factor;
      exact ⟨ x / u, by nlinarith only [ Nat.div_mul_cancel ( show u ∣ x from Nat.pow_dvd_pow_iff ( by decide ) |>.1 <| h_factor.symm ▸ dvd_mul_right _ _ ), h_factor, hu ] ⟩;
    rcases y with ( _ | _ | y ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_succ ];
    nlinarith only [ show v = y + 1 by nlinarith only [ hv ], hv ];
  · -- Since gcd(y+1, y²-y+1) divides 3 and is not 1, it must be 3. Therefore, y+1 = 3u² and y²-y+1 = 3v² for some integers u and v.
    obtain ⟨u, hu⟩ : ∃ u : ℕ, y + 1 = 3 * u ^ 2 := by
      have h_gcd_3 : Nat.gcd (y + 1) (y ^ 2 - y + 1) = 3 := by
        have h_gcd_div_3 : Nat.gcd (y + 1) (y ^ 2 - y + 1) ∣ 3 := by
          rw [ show y ^ 2 - y = y * ( y - 1 ) by rw [ Nat.pow_two, Nat.mul_sub_left_distrib, Nat.mul_one ] ];
          rcases y with ( _ | _ | y ) <;> simp_all +arith +decide [ Nat.gcd_dvd_left, Nat.gcd_dvd_right ];
          norm_num [ ( by ring : ( y + 2 ) * ( y + 1 ) + 1 = ( y + 3 ) * ( y + 0 ) + 3 ) ];
          exact Nat.gcd_dvd_right _ _;
        simp_all +decide [ Nat.dvd_prime ];
      -- Since gcd(y+1, y²-y+1) = 3, we can write y+1 = 3u² and y²-y+1 = 3v² for some integers u and v.
      obtain ⟨u, v, hu, hv⟩ : ∃ u v : ℕ, y + 1 = 3 * u ∧ y ^ 2 - y + 1 = 3 * v ∧ Nat.gcd u v = 1 := by
        exact ⟨ ( y + 1 ) / 3, ( y ^ 2 - y + 1 ) / 3, by rw [ Nat.mul_div_cancel' ( h_gcd_3 ▸ Nat.gcd_dvd_left _ _ ) ], by rw [ Nat.mul_div_cancel' ( h_gcd_3 ▸ Nat.gcd_dvd_right _ _ ) ], by rw [ Nat.gcd_div ( h_gcd_3 ▸ Nat.gcd_dvd_left _ _ ) ( h_gcd_3 ▸ Nat.gcd_dvd_right _ _ ), h_gcd_3, Nat.div_self ( by decide ) ] ⟩;
      -- Since $x^2 = (y + 1)(y^2 - y + 1)$, we have $x^2 = 9uv$, so $uv$ must be a perfect square.
      have h_uv_square : ∃ w : ℕ, u * v = w ^ 2 := by
        have h_uv_square : x ^ 2 = 9 * u * v := by
          nlinarith only [ Nat.sub_add_cancel ( show y ≤ y^2 by nlinarith only [ hy ] ), heq, hu, hv.1 ];
        exact ⟨ x / 3, by nlinarith only [ Nat.div_mul_cancel ( show 3 ∣ x from Nat.prime_three.dvd_of_dvd_pow ( h_uv_square.symm ▸ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by norm_num ) _ ) _ ) ), h_uv_square ] ⟩;
      -- Since $u$ and $v$ are coprime and their product $uv$ is a perfect square, both $u$ and $v$ must themselves be perfect squares.
      obtain ⟨w, hw⟩ : ∃ w : ℕ, u = w ^ 2 := by
        exact exists_eq_pow_of_mul_eq_pow ( by aesop ) h_uv_square.choose_spec;
      aesop
    obtain ⟨v, hv⟩ : ∃ v : ℕ, y ^ 2 - y + 1 = 3 * v ^ 2 := by
      -- Since $x^2 = (y + 1)(y^2 - y + 1)$ and $y + 1 = 3u^2$, we have $x^2 = 3u^2(y^2 - y + 1)$.
      have hx_sq : x^2 = 3 * u^2 * (y^2 - y + 1) := by
        nlinarith only [ Nat.sub_add_cancel ( by nlinarith only [ hy ] : y ≤ y^2 ), heq, hu ];
      -- Since $x^2 = 3u^2(y^2 - y + 1)$, we can write $x = ku$ for some integer $k$.
      obtain ⟨k, hk⟩ : ∃ k : ℕ, x = k * u := by
        exact exists_eq_mul_left_of_dvd <| Nat.pow_dvd_pow_iff two_ne_zero |>.1 <| hx_sq.symm ▸ dvd_mul_of_dvd_left ( dvd_mul_left _ _ ) _;
      -- Substitute $x = ku$ into $x^2 = 3u^2(y^2 - y + 1)$ to get $(ku)^2 = 3u^2(y^2 - y + 1)$, which simplifies to $k^2 = 3(y^2 - y + 1)$.
      have hk_sq : k^2 = 3 * (y^2 - y + 1) := by
        exact mul_left_cancel₀ ( pow_ne_zero 2 ( by aesop_cat : u ≠ 0 ) ) ( by subst hk; linarith );
      exact ⟨ k / 3, by nlinarith only [ Nat.div_mul_cancel ( show 3 ∣ k from Nat.prime_three.dvd_of_dvd_pow ( hk_sq.symm ▸ dvd_mul_right _ _ ) ), hk_sq ] ⟩;
    -- Substitute y = 3u² - 1 into y² - y + 1 = 3v² to get (3u² - 1)² - (3u² - 1) + 1 = 3v², which simplifies to 9u⁴ - 9u² + 3 = 3v², or 3u⁴ - 3u² + 1 = v².
    have h_sub : 3 * u ^ 4 - 3 * u ^ 2 + 1 = v ^ 2 := by
      zify at *;
      rw [ Nat.cast_sub ] at * <;> push_cast at * <;> repeat nlinarith only [ hu, hv ] ;
      nlinarith only [ hu, hy ];
    -- For $u \geq 2$, $3u^4 - 3u^2 + 1$ is not a perfect square.
    by_cases hu_ge_2 : u ≥ 2;
    · exact absurd h_sub ( by { exact fun h => not_sq_3s4_sub_3s2_add_1 u hu_ge_2 <| by use v; linarith } );
    · interval_cases u <;> simp_all +decide;
      nlinarith only [ heq, h_sub ];
  · exact False.elim <| no_solution_y_odd hx hy ( Nat.mod_two_ne_zero.mp hy_even ) heq