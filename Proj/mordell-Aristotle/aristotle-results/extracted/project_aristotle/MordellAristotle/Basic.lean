import Mathlib

/-!
# Mordell Targets

This file lists the main theorem-proving targets for the Mordell project.
-/

axiom quadClassNumber : ℤ → ℕ

/-! ### Helper lemmas -/

set_option linter.style.longLine false in
private lemma not_isSquare_quadratic' (x : ℤ) (hx : x ≥ 1) : ¬ IsSquare (x ^ 2 + x + 1) := by
  exact fun ⟨ y, hy ⟩ => by nlinarith [ show y ≤ x by nlinarith, show y ≥ -x by nlinarith ] ;

/-- 3u⁴ + 3u² + 1 is never a perfect square for u ≥ 1.
This is equivalent to showing that the Pell equation X²−3Y²=1 has no solution
with Y = 2u²+1 for u ≥ 1, a deep result about quadratic values in Pell sequences. -/
private lemma not_isSquare_quartic' (u : ℤ) (hu : u ≥ 1) :
    ¬ IsSquare (3 * u ^ 4 + 3 * u ^ 2 + 1) := by
  sorry

/-! ### Main theorems -/

/--
Generic Mordell descent target for equations of the form `y^2 = x^3 + d`.

Under the usual negative, congruence, squarefree, and class-number hypotheses,
every solution is controlled by an integer parameter `m`.
-/
theorem mordell_d (d : ℤ) (hd : d ≤ -1)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ m : ℤ, (d = 1 - 3 * m ^ 2 ∨ d = -1 - 3 * m ^ 2) ∧
      y = m * (3 * d + m ^ 2) := by
  sorry

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
theorem mordell_minus1_solution_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 1 ↔ x = 1 ∧ y = 0 := by
  by_cases hx : x = 1;
  · aesop;
  · constructor;
    · intro hy
      have h_gcd : Int.gcd (x - 1) (x ^ 2 + x + 1) = 1 ∨ Int.gcd (x - 1) (x ^ 2 + x + 1) = 3 := by
        have h_gcd : Int.gcd (x - 1) (x ^ 2 + x + 1) ∣ 3 := by
          exact Int.gcd_dvd_iff.2 ⟨ -x - 2, 1, by ring ⟩;
        rwa [ Nat.dvd_prime Nat.prime_three ] at h_gcd;
      obtain h | h := h_gcd;
      · have h_perfect_square : ∃ k : ℤ, x^2 + x + 1 = k^2 := by
          have h_perfect_square : ∃ k : ℕ, (x^2 + x + 1).natAbs = k^2 := by
            have h_perfect_square : ∃ k : ℕ, (x^2 + x + 1).natAbs * (x - 1).natAbs = k^2 := by
              use y.natAbs;
              rw [ ← Int.natAbs_mul, mul_comm ];
              rw [ ← Int.natAbs_pow, hy ] ; ring;
            have h_coprime : Nat.gcd ((x^2 + x + 1).natAbs) ((x - 1).natAbs) = 1 := by
              exact Nat.Coprime.symm h;
            exact exists_eq_pow_of_mul_eq_pow ( by aesop ) h_perfect_square.choose_spec;
          exact Exists.elim h_perfect_square fun k hk => ⟨ k, by linarith [ abs_of_nonneg ( by nlinarith : 0 ≤ x ^ 2 + x + 1 ) ] ⟩;
        have h_bounds : x^2 < x^2 + x + 1 ∧ x^2 + x + 1 < (x + 1)^2 := by
          constructor <;> nlinarith [ show x > 0 from lt_of_le_of_ne ( by nlinarith [ sq_nonneg ( x^2 ) ] ) ( Ne.symm <| by rintro rfl; nlinarith ) ];
        obtain ⟨ k, hk ⟩ := h_perfect_square; nlinarith only [ show k ≤ x by nlinarith only [ hk, h_bounds ], show k ≥ -x by nlinarith only [ hk, h_bounds ], hk, h_bounds ] ;
      · obtain ⟨k, hk⟩ : ∃ k : ℤ, x - 1 = 3 * k := by
          exact Int.dvd_trans ( by norm_num ) ( h ▸ Int.gcd_dvd_left _ _ )
        obtain ⟨m, hm⟩ : ∃ m : ℤ, x ^ 2 + x + 1 = 3 * m := by
          exact Int.dvd_trans ( by norm_num ) ( h ▸ Int.gcd_dvd_right _ _ );
        obtain ⟨u, hu⟩ : ∃ u : ℤ, k = u ^ 2 := by
          have h_km_square : ∃ z : ℤ, k * m = z ^ 2 := by
            use y / 3;
            have h_div : y ^ 2 = 9 * k * m := by
              grind;
            cases abs_cases y <;> nlinarith [ Int.ediv_mul_cancel ( show 3 ∣ y from Int.Prime.dvd_pow' ( by decide ) <| h_div.symm ▸ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _ ) ];
          have h_coprime : Int.gcd k m = 1 := by
            simp_all +decide [ Int.gcd_mul_left ];
          have h_k_square : ∃ u : ℕ, k.natAbs = u ^ 2 := by
            have h_k_square : k.natAbs * m.natAbs = h_km_square.choose.natAbs ^ 2 := by
              simpa only [ sq, Int.natAbs_mul ] using congr_arg Int.natAbs h_km_square.choose_spec;
            exact exists_eq_pow_of_mul_eq_pow ( by aesop ) h_k_square;
          exact Exists.elim h_k_square fun u hu => ⟨ u, by linarith [ abs_of_nonneg ( show 0 ≤ k by nlinarith ) ] ⟩
        obtain ⟨v, hv⟩ : ∃ v : ℤ, m = v ^ 2 := by
          have h_km_square : ∃ w : ℤ, k * m = w ^ 2 := by
            use y / 3;
            cases abs_cases y <;> nlinarith [ Int.ediv_mul_cancel ( show 3 ∣ y from Int.Prime.dvd_pow' ( by decide ) <| by rw [ hy ] ; exact Int.dvd_of_emod_eq_zero <| by norm_num [ Int.sub_emod, Int.mul_emod, pow_succ, show x % 3 = 1 from by omega ] ) ];
          by_cases hu : u = 0 <;> simp_all +decide;
          · exact False.elim <| hx <| sub_eq_zero.mp hk;
          · obtain ⟨ w, hw ⟩ := h_km_square;
            exact ⟨ w / u, by cases lt_or_gt_of_ne hu <;> nlinarith [ sq_nonneg ( w / u - u ), Int.ediv_mul_cancel ( show u ∣ w from Int.pow_dvd_pow_iff two_ne_zero |>.1 <| hw ▸ dvd_mul_right _ _ ) ] ⟩;
        have h_sub : (3 * u ^ 2 + 1) ^ 2 + (3 * u ^ 2 + 1) + 1 = 3 * v ^ 2 := by
          grind;
        by_cases hu_pos : u ≥ 1 ∨ u ≤ -1;
        · cases hu_pos <;> [ exact False.elim ( not_isSquare_quartic' u ( by linarith ) ⟨ v, by linarith ⟩ ) ; exact False.elim ( not_isSquare_quartic' ( -u ) ( by linarith ) ⟨ v, by linarith ⟩ ) ];
        · push_neg at hu_pos; rcases hu_pos with ⟨ hu₁, hu₂ ⟩ ; interval_cases u ; simp_all +decide ;
          exact hx ( by linarith );
    · aesop

theorem mordell_minus2_solutions_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 2 ↔ (x = 3 ∧ y = 5) ∨ (x = 3 ∧ y = -5) := by
  sorry

theorem mordell_minus13_solutions_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 13 ↔ (x = 17 ∧ y = 70) ∨ (x = 17 ∧ y = -70) := by
  sorry

set_option linter.style.longLine false in
theorem mordell_minus5 (x y : ℤ) :
    ¬ y ^ 2 = x ^ 3 - 5 := by
  by_contra h_contra
  have hx_odd : x % 2 = 1 := by
    exact Int.emod_two_ne_zero.mp fun h => by have := congr_arg ( · % 4 ) h_contra; rcases Int.even_or_odd' x with ⟨ k, rfl | rfl ⟩ <;> rcases Int.even_or_odd' y with ⟨ l, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod ] at *;
  have hx_mod4 : x % 4 = 1 := by
    rw [ ← Int.emod_emod_of_dvd x ( by decide : ( 2 : ℤ ) ∣ 4 ) ] at hx_odd; have := Int.emod_nonneg x four_pos.ne'; have := Int.emod_lt_of_pos x four_pos; interval_cases _ : x % 4 <;> simp_all +decide ;
    exact absurd ( congr_arg ( · % 4 ) h_contra ) ( by norm_num [ pow_succ', Int.mul_emod, Int.sub_emod, ‹x % 4 = _› ] ; have := Int.emod_nonneg y four_pos.ne'; have := Int.emod_lt_of_pos y four_pos; interval_cases y % 4 <;> trivial )
  obtain ⟨c, hc⟩ : ∃ c : ℤ, x = 4 * c + 1 := by
    exact ⟨ x / 4, by rw [ ← hx_mod4, Int.mul_ediv_add_emod ] ⟩
  have h_eq : (y / 2) ^ 2 + 1 = c * (16 * c ^ 2 + 12 * c + 3) := by
    obtain ⟨a, ha⟩ : ∃ a : ℤ, y = 2 * a := by
      exact even_iff_two_dvd.mp ( by simpa +decide [ hx_odd, hx_mod4, hc, parity_simps ] using congr_arg Even h_contra );
    subst_vars; norm_num; linarith;
  obtain ⟨p, hp_prime, hp_mod⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ Int.natAbs (16 * c ^ 2 + 12 * c + 3) ∧ p % 4 = 3 := by
    by_cases h₂ : ∀ p : ℕ, Nat.Prime p → p ∣ Int.natAbs (16 * c ^ 2 + 12 * c + 3) → p % 4 = 1;
    · have h_mod : Int.natAbs (16 * c ^ 2 + 12 * c + 3) % 4 = 1 := by
        rw [ ← Nat.prod_primeFactorsList ( show Int.natAbs ( 16 * c ^ 2 + 12 * c + 3 ) ≠ 0 from by norm_num; nlinarith ) ] ; rw [ List.prod_nat_mod ] ; rw [ List.prod_eq_one ] <;> aesop;
      rw [ ← Int.ofNat_inj ] at * ; norm_num [ Int.add_emod, Int.mul_emod ] at *;
      rw [ abs_of_nonneg ( by nlinarith ) ] at h_mod ; norm_num [ Int.add_emod, Int.mul_emod ] at h_mod;
    · push_neg at h₂;
      obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := h₂; have := Nat.Prime.eq_two_or_odd hp₁; rcases this with ( rfl | hp₄ ) <;> simp_all +decide [ ← Nat.mod_mod_of_dvd _ ( by decide : 2 ∣ 4 ) ] ;
      · grind;
      · exact ⟨ p, hp₁, hp₂, by have := Nat.mod_lt p zero_lt_four; interval_cases p % 4 <;> trivial ⟩;
  have h_not_quad_res : ¬∃ a : ℤ, a ^ 2 ≡ -1 [ZMOD p] := by
    haveI := Fact.mk hp_prime; simp +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
    intro x hx; have := ZMod.exists_sq_eq_neg_one_iff ( p := p ) ; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
    exact this ⟨ x, by rw [ sq ] at hx; aesop ⟩;
  exact h_not_quad_res ⟨ y / 2, Int.ModEq.symm <| Int.modEq_of_dvd <| by simpa using dvd_trans ( Int.natCast_dvd.mpr hp_mod.left ) <| h_eq.symm ▸ dvd_mul_left _ _ ⟩

theorem mordell_minus6 (x y : ℤ) :
    ¬ y ^ 2 = x ^ 3 - 6 := by
  sorry
