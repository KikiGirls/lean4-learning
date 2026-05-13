import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Tactic

open Zsqrtd

/-!
# Mordell Targets

This file lists the main theorem-proving targets for the Mordell project.
-/

axiom quadClassNumber : ℤ → ℕ

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

private lemma dvd_sub' {α : Type} [CommRing α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c := by
  rcases h₁ with ⟨x, hx⟩
  rcases h₂ with ⟨y, hy⟩
  use x - y
  rw [hx, hy]
  ring

private lemma sq_mod_four (n : ℤ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  have hn := Int.emod_add_ediv n 4
  have h_lt : n % 4 < 4 := Int.emod_lt n (by norm_num)
  have h_ge : 0 ≤ n % 4 := Int.emod_nonneg n (by norm_num)
  have hr_cases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hr_cases with (hr|hr|hr|hr)
  · left; calc
      n ^ 2 % 4 = ((n % 4) ^ 2) % 4 := by rw [← Int.pow_mod]
      _ = (0 : ℤ) ^ 2 % 4 := by rw [hr]
      _ = 0 := by norm_num
  · right; calc
      n ^ 2 % 4 = ((n % 4) ^ 2) % 4 := by rw [← Int.pow_mod]
      _ = (1 : ℤ) ^ 2 % 4 := by rw [hr]
      _ = 1 := by norm_num
  · left; calc
      n ^ 2 % 4 = ((n % 4) ^ 2) % 4 := by rw [← Int.pow_mod]
      _ = (2 : ℤ) ^ 2 % 4 := by rw [hr]
      _ = 0 := by norm_num
  · right; calc
      n ^ 2 % 4 = ((n % 4) ^ 2) % 4 := by rw [← Int.pow_mod]
      _ = (3 : ℤ) ^ 2 % 4 := by rw [hr]
      _ = 1 := by norm_num

private lemma cube_mod_four_not_two (n : ℤ) : n ^ 3 % 4 ≠ 2 := by
  have hn := Int.emod_add_ediv n 4
  have h_lt : n % 4 < 4 := Int.emod_lt n (by norm_num)
  have h_ge : 0 ≤ n % 4 := Int.emod_nonneg n (by norm_num)
  have hr_cases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hr_cases with (hr|hr|hr|hr)
  · calc
      n ^ 3 % 4 = ((n % 4) ^ 3) % 4 := by rw [← Int.pow_mod]
      _ = (0 : ℤ) ^ 3 % 4 := by rw [hr]
      _ = 0 := by norm_num
      _ ≠ 2 := by norm_num
  · calc
      n ^ 3 % 4 = ((n % 4) ^ 3) % 4 := by rw [← Int.pow_mod]
      _ = (1 : ℤ) ^ 3 % 4 := by rw [hr]
      _ = 1 := by norm_num
      _ ≠ 2 := by norm_num
  · calc
      n ^ 3 % 4 = ((n % 4) ^ 3) % 4 := by rw [← Int.pow_mod]
      _ = (2 : ℤ) ^ 3 % 4 := by rw [hr]
      _ = 0 := by norm_num
      _ ≠ 2 := by norm_num
  · calc
      n ^ 3 % 4 = ((n % 4) ^ 3) % 4 := by rw [← Int.pow_mod]
      _ = (3 : ℤ) ^ 3 % 4 := by rw [hr]
      _ = 3 := by norm_num
      _ ≠ 2 := by norm_num

private lemma even_of_mordell_minus1 (x y : ℤ) (h : y ^ 2 = x ^ 3 - 1) : y % 2 = 0 := by
  have h_eq : y ^ 2 + 1 = x ^ 3 := by omega
  by_contra! h_not
  have hy_odd : y % 2 = 1 := by
    have hm := Int.emod_two_eq_zero_or_one y
    rcases hm with (h0 | h1)
    · exact absurd h0 h_not
    · exact h1
  have hy_sq_mod4 : y ^ 2 % 4 = 1 := by
    rcases sq_mod_four y with (h0 | h1)
    · -- y^2 % 4 = 0 means y even, contradiction
      have : y % 2 = 0 := by
        have hy_sq_mod2 : y ^ 2 % 2 = 0 := by
          have : (0 : ℤ) % 2 = 0 := by norm_num
          rw [h0, this]
        -- y^2 % 2 = 0 → y % 2 = 0
        have hm := sq_mod_two y
        sorry
      exact h_not this
    · exact h1
  have hx_cube_mod4 : x ^ 3 % 4 = 2 := by
    rw [← h_eq]
    calc
      (y ^ 2 + 1) % 4 = ((y ^ 2 % 4) + (1 % 4)) % 4 := by rw [Int.add_emod]
      _ = (1 + 1) % 4 := by rw [hy_sq_mod4]; norm_num
      _ = 2 := by norm_num
  exact cube_mod_four_not_two x hx_cube_mod4

private lemma unit_is_cube_GaussianInt (u : GaussianInt) (hu : IsUnit u) : ∃ v : GaussianInt, u = v ^ 3 := by
  have h_norm : u.norm = 1 := by
    have : u.norm = 1 ↔ IsUnit u := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) u)
    exact this.mpr hu
  -- In GaussianInt, norm = re^2 + im^2 = 1 means (re,im) ∈ {(±1,0), (0,±1)}
  -- These correspond to units 1, -1, i, -i
  rcases u with ⟨a, b⟩
  have h_sq : a ^ 2 + b ^ 2 = 1 := by
    simpa [Zsqrtd.norm] using h_norm
  -- a^2 + b^2 = 1, a,b ∈ ℤ → (a,b) = (±1,0) or (0,±1)
  have ha_sq_nonneg : 0 ≤ a ^ 2 := sq_nonneg a
  have hb_sq_nonneg : 0 ≤ b ^ 2 := sq_nonneg b
  have ha_sq_le_one : a ^ 2 ≤ 1 := by
    have : a ^ 2 + b ^ 2 = 1 := h_sq
    omega
  have hb_sq_le_one : b ^ 2 ≤ 1 := by omega
  -- a^2 ∈ {0,1} since it's an integer square
  have ha_sq_cases : a ^ 2 = 0 ∨ a ^ 2 = 1 := by
    have ha_int : a ^ 2 ∈ ({0, 1} : Finset ℤ) := by
      -- Since a^2 is a square of an integer and ≤1, it must be 0 or 1
      have ha_val : -1 ≤ a ∧ a ≤ 1 := by
        -- From a^2 ≤ 1 we get |a| ≤ 1
        sorry
      sorry
    sorry
  sorry

theorem mordell_minus1_solution_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 1 ↔ x = 1 ∧ y = 0 := by
  haveI h_gcdmonoid : GCDMonoid GaussianInt := EuclideanDomain.gcdMonoid _
  constructor
  · intro h
    have h_eq : y ^ 2 + 1 = x ^ 3 := by omega
    have hy_even : y % 2 = 0 := even_of_mordell_minus1 x y h
    have hy_even_dvd : (2 : ℤ) ∣ y := Int.dvd_of_emod_eq_zero hy_even
    rcases hy_even_dvd with ⟨k, hk⟩
    -- y = 2k, so y^2 + 1 = 4k^2 + 1
    have hy_sq_add_one_eq : y ^ 2 + 1 = 4 * k ^ 2 + 1 := by
      rw [hk]; ring
    -- Lift to GaussianInt
    let z : GaussianInt := ⟨y, 1⟩
    have hz_norm : z.norm = y ^ 2 + 1 := by
      simp [z, Zsqrtd.norm]
    -- Key factorization: z * star z = 4k^2+1 = x^3
    have h_prod : z * star z = (x : GaussianInt) ^ 3 := by
      calc
        z * star z = (z.norm : GaussianInt) := by rw [Zsqrtd.norm_eq_mul_conj]
        _ = ((y ^ 2 + 1 : ℤ) : GaussianInt) := by rw [hz_norm]
        _ = ((x ^ 3 : ℤ) : GaussianInt) := by rw [h_eq]
        _ = (x : GaussianInt) ^ 3 := by simp
    -- Coprimality: gcd(z, star z) is a unit
    have h_coprime : IsUnit (gcd z (star z)) := by
      let g := gcd z (star z)
      have hg_dvd_z : g ∣ z := gcd_dvd_left _ _
      have hg_dvd_star : g ∣ star z := gcd_dvd_right _ _
      have hg_dvd_sub : g ∣ z - star z := dvd_sub' hg_dvd_z hg_dvd_star
      -- z - star z = ⟨y,1⟩ - ⟨y,-1⟩ = ⟨0,2⟩
      have h_sub : z - star z = ⟨0, 2⟩ := by
        ext <;> simp [z, star]
      rw [h_sub] at hg_dvd_sub
      have hg_norm_dvd_norm_z : g.norm ∣ z.norm := by
        rcases hg_dvd_z with ⟨q, hq⟩
        rw [hq, Zsqrtd.norm_mul]
        exact ⟨q.norm, rfl⟩
      have hg_norm_dvd_norm_sub : g.norm ∣ (⟨0, 2⟩ : GaussianInt).norm := by
        rcases hg_dvd_sub with ⟨q, hq⟩
        rw [hq, Zsqrtd.norm_mul]
        exact ⟨q.norm, rfl⟩
      have h_norm_sub : (⟨0, 2⟩ : GaussianInt).norm = 4 := by
        simp [Zsqrtd.norm]
      rw [h_norm_sub] at hg_norm_dvd_norm_sub
      rw [hz_norm, hy_sq_add_one_eq] at hg_norm_dvd_norm_z
      -- g.norm divides 4k^2+1 and 4
      have h_gcd_int : Int.gcd (4 * k ^ 2 + 1) (4 : ℤ) = 1 := by
        apply Int.gcd_eq_one_iff_coprime.mpr
        use 1, -k ^ 2
        ring
      have h_norm_dvd_one : g.norm ∣ (1 : ℤ) := by
        have h_dvd_gcd : g.norm ∣ Int.gcd (4 * k ^ 2 + 1) (4 : ℤ) :=
          Int.dvd_gcd hg_norm_dvd_norm_z hg_norm_dvd_norm_sub
        rw [h_gcd_int] at h_dvd_gcd
        exact h_dvd_gcd
      have h_norm_nonneg : 0 ≤ g.norm := GaussianInt.norm_nonneg g
      -- Since g.norm ≥ 0 and g.norm ∣ 1, we have g.norm = 1
      rcases Int.isUnit_iff.mp (isUnit_of_dvd_one h_norm_dvd_one) with (h_eq1 | h_eq_neg1)
      · exact ((Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) g).mpr h_eq1)
      · linarith
    -- Apply the GCDMonoid lemma
    have h_cube_form : ∃ d : GaussianInt, Associated (d ^ 3) z :=
      exists_associated_pow_of_mul_eq_pow h_coprime h_prod
    rcases h_cube_form with ⟨d, hd_assoc⟩
    -- hd_assoc: Associated (d^3) z, so z = u * d^3 for some unit u
    have h_exists_unit : ∃ u : (GaussianInt)ˣ, (u : GaussianInt) * (d ^ 3) = z := by
      -- Associated a b means ∃ u, IsUnit u ∧ u * a = b
      rcases hd_assoc.symm with ⟨u, hu⟩
      -- hd_assoc.symm : Associated z (d^3)
      -- This should give us z ∣ d^3 and d^3 ∣ z
      -- Actually, Associated.symm just swaps
      -- Let me use hd_assoc directly
      sorry
    sorry
  · -- Reverse direction: x=1, y=0 → y^2 = x^3 - 1
    rintro ⟨rfl, rfl⟩
    norm_num

theorem mordell_minus2_solutions_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 2 ↔ (x = 3 ∧ y = 5) ∨ (x = 3 ∧ y = -5) := by
  sorry

theorem mordell_minus13_solutions_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 13 ↔ (x = 17 ∧ y = 70) ∨ (x = 17 ∧ y = -70) := by
  sorry

theorem mordell_minus5 (x y : ℤ) :
    ¬ y ^ 2 = x ^ 3 - 5 := by
  sorry

theorem mordell_minus6 (x y : ℤ) :
    ¬ y ^ 2 = x ^ 3 - 6 := by
  sorry
