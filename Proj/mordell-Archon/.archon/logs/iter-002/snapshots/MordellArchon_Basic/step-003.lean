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

private lemma even_of_mordell_minus1 (x y : ℤ) (h : y ^ 2 = x ^ 3 - 1) : y % 2 = 0 := by
  have h_eq : y ^ 2 + 1 = x ^ 3 := by omega
  have h_mod4 : (y : ZMod 4) ^ 2 = (x : ZMod 4) ^ 3 - 1 := by
    push_cast
    rw [h]
    ring
  have h_all : ∀ a b : ZMod 4, a ^ 2 = b ^ 3 - 1 → (a : ZMod 2) = 0 := by
    decide
  have hz2 : (y : ZMod 2) = 0 := h_all (y : ZMod 4) (x : ZMod 4) h_mod4
  -- Convert (y : ZMod 2) = 0 to y % 2 = 0
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd 2 y]
  -- hz2: (y : ZMod 2) = 0 ↔ 2 ∣ y ↔ y % 2 = 0
  have : (y : ZMod 2) = 0 ↔ (2 : ℤ) ∣ y := by
    -- ZMod 2 is ℤ/2ℤ, so (y : ZMod 2) = 0 means y ≡ 0 mod 2
    -- Use ZMod.intCast_zmod_eq_zero_iff_dvd
    sorry
  sorry

private lemma unit_is_cube_GaussianInt {u : GaussianInt} (hu : IsUnit u) : ∃ v : GaussianInt, u = v ^ 3 := by
  -- Units of GaussianInt are ±1, ±i (norm 1 elements: (±1,0), (0,±1))
  have h_norm_one : u.norm = 1 := by
    have := Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) u
    rcases this.mp ?_ with h
    · exact h
    · exact hu
  sorry

theorem mordell_minus1_solution_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 1 ↔ x = 1 ∧ y = 0 := by
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
    have hz_conj_norm : (star z).norm = y ^ 2 + 1 := by
      simp [z, Zsqrtd.norm, star]
    -- Key factorization: z * star z = (y^2+1 : GaussianInt) = (x : GaussianInt)^3
    have h_prod : z * star z = (x : GaussianInt) ^ 3 := by
      calc
        z * star z = (z.norm : GaussianInt) := by rw [Zsqrtd.norm_eq_mul_conj]
        _ = ((y ^ 2 + 1 : ℤ) : GaussianInt) := by rw [hz_norm]
        _ = (x ^ 3 : ℤ) := by rw [h_eq]
        _ = (x : GaussianInt) ^ 3 := by simp
    -- Coprimality: gcd(z, star z) is a unit
    have h_coprime : IsUnit (gcd z (star z)) := by
      let g := gcd z (star z)
      have hg_dvd_z : g ∣ z := gcd_dvd_left _ _
      have hg_dvd_star_z : g ∣ star z := gcd_dvd_right _ _
      have hg_dvd_sub : g ∣ z - star z := dvd_sub' hg_dvd_z hg_dvd_star_z
      -- z - star z = ⟨y,1⟩ - ⟨y,-1⟩ = ⟨0,2⟩
      have h_sub : z - star z = ⟨0, 2⟩ := by
        ext <;> simp [z, star]
      rw [h_sub] at hg_dvd_sub
      -- Now g divides ⟨0,2⟩ and g divides z = ⟨y,1⟩
      -- Use norm:
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
      -- g.norm divides z.norm = y^2+1 = 4k^2+1 and 4
      -- g.norm ∣ 4 and g.norm ∣ 4k^2+1, so g.norm ∣ gcd(4k^2+1, 4) = 1
      rw [hz_norm, hy_sq_add_one_eq] at hg_norm_dvd_norm_z
      have h_gcd_int : Int.gcd (4 * k ^ 2 + 1) (4 : ℤ) = 1 := by
        -- Bézout: 1 = 1*(4k^2+1) + (-k^2)*4
        apply Int.gcd_eq_one_iff_coprime.mpr
        use 1, -k ^ 2
        ring
      have h_norm_dvd_one : g.norm ∣ (1 : ℤ) := by
        have h_dvd_gcd : g.norm ∣ Int.gcd (4 * k ^ 2 + 1) (4 : ℤ) :=
          Int.dvd_gcd hg_norm_dvd_norm_z hg_norm_dvd_norm_sub
        rw [h_gcd_int] at h_dvd_gcd
        exact h_dvd_gcd
      -- g.norm is a natural number (norm is nonnegative for GaussianInt)
      have h_norm_nonneg : 0 ≤ g.norm := GaussianInt.norm_nonneg g
      rcases Int.isUnit_iff.mp (isUnit_of_dvd_one h_norm_dvd_one) with (h_eq1 | h_eq_neg1)
      · -- g.norm = 1
        -- Use Zsqrtd.norm_eq_one_iff' for d = -1 ≤ 0
        have h_unit : IsUnit g :=
          ((Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) g).mpr h_eq1)
        exact h_unit
      · -- g.norm = -1 impossible since norm ≥ 0
        linarith [GaussianInt.norm_nonneg g]
    -- Apply the GCDMonoid lemma
    have h_cube_form : ∃ d : GaussianInt, Associated (d ^ 3) z :=
      exists_associated_pow_of_mul_eq_pow h_coprime h_prod
    rcases h_cube_form with ⟨d, hd_assoc⟩
    -- hd_assoc: Associated (d^3) z, so z = u * d^3 for some unit u
    rcases hd_assoc.exists_unit with ⟨u, hu_eq⟩
    -- hu_eq: z = u * d^3 (up to the direction; let's check)
    -- Actually, Associated.exists_unit gives z = (u : GaussianInt) * (d^3) or vice versa
    -- Let's use hd_assoc.symm.exists_unit if needed
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
