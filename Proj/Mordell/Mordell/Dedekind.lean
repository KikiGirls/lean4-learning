import Mordell.ZsqrtdBasic

open Zsqrtd
open scoped nonZeroDivisors

namespace Mordell

private lemma int_sq_emod_four_eq_zero_or_one (n : ℤ) :
    n * n % 4 = 0 ∨ n * n % 4 = 1 := by
  rw [Int.mul_emod]
  have h0 : 0 ≤ n % 4 := Int.emod_nonneg n (by norm_num)
  have h4 : n % 4 < 4 := Int.emod_lt_of_pos n (by norm_num)
  interval_cases n % 4 <;> norm_num

private lemma int_odd_sq_emod_four_eq_one {n : ℤ} (hn : Odd n) :
    n ^ 2 % 4 = 1 := by
  have h0 : 0 ≤ n % 4 := Int.emod_nonneg n (by norm_num)
  have h4 : n % 4 < 4 := Int.emod_lt_of_pos n (by norm_num)
  have hmod : n % 2 = 1 := Int.odd_iff.mp hn
  have hmod' : (n % 4) % 2 = 1 := by
    rw [← hmod]
    omega
  interval_cases h : n % 4
  · norm_num at hmod'
  · rw [pow_two, Int.mul_emod, h]
    norm_num
  · norm_num at hmod'
  · rw [pow_two, Int.mul_emod, h]
    norm_num

private lemma int_not_isSquare_of_mod_four_eq_two_or_three
    (d : ℤ) (h_mod : d % 4 = 2 ∨ d % 4 = 3) :
    ¬ IsSquare d := by
  rintro ⟨n, hn⟩
  have hsq : d % 4 = 0 ∨ d % 4 = 1 := by
    simpa [hn] using int_sq_emod_four_eq_zero_or_one n
  rcases h_mod with h2 | h3
  · rw [h2] at hsq
    norm_num at hsq
  · rw [h3] at hsq
    norm_num at hsq

private lemma quadRat_root_not_square_fact
    (d : ℤ) (h_mod : d % 4 = 2 ∨ d % 4 = 3) :
    Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) where
  out := by
    have hrat : ¬ IsSquare (d : ℚ) := by
      simpa [Rat.isSquare_intCast_iff] using
        int_not_isSquare_of_mod_four_eq_two_or_three d h_mod
    intro r hr
    apply hrat
    refine ⟨r, ?_⟩
    simpa [pow_two] using hr.symm

theorem zsqrtd_isDomain_of_mod_four_eq_two_or_three
    (d : ℤ) (h_mod : d % 4 = 2 ∨ d % 4 = 3) : IsDomain (ℤ√d) := by
  have h_nonsquare : ∀ n : ℤ, d ≠ n * n := by
    intro n hdn
    have hsq := int_sq_emod_four_eq_zero_or_one n
    rw [← hdn] at hsq
    rcases h_mod with hmod | hmod <;> rw [hmod] at hsq <;> norm_num at hsq
  letI : NoZeroDivisors (ℤ√d) :=
  { eq_zero_or_eq_zero_of_mul_eq_zero := by
      intro a b hab
      have hnorm : a.norm * b.norm = 0 := by
        simpa [Zsqrtd.norm_mul] using congrArg Zsqrtd.norm hab
      rcases mul_eq_zero.mp hnorm with ha | hb
      · exact Or.inl ((Zsqrtd.norm_eq_zero h_nonsquare a).mp ha)
      · exact Or.inr ((Zsqrtd.norm_eq_zero h_nonsquare b).mp hb) }
  exact NoZeroDivisors.to_isDomain (ℤ√d)

instance zsqrtd_algebra_isIntegral (d : ℤ) : Algebra.IsIntegral ℤ (ℤ√d) :=
  Algebra.IsIntegral.of_finite ℤ (ℤ√d)

instance zsqrtd_isNoetherianRing (d : ℤ) : IsNoetherianRing (ℤ√d) :=
  IsNoetherianRing.of_finite ℤ (ℤ√d)

private lemma quadRat_fraction_surj_aux (d : ℤ) (a b : ℚ) :
    (⟨a, b⟩ : QuadRat d) *
        algebraMap (ℤ√d) (QuadRat d) (((a.den * b.den : ℕ) : ℤ√d)) =
      algebraMap (ℤ√d) (QuadRat d)
        (⟨a.num * (b.den : ℤ), b.num * (a.den : ℤ)⟩ : ℤ√d) := by
  change (⟨a, b⟩ : QuadRat d) *
        zsqrtdToQuadRat d (((a.den * b.den : ℕ) : ℤ√d)) =
      zsqrtdToQuadRat d
        (⟨a.num * (b.den : ℤ), b.num * (a.den : ℤ)⟩ : ℤ√d)
  ext
  · calc
      ({ re := a, im := b } *
            (zsqrtdToQuadRat d) ↑(a.den * b.den)).re =
          a * ((a.den : ℚ) * (b.den : ℚ)) := by
        simp only [Nat.cast_mul, map_mul, map_natCast, QuadraticAlgebra.re_mul,
          QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast, mul_zero,
          add_zero, QuadraticAlgebra.im_mul, zero_mul]
      a * ((a.den : ℚ) * (b.den : ℚ))
          = (a * (a.den : ℚ)) * (b.den : ℚ) := by ring
      _ = (a.num : ℚ) * (b.den : ℚ) := by rw [Rat.mul_den_eq_num]
      _ = ((zsqrtdToQuadRat d)
          { re := a.num * (b.den : ℤ), im := b.num * (a.den : ℤ) }).re := by
        simp [zsqrtdToQuadRat_apply]
  · calc
      ({ re := a, im := b } *
            (zsqrtdToQuadRat d) ↑(a.den * b.den)).im =
          b * ((a.den : ℚ) * (b.den : ℚ)) := by
        simp only [Nat.cast_mul, map_mul, map_natCast, QuadraticAlgebra.im_mul,
          QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast, mul_zero,
          zero_mul, add_zero, QuadraticAlgebra.re_mul, zero_add]
      b * ((a.den : ℚ) * (b.den : ℚ))
          = (b * (b.den : ℚ)) * (a.den : ℚ) := by ring
      _ = (b.num : ℚ) * (a.den : ℚ) := by rw [Rat.mul_den_eq_num]
      _ = ((zsqrtdToQuadRat d)
          { re := a.num * (b.den : ℤ), im := b.num * (a.den : ℤ) }).im := by
        simp [zsqrtdToQuadRat_apply]

private theorem quadRat_isFractionRing_of_mod_four
    (d : ℤ) (h_mod : d % 4 = 2 ∨ d % 4 = 3) :
    IsFractionRing (ℤ√d) (QuadRat d) := by
  haveI : IsDomain (ℤ√d) := zsqrtd_isDomain_of_mod_four_eq_two_or_three d h_mod
  haveI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadRat_root_not_square_fact d h_mod
  letI : Field (QuadRat d) := inferInstance
  exact
  { map_units := by
      rintro ⟨z, hz⟩
      rw [isUnit_iff_ne_zero]
      intro hz0
      have hz_ne : z ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hz
      exact hz_ne (zsqrtdToQuadRat_injective d (by simpa using hz0))
    surj := by
      rintro ⟨a, b⟩
      let s : ℤ√d := ((a.den * b.den : ℕ) : ℤ√d)
      have hs_ne : s ≠ 0 := by
        intro hs
        have hre := congrArg (fun z : ℤ√d => z.re) hs
        dsimp [s] at hre
        norm_num at hre
      have hs_mem : s ∈ (ℤ√d)⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hs_ne
      exact ⟨⟨⟨a.num * (b.den : ℤ), b.num * (a.den : ℤ)⟩, ⟨s, hs_mem⟩⟩,
        quadRat_fraction_surj_aux d a b⟩
    exists_of_eq := by
      intro x y hxy
      refine ⟨1, ?_⟩
      simpa using zsqrtdToQuadRat_injective d hxy }

private lemma quadRat_integral_coords_of_trace_norm_int
    {d c1 c0 : ℤ} {a b : ℚ}
    (h_sqf : Squarefree d)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (hc1 : (c1 : ℚ) = 2 * a)
    (hc0 : (c0 : ℚ) = a ^ 2 - (d : ℚ) * b ^ 2) :
    ∃ a' b' : ℤ, a = a' ∧ b = b' := by
  have h2a : 2 * a = (c1 : ℚ) := hc1.symm
  have hb_scaled :
      (d : ℚ) * (2 * b) ^ 2 = ((c1 ^ 2 - 4 * c0 : ℤ) : ℚ) := by
    calc
      (d : ℚ) * (2 * b) ^ 2 = (2 * a) ^ 2 - 4 * (c0 : ℚ) := by
        rw [hc0]
        ring
      _ = (c1 : ℚ) ^ 2 - 4 * (c0 : ℚ) := by rw [h2a]
      _ = ((c1 ^ 2 - 4 * c0 : ℤ) : ℚ) := by norm_num
  obtain ⟨B, hB⟩ :=
    rat_eq_int_of_squarefree_mul_sq_eq_int h_sqf hb_scaled
  have hEqQ :
      ((d * B ^ 2 : ℤ) : ℚ) = ((c1 ^ 2 - 4 * c0 : ℤ) : ℚ) := by
    rw [← hb_scaled, hB]
    norm_num
  have hEq : d * B ^ 2 = c1 ^ 2 - 4 * c0 := by
    exact_mod_cast hEqQ
  have hB_even : Even B := by
    by_contra hnot
    have hB_odd : Odd B := Int.not_even_iff_odd.mp hnot
    have hBsq : B ^ 2 % 4 = 1 := int_odd_sq_emod_four_eq_one hB_odd
    have hmod_eq : d % 4 = c1 ^ 2 % 4 := by
      calc
        d % 4 = (d * B ^ 2) % 4 := by
          rw [Int.mul_emod, hBsq]
          omega
        _ = (c1 ^ 2 - 4 * c0) % 4 := by rw [hEq]
        _ = c1 ^ 2 % 4 := by omega
    have hc1_sq := int_sq_emod_four_eq_zero_or_one c1
    rcases h_mod with h2 | h3
    · rw [h2] at hmod_eq
      rcases hc1_sq with h0 | h1
      · have h0' : c1 ^ 2 % 4 = 0 := by simpa [pow_two] using h0
        rw [h0'] at hmod_eq
        norm_num at hmod_eq
      · have h1' : c1 ^ 2 % 4 = 1 := by simpa [pow_two] using h1
        rw [h1'] at hmod_eq
        norm_num at hmod_eq
    · rw [h3] at hmod_eq
      rcases hc1_sq with h0 | h1
      · have h0' : c1 ^ 2 % 4 = 0 := by simpa [pow_two] using h0
        rw [h0'] at hmod_eq
        norm_num at hmod_eq
      · have h1' : c1 ^ 2 % 4 = 1 := by simpa [pow_two] using h1
        rw [h1'] at hmod_eq
        norm_num at hmod_eq
  have hc1_even : Even c1 := by
    have hc1_sq_even : Even (c1 ^ 2) := by
      obtain ⟨k, hk⟩ := hB_even
      refine ⟨2 * d * k ^ 2 + 2 * c0, ?_⟩
      subst B
      ring_nf at hEq ⊢
      omega
    exact (Int.even_pow.mp hc1_sq_even).1
  obtain ⟨a', ha'⟩ := hc1_even
  obtain ⟨b', hb'⟩ := hB_even
  refine ⟨a', b', ?_, ?_⟩
  · apply mul_left_cancel₀ (show (2 : ℚ) ≠ 0 by norm_num)
    calc
      (2 : ℚ) * a = (c1 : ℚ) := h2a
      _ = (2 : ℚ) * a' := by
        rw [ha']
        push_cast
        ring
  · apply mul_left_cancel₀ (show (2 : ℚ) ≠ 0 by norm_num)
    calc
      (2 : ℚ) * b = (B : ℚ) := hB
      _ = (2 : ℚ) * b' := by
        rw [hb']
        push_cast
        ring

/--
对于满足 `d % 4 ∈ {2, 3}` 的无平方因子 `d`，`ℤ√d` 是该二次域的全体整数环，
因此是整闭的。
-/
theorem zsqrtd_isIntegrallyClosed_of_squarefree_mod
    (d : ℤ)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d) :
    IsIntegrallyClosed (ℤ√d) := by
  haveI : IsDomain (ℤ√d) := zsqrtd_isDomain_of_mod_four_eq_two_or_three d h_mod
  haveI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadRat_root_not_square_fact d h_mod
  letI : Field (QuadRat d) := inferInstance
  letI : Algebra ℚ (QuadRat d) := QuadraticAlgebra.instAlgebra
  letI : IsScalarTower ℤ ℚ (QuadRat d) :=
  { smul_assoc := by
      intro n q z
      ext <;> simp [Algebra.smul_def] <;> ring }
  haveI : IsFractionRing (ℤ√d) (QuadRat d) :=
    quadRat_isFractionRing_of_mod_four d h_mod
  rw [isIntegrallyClosed_iff (QuadRat d)]
  intro x hx
  have hxZ : IsIntegral ℤ x := isIntegral_trans x hx
  have htrace_int : IsIntegral ℤ (Algebra.trace ℚ (QuadRat d) x) :=
    Algebra.isIntegral_trace hxZ
  have hnorm_int : IsIntegral ℤ (Algebra.norm ℚ x) :=
    Algebra.isIntegral_norm ℚ hxZ
  obtain ⟨c1, hc1⟩ := IsIntegrallyClosed.isIntegral_iff.mp htrace_int
  obtain ⟨c0, hc0⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnorm_int
  have htrace :
      (c1 : ℚ) = 2 * x.re := by
    calc
      (c1 : ℚ) = Algebra.trace ℚ (QuadRat d) x := by simpa using hc1
      _ = 2 * x.re := quadRat_trace d x
  have hnorm :
      (c0 : ℚ) = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := by
    calc
      (c0 : ℚ) = Algebra.norm ℚ x := by simpa using hc0
      _ = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := by
        rw [quadRat_norm]
        ring
  obtain ⟨a', b', ha, hb⟩ :=
    quadRat_integral_coords_of_trace_norm_int h_sqf h_mod htrace hnorm
  refine ⟨⟨a', b'⟩, ?_⟩
  change zsqrtdToQuadRat d (⟨a', b'⟩ : ℤ√d) = x
  ext <;> simp [zsqrtdToQuadRat_apply, ha, hb]

theorem zsqrtd_isIntegralClosure_of_squarefree_mod
    (d : ℤ)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d) :
    IsIntegralClosure (ℤ√d) ℤ (QuadRat d) := by
  haveI : IsDomain (ℤ√d) := zsqrtd_isDomain_of_mod_four_eq_two_or_three d h_mod
  haveI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadRat_root_not_square_fact d h_mod
  letI : Field (QuadRat d) := inferInstance
  letI : Algebra ℚ (QuadRat d) := QuadraticAlgebra.instAlgebra
  letI : IsScalarTower ℤ ℚ (QuadRat d) :=
  { smul_assoc := by
      intro n q z
      ext <;> simp [Algebra.smul_def] <;> ring }
  haveI : IsFractionRing (ℤ√d) (QuadRat d) :=
    quadRat_isFractionRing_of_mod_four d h_mod
  haveI : IsIntegrallyClosed (ℤ√d) :=
    zsqrtd_isIntegrallyClosed_of_squarefree_mod d h_mod h_sqf
  exact IsIntegralClosure.of_isIntegrallyClosed (ℤ√d) ℤ (QuadRat d)

theorem zsqrtd_isDedekindDomain_of_squarefree_mod
    (d : ℤ)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d) :
    IsDedekindDomain (ℤ√d) := by
  haveI : IsDomain (ℤ√d) := zsqrtd_isDomain_of_mod_four_eq_two_or_three d h_mod
  haveI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadRat_root_not_square_fact d h_mod
  letI : Field (QuadRat d) := inferInstance
  letI : Algebra ℚ (QuadRat d) := QuadraticAlgebra.instAlgebra
  letI : IsScalarTower ℤ ℚ (QuadRat d) :=
  { smul_assoc := by
      intro n q z
      ext <;> simp [Algebra.smul_def] <;> ring }
  haveI : IsFractionRing (ℤ√d) (QuadRat d) :=
    quadRat_isFractionRing_of_mod_four d h_mod
  haveI : IsIntegralClosure (ℤ√d) ℤ (QuadRat d) :=
    zsqrtd_isIntegralClosure_of_squarefree_mod d h_mod h_sqf
  exact IsIntegralClosure.isDedekindDomain ℤ ℚ (QuadRat d) (ℤ√d)

end Mordell
