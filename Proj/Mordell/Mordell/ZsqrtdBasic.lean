import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
import Mathlib.NumberTheory.ClassNumber.Finite
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic

open Zsqrtd
open scoped nonZeroDivisors

namespace Mordell

noncomputable abbrev QuadRat (d : ℤ) := QuadraticAlgebra ℚ (d : ℚ) 0

noncomputable def zsqrtdToQuadRat (d : ℤ) : ℤ√d →+* QuadRat d :=
  Zsqrtd.lift ⟨(QuadraticAlgebra.omega : QuadRat d), by
    ext <;> simp [QuadRat]
  ⟩

lemma zsqrtdToQuadRat_apply (d : ℤ) (z : ℤ√d) :
    zsqrtdToQuadRat d z = ⟨(z.re : ℚ), (z.im : ℚ)⟩ := by
  ext <;> simp [zsqrtdToQuadRat, QuadRat]

lemma zsqrtdToQuadRat_injective
    (d : ℤ) : Function.Injective (zsqrtdToQuadRat d) := by
  intro z w h
  ext
  · have h' : (z.re : ℚ) = (w.re : ℚ) := by
      simpa only [zsqrtdToQuadRat_apply] using congrArg QuadraticAlgebra.re h
    exact_mod_cast h'
  · have h' : (z.im : ℚ) = (w.im : ℚ) := by
      simpa only [zsqrtdToQuadRat_apply] using congrArg QuadraticAlgebra.im h
    exact_mod_cast h'

noncomputable instance zsqrtdAlgebraQuadRat (d : ℤ) : Algebra (ℤ√d) (QuadRat d) :=
  (zsqrtdToQuadRat d).toAlgebra

instance zsqrtd_isScalarTower_int_quadRat (d : ℤ) :
    IsScalarTower ℤ (ℤ√d) (QuadRat d) where
  smul_assoc n z x := by
    ext <;> simp [Algebra.smul_def, QuadRat] <;> ring

lemma quadRat_trace_mk (d : ℤ) (a b : ℚ) :
    Algebra.trace ℚ (QuadRat d) (⟨a, b⟩ : QuadRat d) = 2 * a := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (d : ℚ) 0)
    (⟨a, b⟩ : QuadRat d)]
  let M : Matrix (Fin 2) (Fin 2) ℚ := !![a, (d : ℚ) * b; b, a]
  have hM :
      Algebra.leftMulMatrix (QuadraticAlgebra.basis (d : ℚ) 0)
        (⟨a, b⟩ : QuadRat d) = M := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    fin_cases i <;> fin_cases j <;>
      simp [QuadraticAlgebra.basis, QuadraticAlgebra.linearEquivTuple,
        QuadraticAlgebra.equivProd, M]
  rw [hM]
  simp [M]
  ring

lemma quadRat_trace (d : ℤ) (z : QuadRat d) :
    Algebra.trace ℚ (QuadRat d) z = 2 * z.re := by
  rcases z with ⟨a, b⟩
  exact quadRat_trace_mk d a b

lemma quadRat_norm_mk (d : ℤ) (a b : ℚ) :
    Algebra.norm ℚ (⟨a, b⟩ : QuadRat d) = a * a - (d : ℚ) * b * b := by
  rw [Algebra.norm_apply]
  change LinearMap.det
      (DistribSMul.toLinearMap ℚ (QuadRat d) (⟨a, b⟩ : QuadRat d)) = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
  simp [QuadraticAlgebra.norm_def]

lemma quadRat_norm (d : ℤ) (z : QuadRat d) :
    Algebra.norm ℚ z = z.re * z.re - (d : ℚ) * z.im * z.im := by
  rw [Algebra.norm_apply]
  change LinearMap.det (DistribSMul.toLinearMap ℚ (QuadRat d) z) = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
  simp [QuadraticAlgebra.norm_def]

lemma rat_eq_int_of_squarefree_mul_sq_eq_int
    {b : ℚ} {c d : ℤ} (hd : Squarefree d)
    (h : (d : ℚ) * b ^ 2 = c) :
    ∃ b' : ℤ, b = b' := by
  have hdenQ : (b.den : ℚ) ≠ 0 := by positivity
  have hdenZ : (b.den : ℤ) ≠ 0 := by exact_mod_cast b.den_nz
  have hmainQ :
      ((d * b.num ^ 2 : ℤ) : ℚ) =
        ((c * (b.den : ℤ) ^ 2 : ℤ) : ℚ) := by
    calc
      ((d * b.num ^ 2 : ℤ) : ℚ)
          = (d : ℚ) * (b.num : ℚ) ^ 2 := by norm_num
      _ = (d : ℚ) * (b * (b.den : ℚ)) ^ 2 := by
          rw [Rat.mul_den_eq_num]
      _ = ((d : ℚ) * b ^ 2) * (b.den : ℚ) ^ 2 := by ring
      _ = (c : ℚ) * (b.den : ℚ) ^ 2 := by rw [h]
      _ = ((c * (b.den : ℤ) ^ 2 : ℤ) : ℚ) := by norm_num
  have hmain : d * b.num ^ 2 = c * (b.den : ℤ) ^ 2 := by
    exact_mod_cast hmainQ
  have hcop : IsCoprime ((b.den : ℤ) ^ 2) (b.num ^ 2) := by
    have hcop₀ : IsCoprime (b.den : ℤ) b.num := by
      rw [Int.isCoprime_iff_nat_coprime]
      simpa [Nat.coprime_comm] using b.reduced
    simpa using hcop₀.pow
  have hden_sq_dvd : ((b.den : ℤ) ^ 2) ∣ d := by
    apply hcop.dvd_of_dvd_mul_right
    refine ⟨c, ?_⟩
    rw [hmain]
    ring
  have hunit : IsUnit (b.den : ℤ) := by
    apply hd (b.den : ℤ)
    simpa [pow_two] using hden_sq_dvd
  have hden_abs : Int.natAbs (b.den : ℤ) = 1 := Int.isUnit_iff_natAbs_eq.mp hunit
  have hden_one : b.den = 1 := Int.ofNat_inj.mp (by simpa using hden_abs)
  refine ⟨b.num, ?_⟩
  rw [← Rat.num_div_den b, hden_one]
  norm_num

noncomputable def zsqrtdLinearEquiv (d : ℤ) : ℤ√d ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun z := ![z.re, z.im]
  invFun v := ⟨v 0, v 1⟩
  left_inv z := by
    ext <;> simp
  right_inv v := by
    ext i
    fin_cases i <;> simp
  map_add' z w := by
    ext i
    fin_cases i <;> simp
  map_smul' n z := by
    ext i
    fin_cases i <;> simp

noncomputable def zsqrtdBasis (d : ℤ) : Module.Basis (Fin 2) ℤ (ℤ√d) :=
  Module.Basis.ofEquivFun (zsqrtdLinearEquiv d)

instance (d : ℤ) : Module.Free ℤ (ℤ√d) :=
  Module.Free.of_basis (zsqrtdBasis d)

instance (d : ℤ) : Module.Finite ℤ (ℤ√d) :=
  Module.Finite.of_basis (zsqrtdBasis d)

/-- `ℤ` 上的代数范数与显式二次范数一致。 -/
lemma zsqrtd_algebra_norm_mk (d a b : ℤ) :
    Algebra.norm ℤ (⟨a, b⟩ : ℤ√d) = a * a - d * b * b := by
  rw [Algebra.norm_eq_matrix_det (zsqrtdBasis d) (⟨a, b⟩ : ℤ√d)]
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![a, d * b; b, a]
  have hM : Algebra.leftMulMatrix (zsqrtdBasis d) (⟨a, b⟩ : ℤ√d) = M := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    fin_cases i <;> fin_cases j <;>
      simp [zsqrtdBasis, zsqrtdLinearEquiv, M]
  rw [hM]
  simp [M, Matrix.det_fin_two]

lemma zsqrtd_algebra_norm (d : ℤ) (z : ℤ√d) :
    Algebra.norm ℤ z = z.norm := by
  rcases z with ⟨a, b⟩
  simpa [Zsqrtd.norm, mul_assoc] using zsqrtd_algebra_norm_mk d a b

end Mordell
