import Mordell.Descent
import Mordell.EuclideanNegTwo
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

open Zsqrtd
open scoped nonZeroDivisors

/-!
# Small class-number inputs: common infrastructure

This module contains the shared class-number facts and ideal lemmas used by the
concrete Mordell examples.
-/

namespace Mordell

theorem quadClassNumber_neg_one : quadClassNumber (-1) = 1 := by
  simp only [quadClassNumber, Int.reduceNeg, Int.neg_neg_iff_pos, zero_lt_one, ↓reduceDIte,
    Nat.card_eq_fintype_card]
  exact card_classGroup_eq_one (R := ℤ√(-1 : ℤ))

theorem quadClassNumber_neg_two : quadClassNumber (-2) = 1 := by
  simp only [quadClassNumber, Int.reduceNeg, Int.reduceLT, ↓reduceDIte, Nat.card_eq_fintype_card]
  exact card_classGroup_eq_one (R := ℤ√(-2 : ℤ))

theorem classNumber_gcd_three_neg_one :
    Nat.gcd (quadClassNumber (-1)) 3 = 1 := by
  rw [quadClassNumber_neg_one]
  norm_num

theorem classNumber_gcd_three_neg_two :
    Nat.gcd (quadClassNumber (-2)) 3 = 1 := by
  rw [quadClassNumber_neg_two]
  norm_num

abbrev R5 := ℤ√(-5 : ℤ)
abbrev R6 := ℤ√(-6 : ℤ)
abbrev R13 := ℤ√(-13 : ℤ)

lemma mem_span_int_zsqrtd_iff {d n : ℤ} (z : ℤ√d) :
    z ∈ Ideal.span ({(n : ℤ√d)} : Set (ℤ√d)) ↔ n ∣ z.re ∧ n ∣ z.im := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨w, rfl⟩
    constructor
    · use w.re
      simp
    · use w.im
      simp
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    use (⟨a, b⟩ : ℤ√d)
    ext <;> simp [ha, hb]

lemma mem_span_two_zsqrtd_iff {d : ℤ} (z : ℤ√d) :
    z ∈ Ideal.span ({(2 : ℤ√d)} : Set (ℤ√d)) ↔ Even z.re ∧ Even z.im := by
  constructor
  · intro hz
    have h := (mem_span_int_zsqrtd_iff (d := d) (n := 2) z).mp hz
    exact ⟨even_iff_two_dvd.mpr h.1, even_iff_two_dvd.mpr h.2⟩
  · intro h
    exact (mem_span_int_zsqrtd_iff (d := d) (n := 2) z).mpr
      ⟨even_iff_two_dvd.mp h.1, even_iff_two_dvd.mp h.2⟩

lemma mem_span_two_negFive_iff (z : R5) :
    z ∈ Ideal.span ({(2 : R5)} : Set R5) ↔ Even z.re ∧ Even z.im :=
  mem_span_two_zsqrtd_iff z

lemma mem_span_two_negSix_iff (z : R6) :
    z ∈ Ideal.span ({(2 : R6)} : Set R6) ↔ Even z.re ∧ Even z.im :=
  mem_span_two_zsqrtd_iff z

lemma mem_span_two_negThirteen_iff (z : R13) :
    z ∈ Ideal.span ({(2 : R13)} : Set R13) ↔ Even z.re ∧ Even z.im :=
  mem_span_two_zsqrtd_iff z

lemma mem_span_three_negThirteen_iff (z : R13) :
    z ∈ Ideal.span ({(3 : R13)} : Set R13) ↔ (3 : ℤ) ∣ z.re ∧ (3 : ℤ) ∣ z.im :=
  mem_span_int_zsqrtd_iff z

def idealDivBy {R : Type*} [CommRing R] (n : R) (I : Ideal R) : Ideal R where
  carrier := {z | n * z ∈ I}
  zero_mem' := by simp
  add_mem' hx hy := by
    simpa [mul_add] using I.add_mem hx hy
  smul_mem' a x hx := by
    change n * (a * x) ∈ I
    simpa [mul_assoc, mul_left_comm, mul_comm] using I.mul_mem_left a hx

lemma span_singleton_mul_idealDivBy_eq_of_le {R : Type*} [CommRing R]
    {n : R} {I : Ideal R} (hle : I ≤ Ideal.span ({n} : Set R)) :
    Ideal.span ({n} : Set R) * idealDivBy n I = I := by
  apply _root_.le_antisymm
  · rw [Ideal.mul_le]
    intro x hx y hy
    rw [Ideal.mem_span_singleton] at hx
    rcases hx with ⟨r, rfl⟩
    simpa [mul_assoc, mul_left_comm, mul_comm] using I.mul_mem_left r hy
  · intro x hx
    obtain ⟨y, hy⟩ := (Ideal.mem_span_singleton.mp (hle hx))
    rw [hy]
    rw [Ideal.mem_span_singleton_mul]
    exact ⟨y, by change n * y ∈ I; rwa [← hy], by ring⟩

namespace ClassNumber

lemma card_le_two_of_two_values {G : Type*} [Finite G] [One G]
    (s : G) (h : ∀ C : G, C = 1 ∨ C = s) :
    Nat.card G ≤ 2 := by
  letI := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card]
  have hsurj : Function.Surjective
      (fun i : Fin 2 => if (i : ℕ) = 0 then (1 : G) else s) := by
    intro C
    rcases h C with hC | hC
    · exact ⟨0, by simp [hC]⟩
    · exact ⟨1, by simp [hC]⟩
  exact (Fintype.card_le_of_surjective _ hsurj).trans_eq (by simp)

lemma gcd_three_of_card_le_two {G : Type*} [Finite G] [One G]
    (hcard_le : Nat.card G ≤ 2) :
    Nat.gcd (Nat.card G) 3 = 1 := by
  letI := Fintype.ofFinite G
  haveI : Nonempty G := ⟨1⟩
  have hcard_pos : 0 < Nat.card G := Nat.card_pos
  have hcases : Nat.card G = 1 ∨ Nat.card G = 2 := by omega
  rcases hcases with h | h <;> rw [h] <;> norm_num

end ClassNumber

theorem exists_cube_root_y_add_sqrtd_neg_one (x y : ℤ)
    (h_eqn : y ^ 2 = x ^ 3 + (-1 : ℤ)) :
    ∃ z : ℤ√(-1 : ℤ), z ^ 3 = (⟨y, 1⟩ : ℤ√(-1 : ℤ)) := by
  have hmod : (-1 : ℤ) % 4 = 2 ∨ (-1 : ℤ) % 4 = 3 := Or.inr (by decide)
  have hsqf : Squarefree (-1 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    norm_num [Squarefree]
  have hcop := span_y_add_sqrtd_coprime (-1) x y hmod hsqf h_eqn
  exact exists_cube_root_y_add_sqrtd_of_ideal_coprime (-1) (by norm_num)
    classNumber_gcd_three_neg_one x y hcop h_eqn

theorem exists_cube_root_y_add_sqrtd_neg_two (x y : ℤ)
    (h_eqn : y ^ 2 = x ^ 3 + (-2 : ℤ)) :
    ∃ z : ℤ√(-2 : ℤ), z ^ 3 = (⟨y, 1⟩ : ℤ√(-2 : ℤ)) := by
  have hmod : (-2 : ℤ) % 4 = 2 ∨ (-2 : ℤ) % 4 = 3 := Or.inl (by decide)
  have hsqf : Squarefree (-2 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    norm_num
    exact Nat.prime_two.squarefree
  have hcop := span_y_add_sqrtd_coprime (-2) x y hmod hsqf h_eqn
  exact exists_cube_root_y_add_sqrtd_of_ideal_coprime (-2) (by norm_num)
    classNumber_gcd_three_neg_two x y hcop h_eqn

end Mordell
