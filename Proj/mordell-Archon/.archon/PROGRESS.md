# Project Progress

## Current Stage
prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## Previous Iteration Summary (iter-001, iter-002)

Both previous iterations ran but produced no task_results — no prover completed work on the files.
The file `MordellArchon/Basic.lean` still has 6 sorries untouched.

## Difficulty Assessment

| Theorem | Ring | UFD? | Difficulty | Priority |
|---------|------|------|------------|----------|
| `mordell_minus1_solution_iff` | ℤ[i] (GaussianInt) | YES | Medium | **HIGH — do first** |
| `mordell_minus2_solutions_iff` | ℤ[√-2] | YES | Medium-Hard | Medium |
| `mordell_minus5` | ℤ[√-5] | NO (class 2) | Very Hard | Low |
| `mordell_minus6` | ℤ[√-6] | NO (class 2) | Very Hard | Low |
| `mordell_minus13_solutions_iff` | ℤ[√-13] | NO (class 2) | Very Hard | Low |
| `mordell_d` | General | varies | Extremely Hard | Defer |

**Key insight**: Mordell equations CANNOT be proved by congruences alone (Hasse principle failure). They require algebraic number theory: factorization in quadratic integer rings + UFD/coprime arguments.

## Current Objectives

1. **MordellArchon/Basic.lean** — Fill all reachable sorries. Priority order:
   - **PRIMARY**: Prove `mordell_minus1_solution_iff` (line 27). Use GaussianInt (ℤ[i]). See informal proof below.
   - **SECONDARY**: Prove `mordell_minus2_solutions_iff` (line 31). Use Zsqrtd (-2). Similar template to d=-1.
   - **TERTIARY**: Attempt `mordell_minus5` (line 39) and `mordell_minus6` (line 43). These are much harder (non-UFD). If stuck, leave placeholder with partial work and document in task_results.
   - **DEFER**: `mordell_d` (line 18) and `mordell_minus13_solutions_iff` (line 35) are extremely hard. Do not attempt in this iteration.

## Required Imports

Add to `MordellArchon/Basic.lean`:
```lean
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.IntegralDomain
```

## Informal Proof: mordell_minus1_solution_iff

**Statement**: y² = x³ - 1 ↔ x = 1 ∧ y = 0

**← direction**: Trivial: 0² = 1³ - 1.

**→ direction**: Prove (x,y) = (1,0) is the only solution.

### Step 1: Parity — y must be even.

If y is odd: y² ≡ 1 (mod 4) → x³ = y² + 1 ≡ 2 (mod 4). Cubes mod 4 ∈ {0,1,3}. Contradiction. So y is even.

In Lean: use `Int.even_of_mod_two_eq_zero` or `by omega`. Then `h_y_even : y % 2 = 0`.

### Step 2: Lift to GaussianInt.

GaussianInt = ℤ√(-1). Let `z : GaussianInt := ⟨y, 1⟩` (this is y + i). Then:
- `z * conj z = (y + i)(y - i) = y² + 1 = x³`
- Conjugate is `⟨y, -1⟩`

In GaussianInt: `z.re = y`, `z.im = 1`.

### Step 3: Coprimality — gcd(y+i, y-i) is a unit.

Key: gcd(y+i, y-i) divides their difference: `(y+i) - (y-i) = 2i`. Since i is a unit, the gcd divides 2.

In GaussianInt, 2 = -i·(1+i)², so the only prime dividing 2 is 1+i (up to associates).

Test divisibility by 1+i: (1+i) | (a+bi) ↔ a ≡ b (mod 2).
For y+i: a=y (even), b=1 → y ≢ 1 (mod 2). So 1+i ∤ y+i.
Thus no non-unit divides both y+i and y-i → gcd is a unit.

Key lemma: `GaussianInt.instEuclideanDomain` gives UFD. Use `EuclideanDomain.gcd_isUnit_iff` to relate gcd=unit to coprime.

### Step 4: Cube factorization.

Since GaussianInt is a EuclideanDomain → GCDMonoid, and gcd(y+i, y-i) is a unit:

Apply `exists_associated_pow_of_mul_eq_pow` (from `Mathlib.Algebra.GCDMonoid.Basic`):
- `h_coprime : IsUnit (gcd z (conj z))`
- `h_prod : z * (conj z) = (x : GaussianInt) ^ 3`
- Get: `∃ d, Associated (d ^ 3) z`

Interpretation: `z = u * d³` for some unit u.

### Step 5: Absorb unit.

GaussianInt units: {1, -1, i, -i}. All are cubes:
- 1 = 1³, -1 = (-1)³, i = (-i)³, -i = i³

So u = v³ for some v, and `z = (v * d)³`.

Let `a + bi := v * d` (write as `⟨a, b⟩`). Then `y + i = (a + bi)³`.

### Step 6: Expand the cube and equate.

(a + bi)³ = (a³ - 3ab²) + (3a²b - b³)i

Equate: y + i = (a³ - 3ab²) + (3a²b - b³)i

So:
- y = a³ - 3ab² = a(a² - 3b²)
- 1 = 3a²b - b³ = b(3a² - b²)

### Step 7: Solve over ℤ.

From b·(3a² - b²) = 1, since a,b ∈ ℤ:
- b | 1 → b = ±1

Case b = 1: 3a² - 1 = 1 → 3a² = 2 → no integer a.
Case b = -1: 3a² - 1 = -1 → 3a² = 0 → a = 0.

So (a,b) = (0,-1).

### Step 8: Compute x, y.

y = a(a² - 3b²) = 0·(0 - 3) = 0.
From y² + 1 = x³: 0 + 1 = x³ → x = 1.

Thus (x,y) = (1,0). QED.

## Informal Proof: mordell_minus2_solutions_iff

**Statement**: y² = x³ - 2 ↔ (x=3 ∧ y=5) ∨ (x=3 ∧ y=-5)

Same template as d=-1, using ℤ[√-2] instead:
1. Show x,y are odd (mod 4 argument)
2. Factor y² + 2 = x³ in ℤ[√-2]: (y + √-2)(y - √-2) = x³
3. Show factors are coprime (gcd divides 2√-2 = -(√-2)³)
4. Need ℤ[√-2] as UFD: Norm N(a+b√-2) = a² + 2b² is a Euclidean function.
   Mathlib may NOT have `EuclideanDomain` instance for ℤ[√-2]. If missing, prove it:
   - Define norm `N(z) := z.re^2 + 2*z.im^2` (for d=-2, norm uses |d|)
   - Actually `Zsqrtd.norm` for d=-2 gives N(z) = z.re^2 - (-2)*z.im^2 = re² + 2·im²
   - Prove Euclidean property: for a,b with b≠0, ∃q,r s.t. a = qb + r with N(r) < N(b)
5. Apply `exists_associated_pow_of_mul_eq_pow`
6. Units of ℤ[√-2] are ±1 (both cubes): `Zsqrtd.norm_eq_one_iff'` (d≤0) gives units ↔ norm=1
7. Expand (a+b√-2)³ = (a³ - 6ab²) + (3a²b - 2b³)√-2
8. Equate: y = a³ - 6ab², 1 = b(3a² - 2b²)
9. b = ±1, check cases → b=1, a=±1 → y = ±1 - 6(±1) = ∓5
10. x = N(a+b√-2) = a² + 2b² = 1 + 2 = 3

## Notes on Harder Theorems

**mordell_minus5 / mordell_minus6**: d=-5, -6. ℤ[√-5] and ℤ[√-6] are NOT UFDs (class number 2).
Standard proofs use either:
- Kummer's method with class group exponent coprime to 3
- Descent using binary quadratic forms
- Both are beyond current Mathlib infrastructure

**mordell_minus13**: Same difficulty as d=-5, -6. Class number 2.

**mordell_d**: This is a deep general theorem. The statement uses `quadClassNumber` axiom which must eventually be replaced. This theorem is likely not provable with current Mathlib.

## Prover Instructions

1. Read this file and `task_pending.md`
2. Edit `MordellArchon/Basic.lean`:
   - Add required imports
   - Fill sorries starting with `mordell_minus1_solution_iff`
   - Save partial work even if incomplete — use scoped `sorry` for stuck subgoals
3. Write results to `task_results/MordellArchon_Basic.lean.md`
4. Do NOT modify theorem statements
5. Do NOT edit `PROGRESS.md`, `task_pending.md`, or `task_done.md`
