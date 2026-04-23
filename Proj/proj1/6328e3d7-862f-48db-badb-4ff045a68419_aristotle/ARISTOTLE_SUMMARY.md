# Summary of changes for run 6328e3d7-862f-48db-badb-4ff045a68419
## Euler's Special Case of Catalan's Conjecture (x² - y³ = 1)

I formalized a proof that the Diophantine equation x² - y³ = 1 has the unique positive integer solution (x, y) = (3, 2). The proof is in `RequestProject/Euler.lean`.

### What was proved

The file contains the main theorem `euler_catalan` and all supporting lemmas:

1. **`not_sq_of_y_eq_one_mod_three`** — If y ≡ 1 mod 3, then y³ + 1 ≡ 2 mod 3, which is never a perfect square. ✅

2. **`no_cubes_differ_by_two`** — No two positive perfect cubes differ by exactly 2 (key ingredient for the odd y case). ✅

3. **`no_solution_y_odd`** — If y is odd, x² ≠ y³ + 1. The proof factors (x-1)(x+1) = y³, shows gcd(x-1, x+1) = 1 (both odd, differ by 2), concludes both are perfect cubes, then invokes the "no cubes differ by 2" lemma. ✅

4. **`euler_catalan`** (main theorem) — For positive integers x, y with x² = y³ + 1, we have x = 3 and y = 2. The proof:
   - Eliminates odd y (using `no_solution_y_odd`)
   - Eliminates y ≡ 1 mod 3 (using modular arithmetic)
   - For small y (≤ 2): direct computation
   - For y ≥ 3 even: factors x² = (y+1)(y²-y+1), analyzes gcd(y+1, y²-y+1) | 3
   - gcd = 1 case: forces y = 1 via (2t-2y+1)(2t+2y-1) = 3, contradiction
   - gcd = 3 case: writes y+1 = 3a², y²-y+1 = 3b², reduces to b² = 3a⁴-3a²+1
   ✅ (modulo one auxiliary lemma)

### One remaining `sorry`

5. **`not_sq_3s4_sub_3s2_add_1`** — For s ≥ 2, the value 3s⁴ - 3s² + 1 is not a perfect square. This is the core number-theoretic difficulty, equivalent to showing the Pell equation X² - 3Y² = 1 has no solution (X, Y) with X even and (Y+1)/2 being a perfect square ≥ 4. ❌ (`sorry`)

This lemma is a classically well-known result, but its formalization requires either:
- Unique factorization in the Eisenstein integers ℤ[ω] (not available in Mathlib), or
- A covering system of congruences on the associated Pell recurrence sequence (requires verifying a large finite computation with LCM ≈ 6×10⁸)

The proof architecture is fully correct — the main theorem follows immediately from the five lemmas, and four of the five are fully proved without any `sorry`.