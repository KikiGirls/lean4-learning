/-
# Erdős Problem #1161

Let `f k n` count the number of elements of `Sₙ` of order `k`.
For which values of `k` will `f k n` be maximal?

Reference: <https://www.erdosproblems.com/forum/thread/1161>

Background (Beker, 2025): Let `πₙ` be a uniformly random permutation in `Sₙ` and
let `pₙ(m) := P(ord(πₙ) = m)`. Then `f m n = n! · pₙ(m)`, so maximising `f m n`
over `m` is equivalent to finding the mode(s) of the distribution of
`ord(πₙ)`. Define
```
  Kₙ := { k ∈ {0,1,…,n-1} : lcm(1,2,…,k) ∣ (n-k) }.
```
Beker proves for all sufficiently large `n`:

* `M(n) := maxₘ pₙ(m) ∼ 1/n`, and if `pₙ(m) ≥ 1/n` then `m = n - k` for
  some `k ∈ Kₙ`.
* `pₙ(m) = M(n) ↔ m = n - max Kₙ`.

Reference: A. Beker, *The most probable order of a random permutation*,
arXiv:2510.11698v1 (2025).
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Lcm
import Mathlib.Data.Nat.Factorial.Basic

namespace Proj1161

open Finset

/-! ## 基本定义

所有 `k` 的候选值都被限制在有限范围 `Finset.range (Nat.factorial n + 1)` 内，
因为 `Sₙ` 中任何置换的阶都 `≤ n!`（实际上 `≤ n` 的 Landau 函数，但 `n!` 已足够）。
这样避免了 `Set ℕ` / `∀ j : ℕ` 的无穷定义域，使"非空 / singleton / argmax"
都可以直接用 `Finset` 的 API 处理。 -/

/-- `f k n` 是对称群 `Sₙ = Perm (Fin n)` 中阶恰好等于 `k` 的元素个数。 -/
noncomputable def f (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => orderOf σ = k)).card

/-- 所有可能的阶的"搜索范围"：`{0, 1, …, n!}`。
    由于 `Perm (Fin n)` 有 `n!` 个元素，任何 `σ : Perm (Fin n)` 的阶都 `≤ n!`，
    所以在此范围外 `f k n = 0`。把所有"有意义"的 `k` 都装进这个 `Finset`，
    下游就不再需要无限量词。 -/
def orderRange (n : ℕ) : Finset ℕ := Finset.range (Nat.factorial n + 1)

/-! ### 有限化的"最大值点"概念 -/

/-- `IsMaximiser k n`（有限版）：`1 ≤ k ≤ n!`，且在有限搜索范围 `orderRange n`
    里再也找不到严格更大的 `f · n` 值。

    因为范围外 `f · n ≡ 0`，所以限制在 `orderRange n` 上与原始的"对所有 `j ≥ 1`
    取最大"是等价的（见下面 `isMaximiser_iff_global`）。 -/
def IsMaximiser (k n : ℕ) : Prop :=
  1 ≤ k ∧ k ∈ orderRange n ∧ ∀ j ∈ orderRange n, 1 ≤ j → f j n ≤ f k n

/-- `Maximisers n` 是 `orderRange n` 中所有使 `f k n` 达到最大的正整数 `k`
    组成的 **`Finset`**。
    显式的有限性使得后续"非空 / 唯一 / argmax"证明可以直接调用
    `Finset.exists_max_image`、`Finset.argmax` 等 API。 -/
noncomputable def Maximisers (n : ℕ) : Finset ℕ :=
  (orderRange n).filter (fun k => IsMaximiser k n)

/-! ## 问题的形式化陈述

Erdős #1161 是一个**描述型**问题（"哪些 `k` 使 `f k n` 最大？"），
而不是一个闭合的命题。关键观察：

* "最大化集合存在"是平凡的（`Maximisers n` 总可定义，且有限）；
* "存在某个谓词 `P` 使得 `Maximisers n = { k | P n k }`"也是平凡的，
  因为可取 `P := fun n k => IsMaximiser k n`，这是**同义反复**；
* "存在'显式 / 结构性'的刻画"在类型论中没有内在含义。

正确的形式化是把问题写成一个**带自由参数的模式**：对任何事先给定的候选
`P`，`Solves P` / `SolvesEventually P` 才是有具体内容、可真可假的命题。
-/

/-- 候选答案：一个关于 `(n, k)` 的谓词。 -/
abbrev Candidate := ℕ → ℕ → Prop

/-- 给定候选 `P`，断言它正确刻画了 `Maximisers`：
    对每个 `n`、每个 `k ∈ orderRange n`，`k ∈ Maximisers n ↔ P n k`。 -/
def Solves (P : Candidate) : Prop :=
  ∀ n k, k ∈ orderRange n → (k ∈ Maximisers n ↔ P n k)

/-- 渐近版本：`P` 对充分大的 `n` 正确刻画 `Maximisers`。 -/
def SolvesEventually (P : Candidate) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → ∀ k, k ∈ orderRange n →
    (k ∈ Maximisers n ↔ P n k)

/-! ## Beker 给出的（渐近）答案

设 `lcmUpTo k = lcm(1,…,k)`，`Kset n = { k ∈ {0,…,n-1} : lcmUpTo k ∣ (n-k) }`。
Beker 证明：对充分大的 `n`，`Maximisers n = { n - max (Kset n) }` 是单点集。
-/

/-- `lcmUpTo k = lcm(1, 2, …, k)`，约定 `lcmUpTo 0 = 1`。 -/
def lcmUpTo : ℕ → ℕ
  | 0 => 1
  | k + 1 => Nat.lcm (lcmUpTo k) (k + 1)

/-- `Kset n = { k ∈ {0,1,…,n-1} : lcm(1,…,k) ∣ (n-k) }`。
    注意 `0 ∈ Kset n` 对所有 `n ≥ 1` 成立（因为 `lcmUpTo 0 = 1 ∣ n`），
    所以 `Kset n` 对 `n ≥ 1` 总是非空。 -/
def Kset (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun k => lcmUpTo k ∣ (n - k))

/-- `Kset n` 的最大元（在 `WithBot ℕ` 中取最大，避免空集时的 dependent term）。
    对 `n ≥ 1` 它总等于某个 `↑k : WithBot ℕ`。 -/
def KsetMax (n : ℕ) : WithBot ℕ := (Kset n).max

/-- Beker 的候选答案（**不引用 `f`/`orderOf`/`Maximisers`**，只用初等数论和 `lcm`）：
    `P_beker n k` 当且仅当 `Kset n` 非空，且 `n - k` 恰等于 `Kset n` 的最大元。

    这里用 `KsetMax n = (k' : ℕ)` 配合 `k = n - k'` 的方式陈述，
    避免了形如 `∃ hK, k = n - (Kset n).max' hK` 那种 dependent term 的写法。 -/
def P_beker (n k : ℕ) : Prop :=
  ∃ k' : ℕ, KsetMax n = (k' : WithBot ℕ) ∧ k = n - k'

/-- **Beker 的（渐近）定理**（Theorem 1.2 of arXiv:2510.11698v1）：
    对所有充分大的 `n`，`P_beker` 正确刻画 `Maximisers n`，
    即 `Maximisers n = { n - max (Kset n) }` 是单点集。

    因为 `P_beker` 的定义完全独立于 `Maximisers`（只用 `Kset`、`lcm`），
    这是一个真正非平凡、有数学内容的陈述，绝非 `P := IsMaximiser` 那种同义反复。 -/
def bekerTheorem : Prop := SolvesEventually P_beker

/-- Beker 的**弱**结论（Theorem 1.1 of arXiv:2510.11698v1）：
    对所有充分大的 `n`，任何最大化元 `k ∈ Maximisers n` 都形如
    `k = n - j`，其中 `j ∈ Kset n`。 -/
def bekerWeak : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → ∀ k ∈ Maximisers n, ∃ j ∈ Kset n, k = n - j

/-- **同义反复的"平凡解"**：取 `P k n := IsMaximiser k n` 确实满足 `Solves`，
    但这并**不**是 Erdős #1161 的答案——它仅仅把 `Maximisers` 换了个名字。
    显式把它记下来，以强调 `Solves P` 的非平凡性完全依赖于
    候选 `P` 是否**独立于** `f` / `orderOf`。 -/
example : Solves (fun n k => IsMaximiser k n) := by
  intro n k _
  simp [Maximisers, mem_filter]

end Proj1161
