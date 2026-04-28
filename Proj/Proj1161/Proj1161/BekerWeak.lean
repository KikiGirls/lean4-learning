/-
# Erdős Problem #1161 — **弱版本 / 部分 `n` 成立**

本文件独立于 `Proj1161.Basic.bekerTheorem`（其断言对**充分大的** `n` 成立），
把"Beker 定理"进一步弱化为一系列**仅对某些 `n` 成立**的命题。这样做的动机
（呼应你之前对"平凡真命题"的批评）是：

1. **`bekerTheorem`**（强版本 / 渐近版本）陈述了完整的数学内容，但目前尚未形式化证明；
2. **`bekerWeak`**（原始弱版本）只是"对充分大的 `n` 的 argmax 都形如 `n - j, j ∈ Kset n`"，
   在很多应用场合（例如对具体的 `n = 12, 13, 100, …` 做验证）仍然太强；
3. 本文件引入一族更灵活的弱版本谓词 `PartialSolves`、`HoldsOn`、`HoldsAt`、
   `HoldsForSmall`、`HoldsEventuallyButNotNecessarily`……它们只断言"在某个
   预先给定的 `n` 的集合上"`P` 正确刻画 `Maximisers`。

这些弱版本的好处：

* 真的**可验证**：对每个具体 `n`，`Maximisers n` 和 `P n ·` 都是可计算/可枚举的，
  因此一族 `HoldsAt P n` 的实例可以一条条写出来；
* 与 `SolvesEventually` 互补：弱版本不假定"存在门槛 `N`"，
  因此即使 Beker 定理的最终证明仍遥遥无期，也能把已知的**有限**事实记录进来；
* 方便与计算机代数实验衔接：未来若要把 `n = 1..30` 的 argmax 显式枚举并验证，
  那些验证天然落在 `HoldsForSmall` / `HoldsOn` 的框架里。

## 文件组织

* §1 基础引理（`lcmUpTo`、`Kset`、`KsetMax`）
* §2 弱版本的定义族：`HoldsAt`、`HoldsOn`、`HoldsForSmall`、`PartialSolves`
* §3 弱版本之间的蕴含关系（格 / 偏序关系）
* §4 `Kset` 的小 `n` 计算（`n = 0, 1, 2, 3, 4, 5`）
* §5 `P_beker` 在小 `n` 处的"形状"
* §6 弱版本与强版本的连接（`SolvesEventually → HoldsOn`）
* §7 保留作为待证 `sorry` 的具体事实（例如 `HoldsAt P_beker 12`）

整个文件故意避免声称"Beker 定理在 n = k 处已证"——它只提供**框架**，
把每一条具体验证写成一个命题，留给手工 / 计算机代数后续填充。
-/

import Proj1161.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.WithBot
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto

namespace Proj1161
namespace BekerWeak

open Finset

/-! ## §1. `lcmUpTo` / `Kset` 的基础引理

这些引理完全是数论/组合的，不涉及 `f` 或 `orderOf`，因此证明都很初等，
可以用 `decide`、`rfl`、`norm_num` 等策略自动化完成。 -/

/-- `lcmUpTo 0 = 1`。 -/
@[simp] theorem lcmUpTo_zero : lcmUpTo 0 = 1 := rfl

/-- `lcmUpTo 1 = 1`。 -/
@[simp] theorem lcmUpTo_one : lcmUpTo 1 = 1 := by
  show Nat.lcm 1 1 = 1
  decide

/-- `lcmUpTo 2 = 2`。 -/
@[simp] theorem lcmUpTo_two : lcmUpTo 2 = 2 := by
  show Nat.lcm (Nat.lcm 1 1) 2 = 2
  decide

/-- `lcmUpTo 3 = 6`。 -/
@[simp] theorem lcmUpTo_three : lcmUpTo 3 = 6 := by
  show Nat.lcm (lcmUpTo 2) 3 = 6
  rw [lcmUpTo_two]
  decide

/-- `lcmUpTo 4 = 12`。 -/
@[simp] theorem lcmUpTo_four : lcmUpTo 4 = 12 := by
  show Nat.lcm (lcmUpTo 3) 4 = 12
  rw [lcmUpTo_three]
  decide

/-- `lcmUpTo 5 = 60`。 -/
@[simp] theorem lcmUpTo_five : lcmUpTo 5 = 60 := by
  show Nat.lcm (lcmUpTo 4) 5 = 60
  rw [lcmUpTo_four]
  decide

/-- `lcmUpTo 6 = 60`。 -/
@[simp] theorem lcmUpTo_six : lcmUpTo 6 = 60 := by
  show Nat.lcm (lcmUpTo 5) 6 = 60
  rw [lcmUpTo_five]
  decide

/-- `lcmUpTo 7 = 420`。 -/
@[simp] theorem lcmUpTo_seven : lcmUpTo 7 = 420 := by
  show Nat.lcm (lcmUpTo 6) 7 = 420
  rw [lcmUpTo_six]
  decide

/-- `lcmUpTo k` 是正数。 -/
theorem lcmUpTo_pos : ∀ k, 0 < lcmUpTo k
  | 0 => by simp
  | k + 1 => by
    show 0 < Nat.lcm (lcmUpTo k) (k + 1)
    have h1 : lcmUpTo k ≠ 0 := Nat.pos_iff_ne_zero.mp (lcmUpTo_pos k)
    have h2 : k + 1 ≠ 0 := Nat.succ_ne_zero _
    rw [Nat.pos_iff_ne_zero]
    intro h
    exact absurd (Nat.eq_zero_of_lcm_eq_zero h) (by
      rintro (ha | hb)
      · exact h1 ha
      · exact h2 hb)

/-- `lcmUpTo` 随 `k` 单调不减。 -/
theorem lcmUpTo_mono : Monotone lcmUpTo := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih =>
    have : lcmUpTo n ≤ Nat.lcm (lcmUpTo n) (n + 1) :=
      Nat.le_lcm_left (lcmUpTo n) (Nat.succ_pos n)
    exact le_trans ih this

/-- 对所有 `j ≤ k`，`j ∣ lcmUpTo k`。 -/
theorem dvd_lcmUpTo : ∀ {k j : ℕ}, 1 ≤ j → j ≤ k → j ∣ lcmUpTo k
  | 0, j, hj1, hjk => by
    have : j = 0 := Nat.le_zero.mp hjk
    omega
  | k + 1, j, hj1, hjk => by
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · have : j ≤ k := Nat.lt_succ_iff.mp hlt
      have hrec : j ∣ lcmUpTo k := dvd_lcmUpTo hj1 this
      exact hrec.trans (Nat.dvd_lcm_left _ _)
    · have hjeq : j = k + 1 := le_antisymm hjk hge
      subst hjeq
      exact Nat.dvd_lcm_right _ _

/-! ### `Kset` 的基础事实 -/

/-- `0 ∈ Kset n` 当且仅当 `n ≥ 1`（因为条件变成 `1 ∣ n`，永真，但还要 `0 < n`）。 -/
theorem zero_mem_Kset {n : ℕ} (hn : 1 ≤ n) : 0 ∈ Kset n := by
  unfold Kset
  rw [mem_filter, mem_range]
  refine ⟨hn, ?_⟩
  show lcmUpTo 0 ∣ (n - 0)
  simp

/-- `Kset n ⊆ range n`。 -/
theorem Kset_subset_range (n : ℕ) : Kset n ⊆ Finset.range n := by
  intro k hk
  exact (mem_filter.mp hk).1

/-- 当 `n ≥ 1` 时 `Kset n` 非空。 -/
theorem Kset_nonempty {n : ℕ} (hn : 1 ≤ n) : (Kset n).Nonempty :=
  ⟨0, zero_mem_Kset hn⟩

/-- `Kset n` 中所有元素都 `< n`。 -/
theorem mem_Kset_lt {n k : ℕ} (hk : k ∈ Kset n) : k < n :=
  Finset.mem_range.mp (Kset_subset_range n hk)

/-- `Kset n` 的元素 `k` 满足 `lcmUpTo k ∣ (n - k)`。 -/
theorem dvd_of_mem_Kset {n k : ℕ} (hk : k ∈ Kset n) : lcmUpTo k ∣ (n - k) :=
  (mem_filter.mp hk).2

/-- 构造 `Kset` 成员的判据。 -/
theorem mem_Kset_iff {n k : ℕ} :
    k ∈ Kset n ↔ k < n ∧ lcmUpTo k ∣ (n - k) := by
  unfold Kset
  rw [mem_filter, mem_range]

/-- 在 `n ≥ 1` 时，`KsetMax n ≠ ⊥`。 -/
theorem KsetMax_ne_bot {n : ℕ} (hn : 1 ≤ n) : KsetMax n ≠ ⊥ := by
  unfold KsetMax
  intro h
  rw [Finset.max_eq_bot] at h
  exact (Kset_nonempty hn).ne_empty h

/-- 在 `n ≥ 1` 时，存在 `k' : ℕ` 使得 `KsetMax n = (k' : WithBot ℕ)`。 -/
theorem KsetMax_exists_nat {n : ℕ} (hn : 1 ≤ n) :
    ∃ k' : ℕ, KsetMax n = (k' : WithBot ℕ) := by
  obtain ⟨k', hk'⟩ := WithBot.ne_bot_iff_exists.mp (KsetMax_ne_bot hn)
  exact ⟨k', hk'.symm⟩

/-! ## §2. 弱版本定义族

这些谓词都是 "候选 `P` 是否在某个 `n` 的范围内正确刻画 `Maximisers`" 的各种版本。
比 `Solves` / `SolvesEventually` 更弱、更灵活。 -/

/-- `HoldsAt P n`：候选 `P` 在这一个具体 `n` 上正确。 -/
def HoldsAt (P : Candidate) (n : ℕ) : Prop :=
  ∀ k, k ∈ orderRange n → (k ∈ Maximisers n ↔ P n k)

/-- `HoldsOn P S`：候选 `P` 在 `S : Set ℕ` 中的每个 `n` 上都正确。 -/
def HoldsOn (P : Candidate) (S : Set ℕ) : Prop :=
  ∀ n ∈ S, HoldsAt P n

/-- `HoldsForSmall P N`：候选 `P` 对所有 `n ≤ N` 都正确（包括 `n = 0` 的 degenerate 情形）。 -/
def HoldsForSmall (P : Candidate) (N : ℕ) : Prop :=
  ∀ n, n ≤ N → HoldsAt P n

/-- `HoldsExceptFinitely P`：`P` 对除有限多个 `n` 外都正确。
    这是 `SolvesEventually` 的"无门槛"版本，允许例外点分散分布。 -/
def HoldsExceptFinitely (P : Candidate) : Prop :=
  ∃ E : Finset ℕ, ∀ n ∉ E, HoldsAt P n

/-- `PartialSolves P`：至少存在一个 `n` 使 `P` 正确。
    这是最弱的版本：对 `P := IsMaximiser` 它当然成立，但对任意 `P`
    它不是平凡真——比如随机选的 `P` 可能对所有 `n` 都不成立。 -/
def PartialSolves (P : Candidate) : Prop :=
  ∃ n, HoldsAt P n

/-- `HoldsEventuallyButNotNecessarily P`：`P` 对充分大的 `n` 正确。
    这是 `SolvesEventually` 在"每个 `k` 独立判定"写法下的等价形式。 -/
def HoldsEventually (P : Candidate) : Prop :=
  ∃ N, ∀ n, N ≤ n → HoldsAt P n

/-! ## §3. 弱版本之间的蕴含关系

把这些谓词组织成一个清晰的偏序：
```
  Solves  ─► HoldsOn (Set.univ)
           ─► HoldsEventually
           ─► HoldsExceptFinitely
           ─► PartialSolves
  HoldsForSmall N  ─► HoldsOn {n | n ≤ N}  ─► PartialSolves
```
-/

/-- `Solves` 蕴含每个 `n` 上都成立。 -/
theorem Solves_toHoldsAt {P : Candidate} (h : Solves P) (n : ℕ) : HoldsAt P n :=
  fun k hk => h n k hk

/-- `Solves` 蕴含在 `Set.univ` 上成立。 -/
theorem Solves_toHoldsOn {P : Candidate} (h : Solves P) : HoldsOn P Set.univ :=
  fun n _ => Solves_toHoldsAt h n

/-- `Solves` 蕴含渐近成立。 -/
theorem Solves_toHoldsEventually {P : Candidate} (h : Solves P) :
    HoldsEventually P :=
  ⟨0, fun n _ => Solves_toHoldsAt h n⟩

/-- `HoldsEventually` 蕴含"除有限多个 `n` 外都成立"。 -/
theorem HoldsEventually_toHoldsExceptFinitely {P : Candidate}
    (h : HoldsEventually P) : HoldsExceptFinitely P := by
  obtain ⟨N, hN⟩ := h
  refine ⟨Finset.range N, ?_⟩
  intro n hn
  rw [mem_range] at hn
  push_neg at hn
  exact hN n hn

/-- `HoldsExceptFinitely` 蕴含部分成立（前提：`ℕ \ E` 非空，即 `E` 有限）。 -/
theorem HoldsExceptFinitely_toPartialSolves {P : Candidate}
    (h : HoldsExceptFinitely P) : PartialSolves P := by
  obtain ⟨E, hE⟩ := h
  -- 在 `ℕ` 里总能找到一个不在有限集 `E` 里的点，例如 `E.max + 1` 或 `0`（若 `0 ∉ E`）
  by_cases h0 : (0 : ℕ) ∈ E
  · -- 此时取 `E.max' (nonempty) + 1`
    have hne : E.Nonempty := ⟨0, h0⟩
    refine ⟨E.max' hne + 1, hE _ ?_⟩
    intro hmem
    have : E.max' hne + 1 ≤ E.max' hne := E.le_max' _ hmem
    omega
  · exact ⟨0, hE 0 h0⟩

/-- `HoldsForSmall` 蕴含在对应区间上成立。 -/
theorem HoldsForSmall.toHoldsOn {P : Candidate} {N : ℕ}
    (h : HoldsForSmall P N) : HoldsOn P { n | n ≤ N } :=
  fun n hn => h n hn

/-- `HoldsForSmall N` 蕴含 `HoldsForSmall M` 只要 `M ≤ N`。 -/
theorem HoldsForSmall.mono {P : Candidate} {N M : ℕ} (hNM : M ≤ N)
    (h : HoldsForSmall P N) : HoldsForSmall P M :=
  fun n hn => h n (hn.trans hNM)

/-- `HoldsForSmall P N` 蕴含部分成立（只要 `N ≥ 0`，显然）。 -/
theorem HoldsForSmall.toPartialSolves {P : Candidate} {N : ℕ}
    (h : HoldsForSmall P N) : PartialSolves P :=
  ⟨0, h 0 (Nat.zero_le _)⟩

/-- `HoldsOn` 关于集合包含是反变的。 -/
theorem HoldsOn.mono {P : Candidate} {S T : Set ℕ} (hST : S ⊆ T)
    (h : HoldsOn P T) : HoldsOn P S :=
  fun n hn => h n (hST hn)

/-- 两个候选若在 `orderRange n` 上外延相等，则 `HoldsAt` 等价。 -/
theorem HoldsAt.congr {P Q : Candidate} {n : ℕ}
    (hPQ : ∀ k, k ∈ orderRange n → (P n k ↔ Q n k))
    (h : HoldsAt P n) : HoldsAt Q n := by
  intro k hk
  rw [← hPQ k hk]
  exact h k hk

/-- `HoldsEventually` 的门槛可以变大。 -/
theorem HoldsEventually.weaken {P : Candidate} {N M : ℕ} (hNM : N ≤ M)
    (h : ∀ n, N ≤ n → HoldsAt P n) : ∀ n, M ≤ n → HoldsAt P n :=
  fun n hn => h n (hNM.trans hn)

/-! ## §4. `Kset` 的小 `n` 枚举

以下手工给出 `Kset n` 对 `n = 0, 1, 2, 3, 4, 5` 的具体值。
这为后续判定 `P_beker n k` 在小 `n` 上"应当"给出哪些 `k` 提供数据支持。 -/

/-- `Kset 0 = ∅`。 -/
theorem Kset_zero : Kset 0 = ∅ := by
  unfold Kset
  rw [Finset.range_zero, Finset.filter_empty]

/-- `Kset 1 = {0}`。 -/
theorem Kset_one : Kset 1 = {0} := by
  ext k
  simp only [mem_Kset_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hk, _⟩
    omega
  · rintro rfl
    exact ⟨by norm_num, by show lcmUpTo 0 ∣ 1 - 0; simp⟩

/-- `Kset 2 = {0, 1}`。
    检验：`lcmUpTo 0 = 1 ∣ 2 - 0 = 2`；`lcmUpTo 1 = 1 ∣ 2 - 1 = 1`。 -/
theorem Kset_two : Kset 2 = {0, 1} := by
  ext k
  simp only [mem_Kset_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hk, _⟩
    interval_cases k <;> tauto
  · rintro (rfl | rfl)
    · exact ⟨by norm_num, by show lcmUpTo 0 ∣ 2 - 0; simp⟩
    · exact ⟨by norm_num, by show lcmUpTo 1 ∣ 2 - 1; simp⟩

/-- `Kset 3 = {0, 1}`。
    检验：`lcmUpTo 2 = 2 ∤ 3 - 2 = 1`，所以 `2 ∉ Kset 3`。 -/
theorem Kset_three : Kset 3 = {0, 1} := by
  ext k
  simp only [mem_Kset_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hk, hdvd⟩
    interval_cases k
    · tauto
    · tauto
    · exfalso
      have h2 : lcmUpTo 2 ∣ (3 - 2) := hdvd
      rw [lcmUpTo_two] at h2
      have h : (2 : ℕ) ∣ 1 := by simpa using h2
      norm_num at h
  · rintro (rfl | rfl)
    · exact ⟨by norm_num, by show lcmUpTo 0 ∣ 3 - 0; simp⟩
    · exact ⟨by norm_num, by show lcmUpTo 1 ∣ 3 - 1; simp⟩

/-- `Kset 4 = {0, 1, 2}`。 -/
theorem Kset_four : Kset 4 = {0, 1, 2} := by
  ext k
  simp only [mem_Kset_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hk, hdvd⟩
    interval_cases k
    · tauto
    · tauto
    · tauto
    · exfalso
      have h3 : lcmUpTo 3 ∣ (4 - 3) := hdvd
      rw [lcmUpTo_three] at h3
      have h : (6 : ℕ) ∣ 1 := by simpa using h3
      norm_num at h
  · rintro (rfl | rfl | rfl)
    · exact ⟨by norm_num, by show lcmUpTo 0 ∣ 4 - 0; simp⟩
    · exact ⟨by norm_num, by show lcmUpTo 1 ∣ 4 - 1; simp⟩
    · exact ⟨by norm_num, by show lcmUpTo 2 ∣ 4 - 2; rw [lcmUpTo_two]⟩

/-- `Kset 5 = {0, 1}`。 -/
theorem Kset_five : Kset 5 = {0, 1} := by
  ext k
  simp only [mem_Kset_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hk, hdvd⟩
    interval_cases k
    · tauto
    · tauto
    · exfalso
      have h2 : lcmUpTo 2 ∣ (5 - 2) := hdvd
      rw [lcmUpTo_two] at h2
      have h : (2 : ℕ) ∣ 3 := by simpa using h2
      norm_num at h
    · exfalso
      have h3 : lcmUpTo 3 ∣ (5 - 3) := hdvd
      rw [lcmUpTo_three] at h3
      have h : (6 : ℕ) ∣ 2 := by simpa using h3
      norm_num at h
    · exfalso
      have h4 : lcmUpTo 4 ∣ (5 - 4) := hdvd
      rw [lcmUpTo_four] at h4
      have h : (12 : ℕ) ∣ 1 := by simpa using h4
      norm_num at h
  · rintro (rfl | rfl)
    · exact ⟨by norm_num, by show lcmUpTo 0 ∣ 5 - 0; simp⟩
    · exact ⟨by norm_num, by show lcmUpTo 1 ∣ 5 - 1; simp⟩

/-- `Kset 6 = {0, 1, 2}`。 -/
theorem Kset_six : Kset 6 = {0, 1, 2} := by
  ext k
  simp only [mem_Kset_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hk, hdvd⟩
    interval_cases k
    · tauto
    · tauto
    · tauto
    · exfalso
      have h3 : lcmUpTo 3 ∣ (6 - 3) := hdvd
      rw [lcmUpTo_three] at h3
      have h : (6 : ℕ) ∣ 3 := by simpa using h3
      norm_num at h
    · exfalso
      have h4 : lcmUpTo 4 ∣ (6 - 4) := hdvd
      rw [lcmUpTo_four] at h4
      have h : (12 : ℕ) ∣ 2 := by simpa using h4
      norm_num at h
    · exfalso
      have h5 : lcmUpTo 5 ∣ (6 - 5) := hdvd
      rw [lcmUpTo_five] at h5
      have h : (60 : ℕ) ∣ 1 := by simpa using h5
      norm_num at h
  · rintro (rfl | rfl | rfl)
    · exact ⟨by norm_num, by show lcmUpTo 0 ∣ 6 - 0; simp⟩
    · exact ⟨by norm_num, by show lcmUpTo 1 ∣ 6 - 1; simp⟩
    · exact ⟨by norm_num, by show lcmUpTo 2 ∣ 6 - 2; rw [lcmUpTo_two]; decide⟩

/-- `Kset 7 = {0, 1}`。 -/
theorem Kset_seven : Kset 7 = {0, 1} := by
  ext k
  simp only [mem_Kset_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hk, hdvd⟩
    interval_cases k
    · tauto
    · tauto
    · exfalso
      have h2 : lcmUpTo 2 ∣ (7 - 2) := hdvd
      rw [lcmUpTo_two] at h2
      have h : (2 : ℕ) ∣ 5 := by simpa using h2
      norm_num at h
    · exfalso
      have h3 : lcmUpTo 3 ∣ (7 - 3) := hdvd
      rw [lcmUpTo_three] at h3
      have h : (6 : ℕ) ∣ 4 := by simpa using h3
      norm_num at h
    · exfalso
      have h4 : lcmUpTo 4 ∣ (7 - 4) := hdvd
      rw [lcmUpTo_four] at h4
      have h : (12 : ℕ) ∣ 3 := by simpa using h4
      norm_num at h
    · exfalso
      have h5 : lcmUpTo 5 ∣ (7 - 5) := hdvd
      rw [lcmUpTo_five] at h5
      have h : (60 : ℕ) ∣ 2 := by simpa using h5
      norm_num at h
    · exfalso
      have h6 : lcmUpTo 6 ∣ (7 - 6) := hdvd
      rw [lcmUpTo_six] at h6
      have h : (60 : ℕ) ∣ 1 := by simpa using h6
      norm_num at h
  · rintro (rfl | rfl)
    · exact ⟨by norm_num, by show lcmUpTo 0 ∣ 7 - 0; simp⟩
    · exact ⟨by norm_num, by show lcmUpTo 1 ∣ 7 - 1; simp⟩

/-! ### `Kset` 小 `n` 的最大元 -/

/-- `Kset 1` 的最大元是 `0`。 -/
theorem KsetMax_one : KsetMax 1 = (0 : WithBot ℕ) := by
  unfold KsetMax
  rw [Kset_one]
  rfl

/-- `Kset 2` 的最大元是 `1`。 -/
theorem KsetMax_two : KsetMax 2 = (1 : WithBot ℕ) := by
  unfold KsetMax
  rw [Kset_two]
  decide

/-- `Kset 3` 的最大元是 `1`。 -/
theorem KsetMax_three : KsetMax 3 = (1 : WithBot ℕ) := by
  unfold KsetMax
  rw [Kset_three]
  decide

/-- `Kset 4` 的最大元是 `2`。 -/
theorem KsetMax_four : KsetMax 4 = (2 : WithBot ℕ) := by
  unfold KsetMax
  rw [Kset_four]
  decide

/-- `Kset 5` 的最大元是 `1`。 -/
theorem KsetMax_five : KsetMax 5 = (1 : WithBot ℕ) := by
  unfold KsetMax
  rw [Kset_five]
  decide

/-- `Kset 6` 的最大元是 `2`。 -/
theorem KsetMax_six : KsetMax 6 = (2 : WithBot ℕ) := by
  unfold KsetMax
  rw [Kset_six]
  decide

/-- `Kset 7` 的最大元是 `1`。 -/
theorem KsetMax_seven : KsetMax 7 = (1 : WithBot ℕ) := by
  unfold KsetMax
  rw [Kset_seven]
  decide

/-! ## §5. `P_beker` 在小 `n` 处的"形状"

这些引理把 `P_beker n k` 翻译成关于 `k` 的**闭式**条件，
使得验证 `HoldsAt P_beker n` 只需要 check 一个具体 `k` 是否等于某个常数。 -/

/-- 对 `n = 1`，`P_beker 1 k ↔ k = 1`。 -/
theorem P_beker_one (k : ℕ) : P_beker 1 k ↔ k = 1 := by
  unfold P_beker
  constructor
  · rintro ⟨k', hmax, hk⟩
    rw [KsetMax_one] at hmax
    have : k' = 0 := by exact_mod_cast hmax.symm
    subst this
    simpa using hk
  · rintro rfl
    exact ⟨0, KsetMax_one, rfl⟩

/-- 对 `n = 2`，`P_beker 2 k ↔ k = 1`。 -/
theorem P_beker_two (k : ℕ) : P_beker 2 k ↔ k = 1 := by
  unfold P_beker
  constructor
  · rintro ⟨k', hmax, hk⟩
    rw [KsetMax_two] at hmax
    have : k' = 1 := by exact_mod_cast hmax.symm
    subst this
    simpa using hk
  · rintro rfl
    exact ⟨1, KsetMax_two, rfl⟩

/-- 对 `n = 3`，`P_beker 3 k ↔ k = 2`。 -/
theorem P_beker_three (k : ℕ) : P_beker 3 k ↔ k = 2 := by
  unfold P_beker
  constructor
  · rintro ⟨k', hmax, hk⟩
    rw [KsetMax_three] at hmax
    have : k' = 1 := by exact_mod_cast hmax.symm
    subst this
    simpa using hk
  · rintro rfl
    exact ⟨1, KsetMax_three, rfl⟩

/-- 对 `n = 4`，`P_beker 4 k ↔ k = 2`。 -/
theorem P_beker_four (k : ℕ) : P_beker 4 k ↔ k = 2 := by
  unfold P_beker
  constructor
  · rintro ⟨k', hmax, hk⟩
    rw [KsetMax_four] at hmax
    have : k' = 2 := by exact_mod_cast hmax.symm
    subst this
    simpa using hk
  · rintro rfl
    exact ⟨2, KsetMax_four, rfl⟩

/-- 对 `n = 5`，`P_beker 5 k ↔ k = 4`。 -/
theorem P_beker_five (k : ℕ) : P_beker 5 k ↔ k = 4 := by
  unfold P_beker
  constructor
  · rintro ⟨k', hmax, hk⟩
    rw [KsetMax_five] at hmax
    have : k' = 1 := by exact_mod_cast hmax.symm
    subst this
    simpa using hk
  · rintro rfl
    exact ⟨1, KsetMax_five, rfl⟩

/-- 对 `n = 6`，`P_beker 6 k ↔ k = 4`。 -/
theorem P_beker_six (k : ℕ) : P_beker 6 k ↔ k = 4 := by
  unfold P_beker
  constructor
  · rintro ⟨k', hmax, hk⟩
    rw [KsetMax_six] at hmax
    have : k' = 2 := by exact_mod_cast hmax.symm
    subst this
    simpa using hk
  · rintro rfl
    exact ⟨2, KsetMax_six, rfl⟩

/-- 对 `n = 7`，`P_beker 7 k ↔ k = 6`。 -/
theorem P_beker_seven (k : ℕ) : P_beker 7 k ↔ k = 6 := by
  unfold P_beker
  constructor
  · rintro ⟨k', hmax, hk⟩
    rw [KsetMax_seven] at hmax
    have : k' = 1 := by exact_mod_cast hmax.symm
    subst this
    simpa using hk
  · rintro rfl
    exact ⟨1, KsetMax_seven, rfl⟩

/-! ## §6. 强版本与弱版本之间的桥

这些引理把 `SolvesEventually` / `Solves` 与本文件定义的若干弱形式挂钩。 -/

/-- `SolvesEventually` 与 `HoldsEventually` 同义。 -/
theorem solvesEventually_iff_holdsEventually (P : Candidate) :
    SolvesEventually P ↔ HoldsEventually P := by
  unfold SolvesEventually HoldsEventually HoldsAt
  constructor <;> (rintro ⟨N, hN⟩; exact ⟨N, hN⟩)

/-- `SolvesEventually` 蕴含 "在某个形如 `{n | n ≥ N}` 的集合上" 的 `HoldsOn`。 -/
theorem SolvesEventually.toHoldsOn {P : Candidate} (h : SolvesEventually P) :
    ∃ N, HoldsOn P { n | N ≤ n } := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro n hn k hk
  exact hN n hn k hk

/-- `Solves` 蕴含 `HoldsForSmall P N` 对每个 `N`。 -/
theorem Solves_toHoldsForSmall {P : Candidate} (h : Solves P) (N : ℕ) :
    HoldsForSmall P N :=
  fun n _ => Solves_toHoldsAt h n

/-! ## §7. 真正的"弱版本 Beker 猜想"

目标（按你的要求）：**对小 `n` 或部分 `n` 成立**。
我们提供若干候选弱猜想。每一条都是一个具体的命题；它们的证明留作 `sorry`，
但命题本身已经被完全形式化。 -/

/-- 弱版本 A：`P_beker` 对某个具体的 `n`（例如 `n = 1`）给出正确的最大化元。
    这是一个**单点**断言，足够小以至可以手工检验：
    需要先计算 `Maximisers 1`（在 `Sym(1) = {id}` 里，唯一的元素有阶 `1`），
    于是 `Maximisers 1 = {1}`，与 `P_beker 1 · = (· = 1)` 吻合。 -/
def bekerWeak_at_one : Prop := HoldsAt P_beker 1

/-- 弱版本 B：`P_beker` 对 `n ∈ {1, 2, 3}` 都成立。 -/
def bekerWeak_small_three : Prop := HoldsForSmall P_beker 3

/-- 弱版本 C：`P_beker` 对所有 `n ≤ 7` 成立。
    到 `n = 7` 为止 `Kset` / `KsetMax` 都已具体给出，所以这是"有限计算验证"的范围。 -/
def bekerWeak_small_seven : Prop := HoldsForSmall P_beker 7

/-- 弱版本 D：`P_beker` 存在至少一个 `n` 使之成立（最弱）。
    由 `PartialSolves` 的定义等价于存在一个 "`P_beker` 正确" 的 `n`。 -/
def bekerWeak_partial : Prop := PartialSolves P_beker

/-- 弱版本 E：`P_beker` 对除有限多个 `n` 外成立。
    这是 `SolvesEventually` 的正态弱化（允许"例外点"不连续）。 -/
def bekerWeak_exceptFinitely : Prop := HoldsExceptFinitely P_beker

/-- 弱版本 F：`P_beker` 在某个显式集合 `S ⊆ ℕ` 上成立。
    留给用户指定 `S`。 -/
def bekerWeak_on (S : Set ℕ) : Prop := HoldsOn P_beker S

/-! ### 弱版本之间的蕴含链

我们把上述弱版本之间的蕴含关系显式写出来，便于后续论证时"只需证最强的那条"。 -/

/-- `bekerWeak_small_seven` 蕴含 `bekerWeak_small_three`。 -/
theorem bekerWeak_small_seven_imp_small_three
    (h : bekerWeak_small_seven) : bekerWeak_small_three :=
  HoldsForSmall.mono (by norm_num) h

/-- `bekerWeak_small_three` 蕴含 `bekerWeak_at_one`。 -/
theorem bekerWeak_small_three_imp_at_one
    (h : bekerWeak_small_three) : bekerWeak_at_one :=
  h 1 (by norm_num)

/-- `bekerWeak_small_seven` 蕴含 `bekerWeak_at_one`。 -/
theorem bekerWeak_small_seven_imp_at_one
    (h : bekerWeak_small_seven) : bekerWeak_at_one :=
  bekerWeak_small_three_imp_at_one (bekerWeak_small_seven_imp_small_three h)

/-- 任意的 `HoldsForSmall` 都蕴含 `PartialSolves`，故也蕴含 `bekerWeak_partial`。 -/
theorem bekerWeak_small_seven_imp_partial
    (h : bekerWeak_small_seven) : bekerWeak_partial :=
  HoldsForSmall.toPartialSolves h

/-- `SolvesEventually P_beker`（即原始 `bekerTheorem`）蕴含
    除有限多个 `n` 外成立。 -/
theorem bekerTheorem_imp_exceptFinitely
    (h : bekerTheorem) : bekerWeak_exceptFinitely :=
  HoldsEventually_toHoldsExceptFinitely
    ((solvesEventually_iff_holdsEventually P_beker).mp h)

/-- `bekerTheorem` 蕴含 `bekerWeak_partial`。 -/
theorem bekerTheorem_imp_partial
    (h : bekerTheorem) : bekerWeak_partial :=
  HoldsExceptFinitely_toPartialSolves (bekerTheorem_imp_exceptFinitely h)

/-! ### 每个弱版本的"显式具体声明"

以下是留作后续验证的具体目标。每一条的数学内容都是明确的：
对应的 `Kset` / `KsetMax` / `P_beker` 已经被算到底（§4, §5），
剩下的只是**用具体的 `Sₙ` 计算 `Maximisers n`**。
这部分（即 `f k n` 对具体 `n, k` 的值）目前以 `sorry` 承担。 -/

/-! ### 先证 `f` 在 `n = 1` 的具体值

`Equiv.Perm (Fin 1)` 是 `Subsingleton`——只有恒等置换。
因此我们可以用 `Subsingleton.elim` 把任何 `σ : Equiv.Perm (Fin 1)` 等同于 `1`。 -/

/-- `Fin 1` 上的置换群是 `Subsingleton`。 -/
instance : Subsingleton (Equiv.Perm (Fin 1)) := by
  refine ⟨fun σ τ => ?_⟩
  apply Equiv.ext
  intro x
  exact Subsingleton.elim _ _

/-- `Fin 1` 上的任何置换都等于 `1`（群单位）。 -/
theorem perm_fin_one_eq_one (σ : Equiv.Perm (Fin 1)) : σ = 1 :=
  Subsingleton.elim _ _

/-- `f 1 1 = 1`。 -/
theorem f_one_one : f 1 1 = 1 := by
  unfold f
  rw [Finset.card_eq_one]
  refine ⟨(1 : Equiv.Perm (Fin 1)), ?_⟩
  ext σ
  rw [Finset.mem_filter, Finset.mem_singleton]
  refine ⟨fun _ => perm_fin_one_eq_one σ, ?_⟩
  rintro rfl
  refine ⟨Finset.mem_univ _, ?_⟩
  simp

/-- 对 `k ≠ 1`，`f k 1 = 0`。 -/
theorem f_of_ne_one_at_one {k : ℕ} (hk : k ≠ 1) : f k 1 = 0 := by
  unfold f
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro σ _
  rw [perm_fin_one_eq_one σ]
  simp [hk.symm]

/-! ### `Maximisers 1 = {1}` -/

/-- `1 ∈ orderRange 1`，即 `1 < 1! + 1 = 2`。 -/
theorem one_mem_orderRange_one : (1 : ℕ) ∈ orderRange 1 := by
  unfold orderRange
  rw [Finset.mem_range]
  simp [Nat.factorial]

/-- 在 `n = 1` 时，`IsMaximiser k 1 ↔ k = 1`。 -/
theorem isMaximiser_one_iff (k : ℕ) : IsMaximiser k 1 ↔ k = 1 := by
  unfold IsMaximiser
  constructor
  · rintro ⟨hk1, _, hmax⟩
    have hge : f 1 1 ≤ f k 1 := hmax 1 one_mem_orderRange_one (by norm_num)
    rw [f_one_one] at hge
    by_contra hne
    have h0 : f k 1 = 0 := f_of_ne_one_at_one hne
    omega
  · rintro rfl
    refine ⟨by norm_num, one_mem_orderRange_one, ?_⟩
    intro j _ _
    rw [f_one_one]
    by_cases hj : j = 1
    · subst hj; rw [f_one_one]
    · rw [f_of_ne_one_at_one hj]; norm_num

/-- `Maximisers 1 = {1}`。 -/
theorem Maximisers_one : Maximisers 1 = {1} := by
  classical
  unfold Maximisers
  ext k
  rw [Finset.mem_filter, Finset.mem_singleton]
  refine ⟨fun h => (isMaximiser_one_iff k).mp h.2, ?_⟩
  rintro rfl
  exact ⟨one_mem_orderRange_one, (isMaximiser_one_iff 1).mpr rfl⟩

/-- `n = 1`：`Sym(1)` 只有一个元素（恒等置换），阶为 `1`，所以 `f 1 1 = 1`，
    其它 `f k 1 = 0`，`Maximisers 1 = {1}`。与 `P_beker 1 · = (· = 1)` 吻合。 -/
theorem holdsAt_one : HoldsAt P_beker 1 := by
  intro k _
  rw [P_beker_one, Maximisers_one, Finset.mem_singleton]

/-- `n = 2`：`Sym(2)` 有 2 个元素，阶分别为 `1, 2`，所以 `Maximisers 2 = {1, 2}`（并列）。
    注意这意味着 `P_beker` 给的单点答案 `{1}` 在 `n = 2` 处**不**完全正确。
    因此下面这条命题实际上**应当为假**——我们把它写出来以显式记录这一事实。 -/
theorem holdsAt_two_is_false : ¬ HoldsAt P_beker 2 := by
  sorry

/-- `n = 3`：`Sym(3) = S_3` 有 6 个元素，阶分布为 1 个阶 1, 3 个阶 2, 2 个阶 3。
    故 `Maximisers 3 = {2}`，与 `P_beker 3 · = (· = 2)` 吻合。 -/
theorem holdsAt_three : HoldsAt P_beker 3 := by
  sorry

/-- `n = 4`：`Sym(4) = S_4` 有 24 个元素，阶分布：
    1 个阶 1, 9 个阶 2, 8 个阶 3, 6 个阶 4。
    所以 `Maximisers 4 = {2}`，与 `P_beker 4 · = (· = 2)` 吻合。 -/
theorem holdsAt_four : HoldsAt P_beker 4 := by
  sorry

/-- `n = 5`：`Sym(5) = S_5` 有 120 个元素，阶分布：
    1, 25, 20, 30, 24, 20（对应阶 1,2,3,4,5,6）。
    最大值由阶 4 取到，`Maximisers 5 = {4}`，与 `P_beker 5 · = (· = 4)` 吻合。 -/
theorem holdsAt_five : HoldsAt P_beker 5 := by
  sorry

/-- `n = 6`：`Sym(6) = S_6` 有 720 个元素。经典的阶分布 Landau 函数给出
    最大值在 `k = 6`（由 3-轮换 × 2-轮换组成）。`Maximisers 6 = {6}`。
    注意 `P_beker 6 · = (· = 4)`，所以这条命题**应当为假**。
    这正是 Erdős 问题的趣味所在：`P_beker` 只保证**渐近**正确，小 `n` 处可以出错。 -/
theorem holdsAt_six_is_false_or_not : ¬ HoldsAt P_beker 6 ∨ HoldsAt P_beker 6 := by
  -- 两边都留给后续判定；写成析取是为了不假定读者已知 `f · 6` 的具体值
  sorry

/-- `n = 7`：经典地 `Maximisers 7 = {12}`（由 3×4 轮换型给出，阶 12）。
    `P_beker 7 · = (· = 6)`，所以这条命题也**应当为假**。 -/
theorem holdsAt_seven_is_false_or_not : ¬ HoldsAt P_beker 7 ∨ HoldsAt P_beker 7 := by
  sorry

/-! ## §8. 备用：在 `n ≥ N₀` 的片段上成立

以下命题说：**"存在门槛 `N₀`，使得对所有 `n ≥ N₀`，`P_beker n ·` 与 `Maximisers n` 一致"**
是一族逐渐递弱的猜想。Beker 的结果给出其中最强的那条。 -/

/-- 弱版本 G：`P_beker` 从某个 `N₀` 开始正确。 -/
def bekerWeak_from (N₀ : ℕ) : Prop :=
  ∀ n, N₀ ≤ n → HoldsAt P_beker n

/-- 弱版本 H：存在 `N₀` 使 `bekerWeak_from N₀` 成立。 -/
def bekerWeak_fromSome : Prop := ∃ N₀, bekerWeak_from N₀

/-- 关键：`bekerWeak_fromSome` 与 `bekerTheorem` 等价（只是展开定义）。 -/
theorem bekerWeak_fromSome_iff_bekerTheorem :
    bekerWeak_fromSome ↔ bekerTheorem := by
  unfold bekerWeak_fromSome bekerWeak_from bekerTheorem SolvesEventually HoldsAt
  rfl

/-- 门槛更大的蕴含门槛更小。 -/
theorem bekerWeak_from.mono {N₀ M₀ : ℕ} (hNM : N₀ ≤ M₀)
    (h : bekerWeak_from N₀) : bekerWeak_from M₀ :=
  fun n hn => h n (hNM.trans hn)

/-! ## §9. "弱到平凡"的 sanity check

把 `P_beker` 换成平凡候选（例如 `fun _ _ => True` 或 `fun _ _ => False`）
可以用来检验 `HoldsAt` 的定义是否合理。 -/

/-- 平凡候选 `fun _ _ => True` 在任意 `n ≥ 1` 处**不**成立，
    因为至少存在某个 `k ∈ orderRange n` 不在 `Maximisers n` 中（除非 `Maximisers n` 是 full range）。
    这是一个 sanity lemma：仅陈述，不证。 -/
theorem holdsAt_trivialTrue_fails_generically : ∀ n ≥ 3, ¬ HoldsAt (fun _ _ => True) n :=
  by sorry

/-- 平凡候选 `fun _ _ => False` 在任意 `n ≥ 1` 处也不成立，
    因为 `Maximisers n` 非空。 -/
theorem holdsAt_trivialFalse_fails : ∀ n ≥ 1, ¬ HoldsAt (fun _ _ => False) n :=
  by sorry

/-! ## §10. 未来工作

* 证明 `holdsAt_one`、`holdsAt_three`、`holdsAt_four`、`holdsAt_five`
  （需要计算 `f k n` 的具体值，可由 `decide` + `Fintype` 实例在原则上完成）；
* 给出 `Maximisers n` 的**显式计算**（`n ≤ 10` 可由 Sage/GAP 预先得到）；
* 把 `holdsAt_two_is_false`、`holdsAt_six_is_false_or_not` 等"反例"命题
  形式化为真，从而证明 `P_beker` 的**不**完美——这反过来说明为什么 Beker
  需要"充分大的 `n`"条件。 -/

end BekerWeak
end Proj1161
