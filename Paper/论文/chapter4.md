# 第4章 Mordell 方程的数学证明结构与 Lean 4 形式化实现

## 4.1 本章定位与章节分工

本文以 Mordell 方程整数解问题为案例，研究复杂数学证明在 Lean 4 中的形式化表达以及 AI 辅助证明开发的方法。由于附录 A 已经给出了 Mordell 主定理的较完整纸笔推导，本章不再重复全部证明细节，而是围绕“哪些数学步骤需要被形式化、它们在 Lean 4 中如何表达、哪些地方构成主要困难”展开。

本章的写法采用“数学结构 + Lean 代码片段 + 形式化说明”的方式。数学上只保留证明主线和关键节点；Lean 代码只展示核心定义、定理接口和少量代表性证明片段，完整代码可见项目文件和附录 B。第 5 章则在本章基础上，专门分析 AI 工具在这些 Lean 4 形式化任务中的辅助效果。

本文关注的 Mordell 方程为

$$
y^2=x^3+d,\qquad x,y,d\in\mathbb Z.
$$

主要处理的参数为

$$
d=-1,-2,-5,-6,-13.
$$

本章涉及的 Lean 4 文件如下。

| 文件 | 主要作用 |
| --- | --- |
| `ZsqrtdBasic.lean` | 二次整数环、范数和代数结构 |
| `Dedekind.lean` | $\mathbb Z[\sqrt d]$ 的 Dedekind 整环实例 |
| `Descent.lean` | Mordell 下降法核心证明 |
| `ClassGroupApprox.lean` | 类群代表元约化 |
| `ClassNumberSmall.lean` | 小参数类数条件验证 |
| `Solutions.lean` | 具体 Mordell 方程的解或无解结论 |

## 4.2 Mordell 方程概述与 Lean 建模

Mordell 方程是整数方程和椭圆曲线理论中的经典对象。1914 年，Mordell 系统研究了一般形式的方程

$$
y^2=x^3+d,\qquad x,y,d\in\mathbb Z.
$$

本文采用该方程作为 Lean 4 形式化案例，是因为它同时涉及初等整数算术、二次整数环、范数、理想分解、类群和具体参数验证等多个层次，能够较好体现复杂数学证明进入证明助手时的拆解过程。

在 Lean 4 中，Mordell 方程可以直接建模为整数等式。若单独定义谓词，可写为：

```lean
def IsMordellSolution (d x y : ℤ) : Prop :=
  y ^ 2 = x ^ 3 + d
```

在实际证明中，本文更多直接把方程作为定理假设：

```lean
(h_eqn : y ^ 2 = x ^ 3 + d)
```

这种写法便于后续用 `rw`、`linarith`、`ring` 等 tactic 处理等式变形。与普通数学表达相比，Lean 4 中必须明确变量类型，例如 `d x y : ℤ`，也必须明确整数、自然数、有理数和二次整数环元素之间的类型转换。

## 4.3 主要数学结论与 Lean 总接口

本文形式化的核心数学结论可以概括如下。

**定理 4.1（Mordell 基本结论）**  
设 $d<0$ 为无平方因子的整数，满足

$$
d\equiv 2\ \text{或}\ 3\pmod4,
$$

且

$$
3\nmid h(\mathbb Z[\sqrt d]).
$$

若整数 $x,y$ 满足

$$
y^2=x^3+d,
$$

则存在整数 $m$，使

$$
d=1-3m^2\quad\text{或}\quad d=-1-3m^2,
$$

并且

$$
y=m(3d+m^2).
$$

在 Lean 4 中，对应的总接口是 `mordell_d`：

```lean
theorem mordell_d (d : ℤ) (hd : d ≤ -1)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ m : ℤ, (d = 1 - 3 * m ^ 2 ∨ d = -1 - 3 * m ^ 2) ∧
      y = m * (3 * d + m ^ 2)
```

这里可以看到，普通数学中的前提在 Lean 中都必须显式出现：`d ≤ -1` 表示负参数条件，`h_mod` 表示同余条件，`h_sqf` 表示无平方因子条件，`hcl` 表示类数与 $3$ 互素。

需要注意的是，正文数学定理常写成 $m\in\mathbb Z_{\ge0}$ 并带有正负号；而 Lean 中先得到一个 `m : ℤ`，把正负号吸收到整数 $m$ 的符号中。这种写法更适合形式化证明，也减少了自然数与整数之间的类型转换。

## 4.4 二次整数环与范数的形式化

证明 Mordell 方程的关键，是把

$$
y^2-d=x^3
$$

放入二次整数环

$$
\mathbb Z[\sqrt d]
$$

中处理。该环中的元素写成

$$
a+b\sqrt d,\qquad a,b\in\mathbb Z,
$$

范数为

$$
N(a+b\sqrt d)=a^2-db^2.
$$

在 Mathlib4 中，二次整数环对应 `ℤ√d`，元素的实部和虚部分别为 `re` 和 `im`。本文需要证明显式范数与代数范数一致：

```lean
lemma zsqrtd_algebra_norm (d : ℤ) (z : ℤ√d) :
    Algebra.norm ℤ z = z.norm := by
  rcases z with ⟨a, b⟩
  simpa [Zsqrtd.norm, mul_assoc] using zsqrtd_algebra_norm_mk d a b
```

这一代码片段体现了形式化中的一个基本特点：纸笔证明中一句“范数公式为 $a^2-db^2$”，在 Lean 中需要先固定具体结构 `ℤ√d`，再证明库中的 `Algebra.norm` 与手写范数 `z.norm` 一致。该结果后续会用于理想、单位和类群相关证明。

## 4.5 方程分解与主理想等式

Mordell 方程可改写为

$$
y^2-d=x^3.
$$

在 $\mathbb Z[\sqrt d]$ 中有分解

$$
(y+\sqrt d)(y-\sqrt d)=x^3.
$$

Lean 4 中对应的基础引理是：

```lean
theorem factor_y_sq_sub_d (d y : ℤ) :
    ((y ^ 2 - d : ℤ) : ℤ√d) =
      (⟨y, 1⟩ : ℤ√d) * ⟨y, -1⟩ := by
  ext
  · simp [pow_two]
    ring
  · simp [pow_two]
```

这里 `⟨y, 1⟩` 表示 $y+\sqrt d$，`⟨y,-1⟩` 表示 $y-\sqrt d$。证明本身只是代数展开，所以可以由 `ring` 处理。

下一步是将元素等式提升为主理想等式：

$$
\langle y+\sqrt d\rangle\langle y-\sqrt d\rangle=\langle x\rangle^3.
$$

这一步在数学上很自然，但在 Lean 中要显式使用 `Ideal.span`、单元素生成理想、理想乘法和理想幂。对应的关键接口是：

```lean
theorem span_y_add_sqrtd_eq_ideal_cube_of_coprime
    (d x y : ℤ) [IsDomain (ℤ√d)] [IsDedekindDomain (ℤ√d)]
    (hcop : IsCoprime
      (Ideal.span ({(⟨y, 1⟩ : ℤ√d)} : Set (ℤ√d)))
      (Ideal.span ({(⟨y, -1⟩ : ℤ√d)} : Set (ℤ√d))))
    (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ I : Ideal (ℤ√d),
      Ideal.span ({(⟨y, 1⟩ : ℤ√d)} : Set (ℤ√d)) = I ^ 3
```

该定理表达的是：只要两个主理想互素，方程分解就能推出 $\langle y+\sqrt d\rangle$ 是某个理想的三次方。

## 4.6 互素性证明

完整的互素性证明见附录 A。正文只保留其关键结构：若某个素理想同时整除

$$
\langle y+\sqrt d\rangle
\quad\text{和}\quad
\langle y-\sqrt d\rangle,
$$

则它会同时控制 $x$ 和 $2y$。结合 $d$ 无平方因子、$\gcd(x,y)=1$ 以及 $x$ 为奇数，可以推出矛盾。因此两个主理想互素。

在 Lean 中，互素性最终被写成如下定理：

```lean
theorem span_y_add_sqrtd_coprime
    (d x y : ℤ)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (h_eqn : y ^ 2 = x ^ 3 + d) :
    IsCoprime
      (Ideal.span ({(⟨y, 1⟩ : ℤ√d)} : Set (ℤ√d)))
      (Ideal.span ({(⟨y, -1⟩ : ℤ√d)} : Set (ℤ√d)))
```

这一部分的形式化难点在于，纸笔证明中的“互素”需要被转化为理想层面的 `IsCoprime`，而理想层面的证明又需要回到整数中的整除和模运算。项目中先证明辅助结论：

```lean
lemma x_odd_two_three {x y d : ℤ}
    (hd : d % 4 = 2 ∨ d % 4 = 3)
    (h_eqn : y ^ 2 - d = x ^ 3) :
    ¬ Even x
```

这对应数学中“$x$ 必为奇数”的步骤。该类证明主要由 `ZMod`、`norm_num` 和 `omega` 等工具完成。

## 4.7 类群下降与单位因子

互素性给出理想三次方后，还需要利用类群条件

$$
3\nmid h(\mathbb Z[\sqrt d])
$$

把理想三次方下降为元素三次方。数学上，若

$$
\langle y+\sqrt d\rangle=\mathfrak a^3,
$$

则在类群中有 $[\mathfrak a]^3=1$。由于 $3$ 与类群阶数互素，得到 $[\mathfrak a]=1$，所以 $\mathfrak a$ 是主理想。再处理单位因子后，可得到

$$
y+\sqrt d=(a+b\sqrt d)^3.
$$

Lean 中类群下降的核心引理为：

```lean
theorem ideal_isPrincipal_of_cube_isPrincipal
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {I : Ideal R} (hI0 : I ∈ (Ideal R)⁰)
    (hcl : Nat.gcd 3 (Nat.card (ClassGroup R)) = 1)
    (hI3 : (I ^ 3).IsPrincipal) :
    I.IsPrincipal
```

处理单位因子的关键结论是：

```lean
theorem zsqrtd_units_cubes {d : ℤ} (hd : d ≤ -1) (u : (ℤ√d)ˣ) :
    ∃ v : (ℤ√d)ˣ, u = v ^ 3
```

最后打包得到：

```lean
theorem exists_cube_root_y_add_sqrtd
    (d : ℤ) (hd : d ≤ -1)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ z : ℤ√d, z ^ 3 = (⟨y, 1⟩ : ℤ√d)
```

这就是从原方程进入“比较三次方系数”的桥梁。

## 4.8 系数比较与参数化结论

由上一节得到

$$
y+\sqrt d=(a+b\sqrt d)^3.
$$

展开并比较系数，可推出 $b=\pm1$，进一步得到

$$
d=1-3a^2
\quad\text{或}\quad
d=-1-3a^2,
$$

以及

$$
y=a(a^2+3d).
$$

在 Lean 中，这一步被封装为：

```lean
theorem mordell_arithmetic_of_cube {d y : ℤ} {z : ℤ√d}
    (hz : z ^ 3 = (⟨y, 1⟩ : ℤ√d)) :
    ∃ m : ℤ, (d = 1 - 3 * m ^ 2 ∨ d = -1 - 3 * m ^ 2) ∧
      y = m * (3 * d + m ^ 2)
```

该证明主要依赖两个展开引理：

```lean
private lemma cube_re (a b d : ℤ) :
    ((⟨a, b⟩ : ℤ√d) ^ 3).re =
      a * (3 * d * b ^ 2 + a ^ 2)

private lemma cube_im (a b d : ℤ) :
    ((⟨a, b⟩ : ℤ√d) ^ 3).im =
      b * (d * b ^ 2 + 3 * a ^ 2)
```

这类目标数学上只是代数展开，但在 Lean 中需要明确取实部 `re` 和虚部 `im`，再用 `congrArg` 将二次整数环中的等式转化为整数等式。

反方向验证则是纯代数恒等式：

```lean
theorem mordell_param_solution {R : Type*} [CommRing R] (d m : R)
    (hd : d = 1 - 3 * m ^ 2 ∨ d = -1 - 3 * m ^ 2) :
    (m * (3 * d + m ^ 2)) ^ 2 = (m ^ 2 - d) ^ 3 + d := by
  rcases hd with rfl | rfl <;> ring
```

这段代码适合作为 AI 辅助实验中的简单成功案例，因为它结构清晰、自动化程度高，`ring` 可以直接完成核心证明。

## 4.9 类群计算与类数条件验证

Mordell 下降法需要输入

$$
3\nmid h(\mathbb Z[\sqrt d]).
$$

对于本文使用的五个参数，需要在 Lean 中分别证明对应类数条件。

当 $d=-1$ 时，$\mathbb Z[i]$ 是高斯整数环，类数为 $1$。当 $d=-2$ 时，项目中构造了 $\mathbb Z[\sqrt{-2}]$ 上的欧几里得结构，因此类数也为 $1$。对应结论为：

```lean
theorem classNumber_gcd_three_neg_one :
    Nat.gcd (quadClassNumber (-1)) 3 = 1

theorem classNumber_gcd_three_neg_two :
    Nat.gcd (quadClassNumber (-2)) 3 = 1
```

对于 $d=-5,-6,-13$，并不需要完整给出类群同构结构。本文只证明每个类群元素至多等于两个候选类之一，从而得到类群阶数至多为 $2$，因此类数不被 $3$ 整除。对应结论为：

```lean
theorem classNumber_gcd_three_neg_five :
    Nat.gcd (quadClassNumber (-5)) 3 = 1

theorem classNumber_gcd_three_neg_six :
    Nat.gcd (quadClassNumber (-6)) 3 = 1

theorem classNumber_gcd_three_neg_thirteen :
    Nat.gcd (quadClassNumber (-13)) 3 = 1
```

其中类群代表元约化的核心思想是：证明每个理想类都有一个包含小整数的代表。Lean 中对应接口包括：

```lean
theorem classGroup_exists_mk0_mem_two_of_neg_six_le
    (d : ℤ) (hd_neg : d < 0) (hd_ge : -6 ≤ d)
    [IsDomain (ℤ√d)] [IsDedekindDomain (ℤ√d)] (C : ClassGroup (ℤ√d)) :
    ∃ J : (Ideal (ℤ√d))⁰,
      C = ClassGroup.mk0 J ∧ (2 : ℤ√d) ∈ (J : Ideal (ℤ√d))

theorem classGroup_exists_mk0_mem_twelve_neg_thirteen
    [IsDomain (ℤ√(-13 : ℤ))] [IsDedekindDomain (ℤ√(-13 : ℤ))]
    (C : ClassGroup (ℤ√(-13 : ℤ))) :
    ∃ J : (Ideal (ℤ√(-13 : ℤ)))⁰,
      C = ClassGroup.mk0 J ∧ (12 : ℤ√(-13 : ℤ)) ∈ (J : Ideal (ℤ√(-13 : ℤ)))
```

这部分是形式化难度最高的内容之一。正文只需要说明其作用：它为 `mordell_d` 提供类数条件 `hcl`。完整的类群代表元约化证明和奇偶分类细节不宜放在正文中，否则会淹没主线。

## 4.10 具体参数下的形式化结果

结合 `mordell_d` 和各个小类数结论，可以得到具体 Mordell 方程的解或无解结论。

| 参数 $d$ | 数学结论 | Lean 4 定理 |
| --- | --- | --- |
| $-1$ | 唯一解为 $(1,0)$ | `mordell_minus1_solution_iff` |
| $-2$ | 解为 $(3,\pm5)$ | `mordell_minus2_solutions_iff` |
| $-5$ | 无整数解 | `mordell_minus5` |
| $-6$ | 无整数解 | `mordell_minus6` |
| $-13$ | 解为 $(17,\pm70)$ | `mordell_minus13_solutions_iff` |

例如 $d=-2$ 的最终形式化定理为：

```lean
theorem mordell_minus2_solutions_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 2 ↔
      (x = 3 ∧ y = 5) ∨ (x = 3 ∧ y = -5)
```

$d=-5$ 的无解结论为：

```lean
theorem mordell_minus5 (x y : ℤ) :
    ¬ (y ^ 2 = x ^ 3 - 5)
```

$d=-13$ 的最终形式化定理为：

```lean
theorem mordell_minus13_solutions_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 13 ↔
      (x = 17 ∧ y = 70) ∨ (x = 17 ∧ y = -70)
```

这些定理是第 4 章形式化工作的最终输出。正文展示定理接口即可，具体证明代码较长，适合放入附录或仅在代码仓库中保留。

## 4.11 本章小结

本章将 Mordell 方程的数学证明结构与 Lean 4 形式化实现合并讨论。数学上，证明主线是将

$$
y^2=x^3+d
$$

转化为

$$
(y+\sqrt d)(y-\sqrt d)=x^3,
$$

再通过理想分解、互素性、类群下降和系数比较得到参数化结论。形式化上，该路线被拆解为二次整数环建模、范数公式、理想互素、类群下降、单位吸收、系数比较、类数条件验证和具体参数求解等多个 Lean 4 模块。

由于附录 A 已经给出完整纸笔证明，正文只保留关键数学节点和代表性 Lean 代码片段。这样的安排可以突出本文的重点：不是重新书写 Mordell 方程的全部数论证明，而是说明复杂证明如何被组织成 Lean 4 可检查的形式化结构，并为第 5 章的 AI 辅助证明实验提供任务基础。
