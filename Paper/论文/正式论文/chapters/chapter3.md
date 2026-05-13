# Mordell 方程相关命题的 Lean 4 形式化实现

本文以 Mordell 方程的整数解问题为典型案例，深入研究复杂数学证明在 Lean 4 中的形式化表达以及 AI 辅助证明开发的方法。选择 Mordell 方程作为研究对象，主要因为该问题兼具充足的数学复杂度与成熟的参考依据：Baanen 等人此前已在 Lean 3 中成功形式化了若干 $d < 0$ 情形下的求解过程，并确立了基于类群计算与理想下降法的证明路线[@Baanen2023MordellLean]。本文将在充分吸收其证明思想的基础上，在 Lean 4 与 Mathlib4 环境中对相关定义、引理和证明目标进行重构与拆解，进而沿着该路线完成形式化证明的开发，并借此全面评估 AI 工具在整个证明构建过程中的辅助价值与局限性。

## Mordell 方程概述

首先简要介绍 Mordell 方程本身的历史。

1657 年，Fermat 在一封信中指出，方程
$$
y^2=x^3-2
$$
在正整数中的唯一解是 $(x,y)=(3,5)$[@Fermat1894]。1914 年，Mordell[@Mordell1914] 系统研究了一般形式的方程
$$
y^2=x^3+d,\qquad x,y,d\in\mathbb{Z}.
$$
Mordell 的研究主要关注两个方面：一是给出使方程不存在任何整数解的关于 $d$ 的条件；二是基于理想下降法为某些 $d$ 寻找解的方法。这个方程很快就被称为 Mordell 方程。在二十世纪和二十一世纪，围绕 Mordell 方程的研究不断深入，人们开发出了有效解决 Mordell 方程的技术。Mordell[@Mordell1914, @Mordell1920, @Mordell1969]、Baker[@Baker1968]、Stark[@Stark1973]、Bennett 和 Ghadermarzi[@Bennett2015]等人的研究为 Mordell 方程的理论发展和具体求解提供了重要基础。

在本文的 Lean 4 证明过程中，核心参考的是 Mordell[@Mordell1914] 中一个基于类群下降法得到的存在性结论，用来求 $d=-1,-2,-5,-6,-13$ 等特殊负整数参数下的整数解。

## 使用的主要结论

### Mordell 基本结论

令 $d<0$ 为无平方因子的整数，满足
$$
d\equiv 2\ \text{或}\ 3 \pmod{4},
$$
且假设
$$
3\nmid h(\mathbb{Z}[\sqrt d]).
$$
则 Mordell 方程
$$
y^2=x^3+d
$$
有整数解当且仅当存在 $m\in\mathbb{N}$，使得 $d=-3m^2\pm 1$；此时方程的解满足
$$
y=\pm m(3d+m^2).
$$
```lean
theorem mordell_d (d : ℤ) (hd : d ≤ -1)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ m : ℤ, (d = 1 - 3 * m ^ 2 ∨ d = -1 - 3 * m ^ 2) ∧
      y = m * (3 * d + m ^ 2)
```

上述 Mordell 基本结论是本文后续 Lean 4 形式化实践中的核心数学依据。它将原本关于整数点存在性的数论问题，转化为关于参数 $m$ 的条件判断。在 Lean 4 中，本文将该结论拆成两个方向处理：`mordell_d` 证明任意整数解必须满足上述参数化条件；反向的代数恒等式由 `mordell_param_solution` 给出。该结论的证明见附录 A。这里介绍主要思路。

![Mordell 方程主要证明思路图](mordell_math_proof_strategy.png)
*Mordell 方程主要证明思路图*
<!-- fig:mordell-math-proof-strategy -->

## 从元素分解到理想分解

下降法的第一个步骤是：把整数方程
$$
y^2=x^3+d
$$
在 $\mathbb Z[\sqrt d]$ 中分解为共轭因子的乘积；
$$
(y+\sqrt d)(y-\sqrt d)=x^3.
$$

在lean中需要先分解整数等式
```lean
theorem factor_y_sq_sub_d (d y : ℤ) :
    ((y ^ 2 - d : ℤ) : ℤ√d) =
      (⟨y, 1⟩ : ℤ√d) * ⟨y, -1⟩
```

再用 `factor_y_sq_sub_d` 把整数等式提升为 $\mathbb Z[\sqrt d]$ 中的元素等式：

```lean
have hmul_elem :
    (⟨y, 1⟩ : ℤ√d) * ⟨y, -1⟩ = (x : ℤ√d) ^ 3 := by
  rw [← factor_y_sq_sub_d]
  exact_mod_cast hsub
```


接着需要把这个等式转化为主理想等式。记
$$
I=\langle y+\sqrt d\rangle,\qquad
J=\langle y-\sqrt d\rangle,\qquad
A=\langle x\rangle.
$$
由主理想乘法公式 $\langle a\rangle\langle b\rangle=\langle ab\rangle$ 和主理想幂公式 $\langle a\rangle^3=\langle a^3\rangle$，上面的元素等式给出
$$
IJ=A^3.
$$
Lean 中这一转化写为：

```lean
have hmul_ideal :
    Ideal.span ({(⟨y, 1⟩ : ℤ√d)} : Set (ℤ√d)) *
      Ideal.span ({(⟨y, -1⟩ : ℤ√d)} : Set (ℤ√d)) =
        (Ideal.span ({(x : ℤ√d)} : Set (ℤ√d))) ^ 3 := by
  rw [Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_pow,
      hmul_elem]
```

接下来需要借助两个条件推出 $I=\langle y+\sqrt d\rangle$ 本身是某个理想的三次方。

第一，环 $\mathbb Z[\sqrt d]$ 是 Dedekind 整环中。

第二，两个共轭因子对应的主理想互素：
$$
\langle y+\sqrt d\rangle+\langle y-\sqrt d\rangle=\langle 1\rangle.
$$
在这两个条件下，利用 Dedekind 整环中的一般理想论结论：如果两个互素理想的乘积是一个三次幂，那么每个因子本身也是理想的三次幂。因此由 $IJ=A^3$ 可以推出存在理想 $K$，使得
$$
\langle y+\sqrt d\rangle=K^3.
$$
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

## Dedekind 条件与互素性

上一节中的理想分解定理需要 $\mathbb Z[\sqrt d]$ 是整环和 Dedekind 整环。Mathlib4 已经有 Dedekind 整环、整闭性、Noetherian 性、维数不超过一以及类群等抽象定义和定理，但并不会自动证明每一个具体二次整数环都满足这些条件。本文因此补充证明了在 Mordell 基本结论所需假设下，$\mathbb Z[\sqrt d]$ 具有相应的 Dedekind 结构。

主要结论为：

```lean
theorem zsqrtd_isDedekindDomain_of_squarefree_mod
    (d : ℤ) (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d) :
    IsDedekindDomain (ℤ√d)
```

它依赖几个中间步骤：首先，由 d 无平方因子且 d≡2,3(mod4) 可知 d 不是平方数，因此 Z[
d
	​

] 无零因子。其次，Z[
d
	​

] 作为 Z-模由 1 与 
d
	​

 有限生成，因此具有 Noetherian 性。再次，作为 Z 的有限整扩张，其 Krull 维数至多为 1。最后，平方自由性与模 4 条件保证 Z[
d
	​

] 正是对应二次域的整数环，从而在其分式域中整闭。由这些性质可得 Z[
d
	​

] 是 Dedekind 整环。


另一个条件是两个主理想的互素性。数学上，需要证明
$$
\langle y+\sqrt d\rangle
\quad\text{与}\quad
\langle y-\sqrt d\rangle
$$
互素。由于在 Lean 里面直接处理二次整数环里的理想互素证明会十分麻烦，本文将这一命题转化为整数互素。

考虑理想 $I+J$。由于
$$
y+\sqrt d\in I\subseteq I+J,\qquad
y-\sqrt d\in J\subseteq I+J,
$$
所以
$$
(y+\sqrt d)-(y-\sqrt d)=2\sqrt d\in I+J,
\qquad
(2\sqrt d)^2=4d\in I+J.
$$
另一方面，
$$
(y+\sqrt d)(y-\sqrt d)=y^2-d\in I+J.
$$
因此 $4d$ 与 $y^2-d$ 都属于 $I+J$。又易得 $\gcd(4d,y^2-d)=1$，由 Bezout 等式
$$
a(4d)+b(y^2-d)=1
$$
可得 $1\in I+J$。因此 $I+J=D$，即 $\langle y+\sqrt d\rangle$ 与 $\langle y-\sqrt d\rangle$ 互素。

最终得到定理：

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

## 类群下降

当已经知道
$$
\langle y+\sqrt d\rangle=I^3
$$
后，还需要利用类数条件把理想三次方下降为元素三次方。数学上，若类群阶数与 $3$ 互素，则由 $[I]^3=1$ 可推出 $[I]=1$，即 $I$ 是主理想。

```lean
theorem ideal_isPrincipal_of_cube_isPrincipal
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {I : Ideal R} (hI0 : I ∈ (Ideal R)⁰)
    (hcl : Nat.gcd 3 (Nat.card (ClassGroup R)) = 1)
    (hI3 : (I ^ 3).IsPrincipal) :
    I.IsPrincipal
```

在理想成为主理想后，由两个主理想相等可以得到生成元相差一个单位。因此存在单位 $u\in D^\times$，满足
$$
    y+\sqrt d=u\alpha^3.
$$
对于 $d\le -1$，可以证明 $\mathbb Z[\sqrt d]$ 中三次幂映射
$$
    D^\times\longrightarrow D^\times,
    \qquad
    v\longmapsto v^3
$$
是双射。故存在单位 $v\in D^\times$，使得
$$
    u=v^3.
$$
```lean
theorem zsqrtd_units_cubes {d : ℤ} (hd : d ≤ -1) (u : (ℤ√d)ˣ) :
    ∃ v : (ℤ√d)ˣ, u = v ^ 3
```

于是可以把单位吸收到三次方中：
$$
    y+\sqrt d=u\alpha^3 = v^3\alpha^3 =(a+b\sqrt d)^3,
    \qquad a,b\in\mathbb Z.
$$

```lean
theorem exists_cube_root_y_add_sqrtd
    (d : ℤ) (hd : d ≤ -1)
    (h_mod : d % 4 = 2 ∨ d % 4 = 3)
    (h_sqf : Squarefree d)
    (hcl : Nat.gcd (quadClassNumber d) 3 = 1)
    (x y : ℤ) (h_eqn : y ^ 2 = x ^ 3 + d) :
    ∃ z : ℤ√d, z ^ 3 = (⟨y, 1⟩ : ℤ√d)
```

最后一步通过展开等式并比较系数
$$
y+\sqrt d=(a+b\sqrt d)^3
$$
得到本章开头给出的主定理 `mordell_d`。

```lean
theorem mordell_arithmetic_of_cube {d y : ℤ} {z : ℤ√d}
    (hz : z ^ 3 = (⟨y, 1⟩ : ℤ√d)) :
    ∃ m : ℤ, (d = 1 - 3 * m ^ 2 ∨ d = -1 - 3 * m ^ 2) ∧
      y = m * (3 * d + m ^ 2)
```

## 类群计算

前面的 `mordell_d` 定理仍然依赖一个类数条件：
$$
3\nmid h(\mathbb Z[\sqrt d]).
$$

```lean
hcl : Nat.gcd (quadClassNumber d) 3 = 1
```

这里 `quadClassNumber d` 表示二次整数环 $\mathbb Z[\sqrt d]$ 的类数。因此，若要把抽象的 Mordell 下降定理应用到具体参数 $d$，还必须证明相应类数不被 $3$ 整除。

### $d=-1$ 与 $d=-2$ 的情形

对于 $d=-1$ 和 $d=-2$，类群计算相对直接。基本思路是：如果 $\mathbb Z[\sqrt d]$ 是欧几里得整环，则它是主理想整环，因而每个非零理想都是主理想。于是理想类群平凡，类数等于 $1$。

在 $d=-1$ 的情形下，$\mathbb Z[\sqrt{-1}]$ 即高斯整数环，Mathlib4 已经包含高斯整数的相关结构。对于 $d=-2$，本文构造了 $\mathbb Z[\sqrt{-2}]$ 的欧几里得整环实例。由此得到：
$$
\gcd(h(\mathbb Z[\sqrt{-1}]),3)=1,
\qquad
\gcd(h(\mathbb Z[\sqrt{-2}]),3)=1.
$$
### $d=-5,-6,-13$ 的有限理想类代表

对于 $d=-5,-6,-13$，本文通过把每个理想类的代表限制到有限个候选理想来确定类数的上界。

其核心思想是：先证明任意理想类都可以选择一个满足额外整除条件的整理想代表，再对这些有限可能的代表进行分类。

更具体地说，对于 Dedekind 整环
$$
D=\mathbb Z[\sqrt d],
$$
若每个理想类都存在一个代表 $J$，并且 $J$ 包含某个固定的小整数 $n$，例如 $2$ 或 $12$，那么
$$
(n)\subseteq J\subseteq D.
$$
因此，可选代表理想被限制在一个有限范围内。随后只需要对这些有限候选代表进行判别，即可得到类群的大小上界。

在 Lean 中，这一步由引理 `exists_mk0_eq_mk0_of_approx` 承担。

```lean
theorem exists_mk0_eq_mk0_of_approx
    {R S : Type*} [EuclideanDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [IsDedekindDomain S]
    (abv : AbsoluteValue R ℤ) (I : (Ideal S)⁰)
    (M : Finset R) (prodM : R)
    (hprodM : ∀ m ∈ M, m ∣ prodM)
    (hprodMnz : algebraMap R S prodM ≠ 0)
    (hex : ∀ (a : S) {b : S}, b ≠ 0 →
      ∃ (q : S) (r : R), r ∈ M ∧
        abv (Algebra.norm R (r • a - q * b)) < abv (Algebra.norm R b)) :
    ∃ J : (Ideal S)⁰,
      ClassGroup.mk0 I = ClassGroup.mk0 J ∧ algebraMap R S prodM ∈ (J : Ideal S)
```

这一引理的基础来自 Baanen 等人对 Dedekind 整环和类群的形式化工作[@Baanen2021DedekindClassGroups]。该结果在本文中可概括为如下形式。

**定理 2.2（类群代表元约化）**

令 $I$ 为 $\mathcal O_K$ 的一个非零理想，令 $M$ 为一个由非零整数组成的有限集合。假设对任意 $a,b\in\mathcal O_K$ 且 $b\ne0$，存在 $q\in\mathcal O_K$ 和 $r\in M$，使得
$$
\left|N_{\mathcal O_K/\mathbb Z}(ra-qb)\right|
<
\left|N_{\mathcal O_K/\mathbb Z}(b)\right|.
$$
则存在 $\mathcal O_K$ 的一个理想 $J$，使得
$$
I\sim J
\qquad\text{且}\qquad
J\mid\left\langle \prod_{m\in M}m\right\rangle .
$$
这里 $I\sim J$ 表示 $I$ 与 $J$ 在理想类群中属于同一类，$\left\langle \prod_{m\in M}m\right\rangle$ 表示由整数 $\prod_{m\in M}m$ 在 $\mathcal O_K$ 中生成的主理想。

在形式化时，本文没有把该定理只写成数域整数环上的专用命题，而是把底环推广为带绝对值的欧几里得整环 $R$，把 $\mathcal O_K$ 推广为 Dedekind 整环 $S$，并把“$J$ 整除由 $M$ 中元素乘积生成的理想”改写为“某个公共倍数 `prodM` 的像属于 $J$”。这是因为后续有限分类实际只需要
$$
(n)\subseteq J
$$
这一包含关系；在理想的整除顺序下，它正是 $J\mid(n)$ 的可用形式。

值得一提的是，Mathlib4 中虽然已有较一般的近似结果，但其形式更适合通用理论；而本文需要的是针对具体 $d$ 的更小候选范围。对于 $d=-5,-6$，理想类代表可以限制到与集合 $\{1,2\}$ 相关的情形；对于 $d=-13$，则需要处理与集合 $\{1,2,3,4\}$ 相关的情形。

在此基础上，对于 $d<0$ 且 $-6\le d$ 的情形，本文证明了如下结论：

```lean
theorem classGroup_exists_mk0_mem_two_of_neg_six_le
    (d : ℤ) (hd_neg : d < 0) (hd_ge : -6 ≤ d)
    [IsDomain (ℤ√d)] [IsDedekindDomain (ℤ√d)] (C : ClassGroup (ℤ√d)) :
    ∃ J : (Ideal (ℤ√d))⁰,
      C = ClassGroup.mk0 J ∧ (2 : ℤ√d) ∈ (J : Ideal (ℤ√d))
```

该定理说明：当 $d=-5$ 或 $d=-6$ 时，任意理想类 $C$ 都可以选取一个非零整理想 $J$ 作为代表，并且该代表包含元素 $2$。也就是说，
$$
(2)\subseteq J.
$$
因此，这些理想代表只可能出现在 $(2)$ 的有限分解结构中。

对于 $d=-13$，本文证明了类似的结论：

```lean
theorem classGroup_exists_mk0_mem_twelve_neg_thirteen
    [IsDomain (ℤ√(-13 : ℤ))] [IsDedekindDomain (ℤ√(-13 : ℤ))]
    (C : ClassGroup (ℤ√(-13 : ℤ))) :
    ∃ J : (Ideal (ℤ√(-13 : ℤ)))⁰,
      C = ClassGroup.mk0 J ∧ (12 : ℤ√(-13 : ℤ)) ∈ (J : Ideal (ℤ√(-13 : ℤ)))
```

这样，类群计算同样被化约为有限多个理想代表的判别问题。

### 有限代表的分类

确定有限候选代表之后，接下来需要对可能出现的理想类进行分类。本文分别在 $d=-5,-6,-13$ 的情形下构造了一个与素数 $2$ 相关的候选理想类，并证明对于
$$
R_5=\mathbb Z[\sqrt{-5}],\qquad
R_6=\mathbb Z[\sqrt{-6}],\qquad
R_{13}=\mathbb Z[\sqrt{-13}].
$$
类群中的每一个元素都属于一个二元素集合：
$$
\operatorname{Cl}(R)\subseteq\{1,A\},
$$
其中 $1$ 是平凡理想类，$A$ 是由 $2$ 上方理想构造出的候选理想类。这一有限分类的证明见附录 E。

在 Lean 中，对应的三个分类结论为：

```lean
lemma classGroup_negFive_eq_one_or_sqrtTwo
    [IsDomain R5] [IsDedekindDomain R5] (C : ClassGroup R5) :
    C = 1 ∨ C = sqrtTwoClassNegFive

lemma classGroup_negSix_eq_one_or_sqrtTwo
    [IsDomain R6] [IsDedekindDomain R6] (C : ClassGroup R6) :
    C = 1 ∨ C = sqrtTwoClassNegSix

lemma classGroup_negThirteen_eq_one_or_sqrtTwo
    [IsDomain R13] [IsDedekindDomain R13] (C : ClassGroup R13) :
    C = 1 ∨ C = sqrtTwoClassNegThirteen
```

需要注意的是，这里并不需要证明 $A\ne1$。换言之，本文不需要完整证明这些类群恰好是二阶群。对于 Mordell 下降定理而言，只需要知道类数不被 $3$ 整除。因此，只要证明类群至多有两个元素，就已经足够。

由上述分类结论可知：
$$
|\operatorname{Cl}(R_5)|\le2,\qquad
|\operatorname{Cl}(R_6)|\le2,\qquad
|\operatorname{Cl}(R_{13})|\le2.
$$
另一方面，类群至少含有单位元，因此其基数为正数。于是这些类群的阶数只能为 $1$ 或 $2$。因此必然有：
$$
\gcd(|\operatorname{Cl}(R)|,3)=1.
$$
这正是 Mordell 下降中所需的类数条件。

## 具体整数解的求解

有了 `mordell_d` 以后，具体 Mordell 方程的求解就转化为有限的整数计算。对于给定负整数 $d$，定理给出必要条件：
$$
d=1-3m^2
\quad\text{或}\quad
d=-1-3m^2,
$$
并且
$$
y=m(3d+m^2).
$$
因此，求解流程分为三步：第一步代入具体的 $d$，求出可能的整数 $m$；第二步由公式计算对应的 $y$；第三步把 $y$ 代回原方程，求出 $x$。在 Lean 中，前两步主要由 `omega`、`nlinarith` 和模运算排除不可能的平方值；最后一步利用整数三次函数的单射性，从 $x^3=n^3$ 推出 $x=n$。

本文在 `Solutions.lean` 中给出了五个具体参数的求解结果。对应的最终解集如下：

| 参数 $d$ | 类数 $h(\mathbb Z[\sqrt d])$ | 整数解 $(x,y)$ |
| --- | ---: | --- |
| $-1$ | $1$ | $(1,0)$ |
| $-2$ | $1$ | $(3,5),(3,-5)$ |
| $-5$ | $2$ | 无整数解 |
| $-6$ | $2$ | 无整数解 |
| $-13$ | $2$ | $(17,70),(17,-70)$ |

Lean 中的最终定理如下：

```lean
theorem mordell_minus1_solution_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 1 ↔ x = 1 ∧ y = 0

theorem mordell_minus2_solutions_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 2 ↔
      (x = 3 ∧ y = 5) ∨ (x = 3 ∧ y = -5)

theorem mordell_minus5 (x y : ℤ) :
    ¬ (y ^ 2 = x ^ 3 - 5)

theorem mordell_minus6 (x y : ℤ) :
    ¬ (y ^ 2 = x ^ 3 - 6)

theorem mordell_minus13_solutions_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 - 13 ↔ (x = 17 ∧ y = 70) ∨ (x = 17 ∧ y = -70)
```

## 本章小结

本章介绍了 Mordell 方程的研究背景、本文使用的主要结论、二次整数环中的分解方法、理想分解、类群下降法、类群计算以及具体整数解的求解。上述数学结构构成本文 Lean 4 形式化实践的主要对象。
