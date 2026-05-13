# 附录E：有限代表的分类证明

## E.1 目标与候选理想类

本附录补充正文中“有限代表的分类”步骤。正文已经由代表元约化得到：在 $d=-5,-6$ 时，每个理想类都有一个非零整理想代表 $J$，满足 $2\in J$；在 $d=-13$ 时，每个理想类都有一个非零整理想代表 $J$，满足 $12\in J$。本附录说明如何从这些包含关系推出：任意理想类只能是平凡类或一个与素数 $2$ 相关的候选类。

记
$$
R_5=\mathbb Z[\sqrt{-5}],\qquad
R_6=\mathbb Z[\sqrt{-6}],\qquad
R_{13}=\mathbb Z[\sqrt{-13}].
$$
三个候选理想分别为
$$
P_5=\langle 1+\sqrt{-5},2\rangle,\quad
P_6=\langle \sqrt{-6},2\rangle,\quad
P_{13}=\langle 1+\sqrt{-13},2\rangle.
$$
令 $A_d=[P_d]$ 表示其在对应类群中的理想类。需要证明：
$$
\operatorname{Cl}(R_5)=\{1,A_5\},\qquad
\operatorname{Cl}(R_6)=\{1,A_6\},\qquad
\operatorname{Cl}(R_{13})=\{1,A_{13}\},
$$
这里的等号表示每个类群元素都落在右侧二元素集合中，并不要求 $A_d\ne1$。

## E.2 包含 $2$ 的理想代表：$d=-5$ 与 $d=-13$

先处理 $R_5$；$R_{13}$ 在包含 $2$ 的情形下完全相同。设 $I\subset R_5$ 是非零理想，且 $2\in I$。写任意元素为 $z=a+b\sqrt{-5}$。候选理想 $P_5$ 有同余刻画：
$$
z\in P_5\Longleftrightarrow a-b\equiv0\pmod2.
$$
若存在 $z\in I$ 使 $a-b$ 为奇数，则 $N(z)=a^2+5b^2$ 为奇数。又 $z\bar z=N(z)\in I$，且 $2\in I$。由 Bezout 恒等式得 $1\in I$，所以 $I=R_5$，类为平凡类。

若所有 $z\in I$ 都满足 $a-b$ 为偶数，且 $1+\sqrt{-5}\in I$，则 $P_5\subseteq I$，同时由同余刻画 $I\subseteq P_5$，故 $I=P_5$，类为 $A_5$。

若所有 $z\in I$ 都满足 $a-b$ 为偶数，但 $1+\sqrt{-5}\notin I$，则每个 $z=a+b\sqrt{-5}\in I$ 的 $b$ 必为偶数；否则可由 $z$、$2$ 与 $2(1+\sqrt{-5})$ 的整数线性组合得到 $1+\sqrt{-5}\in I$，矛盾。因此 $a,b$ 均为偶数，$I\subseteq(2)$。又 $2\in I$，故 $I=(2)$，类为平凡类。

所以在 $R_5$ 中，任意满足 $2\in I$ 的非零理想 $I$ 都满足
$$
[I]=1\quad\text{或}\quad [I]=A_5.
$$
同样论证适用于 $R_{13}$ 中满足 $2\in I$ 的非零理想，范数换成 $N(a+b\sqrt{-13})=a^2+13b^2$，候选理想换成 $P_{13}$。因此若 $I\subset R_{13}$ 且 $2\in I$，则
$$
[I]=1\quad\text{或}\quad [I]=A_{13}.
$$

## E.3 包含 $2$ 的理想代表：$d=-6$

对 $R_6=\mathbb Z[\sqrt{-6}]$，候选理想为
$$
P_6=\langle \sqrt{-6},2\rangle.
$$
写 $z=a+b\sqrt{-6}$。此时有同余刻画：
$$
z\in P_6\Longleftrightarrow a\equiv0\pmod2.
$$

设 $I\subset R_6$ 为非零理想且 $2\in I$。若存在 $z=a+b\sqrt{-6}\in I$ 使 $a$ 为奇数，则 $N(z)=a^2+6b^2$ 为奇数。由 $N(z)\in I$、$2\in I$ 和 Bezout 恒等式可得 $1\in I$，故 $I=R_6$，类为平凡类。

若所有 $z\in I$ 都有 $a$ 为偶数，并且 $\sqrt{-6}\in I$，则 $I=P_6$，类为 $A_6$。

若所有 $z\in I$ 都有 $a$ 为偶数，但 $\sqrt{-6}\notin I$，则每个 $z=a+b\sqrt{-6}\in I$ 的 $b$ 必为偶数；否则可由 $z$、$2$ 与 $2\sqrt{-6}$ 的整数线性组合得到 $\sqrt{-6}\in I$，矛盾。因此 $I=(2)$，类为平凡类。

所以在 $R_6$ 中，任意满足 $2\in I$ 的非零理想 $I$ 都满足
$$
[I]=1\quad\text{或}\quad [I]=A_6.
$$

## E.4 $d=-13$ 中从包含 $12$ 到有限分类

对 $d=-13$，代表元约化得到的是 $12\in I$。若 $I\subseteq(3)$，定义商理想
$$
K=(I:3)=\{z\in R_{13}\mid 3z\in I\}.
$$
则 $4\in K$，且 $(3)K=I$。由于 $(3)$ 是主理想，$I$ 与 $K$ 在类群中代表同一理想类。

若 $I\not\subseteq(3)$，则取 $z=a+b\sqrt{-13}\in I$ 且 $z\notin(3)$。模 $3$ 下
$$
N(z)=a^2+13b^2\equiv a^2+b^2\pmod3,
$$
而在 $\mathbb Z/3\mathbb Z$ 中，$a^2+b^2\equiv0$ 只能推出 $a\equiv b\equiv0$。所以 $3\nmid N(z)$。由 $N(z)\in I$、$12\in I$ 和 Bezout 恒等式可得 $4\in I$。因此总能归结到满足 $4\in I$ 的情形。

若 $4\in I$ 且 $2\in I$，则已由 E.2 得到 $[I]=1$ 或 $[I]=A_{13}$。若 $4\in I$ 且 $2\notin I$，先证明所有 $z=a+b\sqrt{-13}\in I$ 都满足 $a-b$ 为偶数；否则 $N(z)$ 为奇数，与 $4$ 互素，Bezout 组合会推出 $1\in I$，进而 $2\in I$，矛盾。

再证明 \(I\subseteq(2)\)。若某个 $z=a+b\sqrt{-13}\in I$ 的 $a$ 为奇数，则由 $a-b$ 为偶数可知 $b$ 也为奇数。利用 $z\in I$ 与 $4\in I$，可以通过乘以 $\sqrt{-13}$、取负和减去 $4$ 的倍数得到 $1+\sqrt{-13}\in I$。于是 $14=N(1+\sqrt{-13})\in I$，而 $4\in I$，所以 $2=14-3\cdot4\in I$，矛盾。因此每个 $z\in I$ 的实部和虚部都为偶数，故 $I\subseteq(2)$。

定义
$$
K=(I:2)=\{z\in R_{13}\mid 2z\in I\}.
$$
由 $4\in I$ 得 $2\in K$，且 $(2)K=I$。因为 $(2)$ 是主理想，$I$ 和 $K$ 在类群中代表同一类。由 E.2 的“包含 $2$”分类可知 $[I]=1$ 或 $[I]=A_{13}$。

结合代表元约化结论，每个 \(R_{13}\) 的理想类都有满足 \(12\in I\) 的代表，所以任意类群元素 \(C\in\operatorname{Cl}(R_{13})\) 都满足
$$
C=1\quad\text{或}\quad C=A_{13}.
$$

## E.5 对类数条件的影响

综上，本文形式化得到三个分类结论：
$$
\forall C\in\operatorname{Cl}(R_5),\quad C=1\ \text{或}\ C=A_5,
$$
$$
\forall C\in\operatorname{Cl}(R_6),\quad C=1\ \text{或}\ C=A_6,
$$
$$
\forall C\in\operatorname{Cl}(R_{13}),\quad C=1\ \text{或}\ C=A_{13}.
$$
因此三个类群的基数都不超过 $2$。由于类群至少包含单位元，类数只能是 $1$ 或 $2$，从而必有
$$
\gcd(h(R_5),3)=\gcd(h(R_6),3)=\gcd(h(R_{13}),3)=1.
$$
这正是 Mordell 下降定理在 $d=-5,-6,-13$ 三个具体参数中所需的类数输入。
