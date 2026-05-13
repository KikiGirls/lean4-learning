# 论文数学推导与证明思路笔记

论文：**Formalized Class Group Computations and Integral Points on Mordell Elliptic Curves**  
主题：在 Lean 3 中形式化若干 Mordell 方程

$$
y^2=x^3+d,\qquad x,y\in \mathbb Z,
$$

的求解过程。论文的数学核心不是提出新的数论定理，而是把“二次数域 + 理想类群 + 理想下降法”这套非初等方法形式化，并用它求出若干具体方程的整数解。

---

## 1. 总体证明框架

论文解决 Mordell 方程的主线如下：

```text
Mordell 方程 y^2 = x^3 + d
        ↓ 在二次数环 Z[√d] 中分解
(y+√d)(y-√d)=x^3
        ↓ 转为理想等式
<y+√d><y-√d>=<x>^3
        ↓ 证明两个理想互素
        ↓ Dedekind 环中的理想唯一分解 / 理想下降
<y+√d>=A^3
        ↓ 类群中 3 与类数互素 ⇒ A 主理想
<y+√d>=<α^3>
        ↓ 单位都是三次方 ⇒ y+√d=α^3
        ↓ 展开 α=a+b√d 并比较 √d 系数
b(3a^2+b^2d)=1
        ↓ b=±1
        ↓ d=-3a^2±1,  y=a(3d+a^2)
```

这就是论文 Theorem `Mordell_basic` 的核心数学推导。

---

## 2. 基础对象与公式

### 2.1 Mordell 方程

论文研究的是

$$
y^2=x^3+d,\qquad d\in\mathbb Z\setminus\{0\}.
$$

其中重点形式化了若干 $d<0$ 的情形。

---

### 2.2 二次环 `quad_ring`

论文为了在 Lean 中高效计算，引入了一个专门的二次环结构。给定交换环 $R$ 与 $a,b\in R$，定义一个符号 $\alpha$ 满足

$$
\alpha^2=a\alpha+b.
$$

环中元素写成

$$
z=z_1+z_2\alpha,\qquad z_1,z_2\in R.
$$

若

$$
z=z_1+z_2\alpha,\qquad w=w_1+w_2\alpha,
$$

则乘法公式为

$$
zw=(z_1w_1+z_2w_2b)+(z_2w_1+z_1w_2+z_2w_2a)\alpha.
$$

在最常用的平方根情形 $\alpha=\sqrt d$ 中，$a=0,b=d$，所以

$$
(z_1+z_2\sqrt d)(w_1+w_2\sqrt d)
=(z_1w_1+dz_2w_2)+(z_2w_1+z_1w_2)\sqrt d.
$$

---

### 2.3 二次数域与整数环

设

$$
K=\mathbb Q(\sqrt d),
$$

其中 $d$ 是平方自由整数。整数环为

$$
\mathcal O_K=\{x\in K: x\text{ 是 }\mathbb Z\text{ 上的整元素}\}.
$$

经典结论：

$$
\mathcal O_K=
\begin{cases}
\mathbb Z[\sqrt d], & d\equiv 2,3\pmod 4,\\[4pt]
\mathbb Z\left[\dfrac{1+\sqrt d}{2}\right], & d\equiv 1\pmod 4.
\end{cases}
$$

论文形式化了这两个模型，并由此得到这些环是 Dedekind domain。

---

### 2.4 最小多项式推导

对

$$
\beta=a+b\sqrt d\in \mathbb Q(\sqrt d),
$$

其共轭为

$$
\overline\beta=a-b\sqrt d.
$$

因此

$$
(X-\beta)(X-\overline\beta)
=X^2-(\beta+\overline\beta)X+\beta\overline\beta.
$$

又因为

$$
\beta+\overline\beta=2a,
$$

$$
\beta\overline\beta=a^2-db^2,
$$

所以若 $b\neq 0$，$a+b\sqrt d$ 的最小多项式是

$$
X^2-2aX+(a^2-db^2).
$$

如果 $a+b\sqrt d$ 是整元素，则其迹和范数满足整数性条件：

$$
2a\in\mathbb Z,
\qquad
 a^2-db^2\in\mathbb Z.
$$

结合 $d\pmod 4$ 的分类，可以推出上面的整数环公式。

---

## 3. 范数公式

### 3.1 元素范数

在 $\mathbb Z[\sqrt d]$ 中，元素

$$
\alpha=a+b\sqrt d
$$

的范数为

$$
N(\alpha)=\alpha\overline\alpha=a^2-db^2.
$$

当 $d<0$ 时，

$$
N(a+b\sqrt d)=a^2+|d|b^2\ge 0.
$$

这个公式在三个地方反复使用：

1. 判断单位；
2. 判断理想是否主理想；
3. 从 $y+\sqrt d=\alpha^3$ 推出 $x=m^2-d$。

---

### 3.2 理想范数

对 Dedekind domain $R$ 的非零理想 $I$，论文形式化了绝对理想范数

$$
N(I)=|R/I|,
$$

若商环有限；否则定义为 $0$。

关键性质：

$$
N(IJ)=N(I)N(J).
$$

证明思路：

1. 先证明 $I,J$ 互素时的乘法性；
2. 再证明素理想幂的范数公式

   $$
   N(P^n)=N(P)^n;
   $$

3. 用 Dedekind domain 中理想唯一分解把结论推广到任意非零理想。

一个重要推论：如果

$$
N(P)=p
$$

是普通整数中的素数，则 $P$ 是素理想。因为若

$$
P=IJ,
$$

则

$$
p=N(P)=N(I)N(J),
$$

所以 $N(I)=1$ 或 $N(J)=1$，从而其中一个理想是整个环。

---

## 4. 下降法与类群

### 4.1 整数中的下降法

经典下降法中常用的事实是：若

$$
\gcd(a,b)=1,
\qquad
ab=c^n,
$$

则存在整数 $c_1,c_2$ 使得

$$
a=\pm c_1^n,
\qquad
b=\pm c_2^n.
$$

这个结论依赖 $\mathbb Z$ 的唯一分解性。

---

### 4.2 Dedekind domain 中的理想下降

在一般数环中，元素唯一分解可能失败，但 Dedekind domain 中非零理想唯一分解成立。因此可以把下降法改写成理想版本。

若 $D$ 是 Dedekind domain，$I,J,L$ 是非零理想，且

$$
\gcd(I,J)=1,
\qquad
IJ=L^n,
$$

则存在理想 $L_1,L_2$，使得

$$
I=L_1^n,
\qquad
J=L_2^n.
$$

这是论文中应用到 Mordell 方程的核心定理之一。

---

### 4.3 类群与主理想判定

类群定义为非零分式理想模掉主分式理想：

$$
\mathrm{Cl}(D)=\{\text{非零分式理想}\}/\{\text{主分式理想}\}.
$$

类数为

$$
h(D)=|\mathrm{Cl}(D)|.
$$

理想 $I$ 在类群中为单位元，当且仅当 $I$ 是主理想。

论文用到的关键结论是：若

$$
\gcd(n,h(D))=1
$$

且

$$
I^n\text{ 是主理想},
$$

则

$$
I\text{ 是主理想}.
$$

原因：在有限群 $\mathrm{Cl}(D)$ 中，若 $[I]^n=1$，且 $n$ 与群阶互素，则 $[I]=1$。这直接来自 Lagrange 定理或有限群中幂映射 $g\mapsto g^n$ 的自同构性。

---

## 5. 类群计算的核心方法

论文计算了若干虚二次数域的类数。使用的方法不是 Minkowski bound，而是一个更直接的“广义带余除法”判据。

---

### 5.1 广义带余除法定理

设 $I$ 是 $\mathcal O_K$ 的非零理想，$M$ 是一个有限整数集合。若对任意

$$
a,b\in\mathcal O_K,\qquad b\neq 0,
$$

存在

$$
q\in\mathcal O_K,
\qquad
r\in M,
$$

使得

$$
\left|N_{\mathcal O_K/\mathbb Z}(ra-qb)\right|
<
\left|N_{\mathcal O_K/\mathbb Z}(b)\right|,
$$

则每个理想类都有一个代表 $J$，满足

$$
I\sim J,
\qquad
J\mid \left\langle\prod_{m\in M}m\right\rangle.
$$

直观解释：这个不等式给出了类似 Euclidean division 的“下降步骤”。如果理想代表不够小，就可以用这个除法步骤构造出同一理想类中范数更小的代表。不断下降后，剩下的代表必须整除由 $M$ 中元素生成的主理想。

---

### 5.2 转化为数域中的范数估计

论文还把上面的条件改写为域中的形式。把 $\gamma=a/b$ 看成 $K$ 中元素，则上面的条件等价于：

对任意

$$
\gamma\in K,
$$

存在

$$
q\in\mathcal O_K,
\qquad
r\in M,
$$

使得

$$
|N_{K/\mathbb Q}(r\gamma-q)|<1.
$$

证明本质上是把

$$
ra-qb=b(r\gamma-q)
$$

代入范数，并利用范数乘法性：

$$
N(ra-qb)=N(b)N(r\gamma-q).
$$

---

### 5.3 $d\in\{-1,-2,-5,-6\}$ 的上界

对

$$
K=\mathbb Q(\sqrt d),
\qquad
D=\mathbb Z[\sqrt d],
$$

其中

$$
d\in\{-1,-2,-5,-6\},
$$

论文用

$$
M=\{1,2\}
$$

完成范数估计。因此每个理想类都有代表整除

$$
\langle 1\cdot 2\rangle=\langle 2\rangle.
$$

接下来只需要分解 $\langle 2\rangle$。

---

### 5.4 素理想 $P_2$ 的定义与性质

论文定义了 $2$ 上方的一个理想 $P_2$。记作 `sqrt_2 d`。

若

$$
d\equiv 2\pmod 4,
$$

则

$$
P_2=\langle \sqrt d,2\rangle.
$$

若

$$
d\equiv 3\pmod 4,
$$

则

$$
P_2=\langle 1+\sqrt d,2\rangle.
$$

论文证明：

$$
P_2^2=\langle 2\rangle,
$$

并且

$$
N(P_2)=2.
$$

因为 $2$ 是素数，所以

$$
P_2\text{ 是素理想}.
$$

又由于

$$
[P_2]^2=[\langle 2\rangle]=1
$$

在类群中成立，所以 $[P_2]$ 的阶只能是 $1$ 或 $2$。

于是对这些 $d$，类群至多由两个元素组成：

$$
\mathrm{Cl}(\mathbb Q(\sqrt d))\subseteq \{1,[P_2]\}.
$$

严格地说，是每个类都等于 $1$ 或 $[P_2]$。

---

### 5.5 下界：证明 $P_2$ 非主理想

为了说明类数确实为 $2$，需要证明 $P_2$ 不是主理想。

假设 $P_2$ 是主理想：

$$
P_2=\langle a+b\sqrt d\rangle.
$$

由于

$$
N(P_2)=2,
$$

主理想范数给出

$$
|N(a+b\sqrt d)|=2.
$$

当 $d<0$ 时，

$$
N(a+b\sqrt d)=a^2-db^2=a^2+|d|b^2.
$$

所以需要整数解

$$
a^2-db^2=2.
$$

如果

$$
d<-2,
$$

则：

- 若 $b=0$，则 $a^2=2$，不可能；
- 若 $|b|\ge 1$，则

  $$
  a^2+|d|b^2\ge |d|>2,
  $$

  也不可能。

因此 $P_2$ 非主理想，$[P_2]$ 的阶为 $2$，从而

$$
2\mid h(\mathbb Q(\sqrt d)).
$$

---

### 5.6 明确类数结果

论文最终形式化了：

$$
h(\mathbb Q(\sqrt{-1}))=1,
$$

$$
h(\mathbb Q(\sqrt{-2}))=1,
$$

$$
h(\mathbb Q(\sqrt{-5}))=2,
$$

$$
h(\mathbb Q(\sqrt{-6}))=2,
$$

$$
h(\mathbb Q(\sqrt{-13}))=2.
$$

其中 $d=-13$ 的情形更复杂：论文使用

$$
M=\{1,2,3,4\}
$$

做范数估计，并用 Kummer-Dedekind 定理处理 $\langle 3\rangle$ 的素理想分解。结论仍然是类群由 $[P_2]$ 控制，并且 $P_2$ 非主理想，所以类数为 $2$。

---

## 6. Mordell 方程主定理

### 6.1 主定理

设 $d<0$ 是平方自由整数，且

$$
d\equiv 2\text{ 或 }3\pmod 4.
$$

因此

$$
\mathcal O_{\mathbb Q(\sqrt d)}=\mathbb Z[\sqrt d].
$$

再假设

$$
3\nmid h(\mathbb Z[\sqrt d]).
$$

则 Mordell 方程

$$
y^2=x^3+d
$$

有整数解，当且仅当存在 $m$ 使得

$$
d=-3m^2+1
\qquad\text{或}\qquad
 d=-3m^2-1.
$$

此时

$$
y=\pm m(3d+m^2),
$$

并且完整的 $x$ 坐标为

$$
x=m^2-d.
$$

论文的 Lean 版本把必要性写成存在整数 $m$：

$$
y=m(3d+m^2),
$$

且

$$
d=1-3m^2
\qquad\text{或}\qquad
 d=-1-3m^2.
$$

改变 $m$ 的符号就得到 $y$ 的正负两个值。

---

## 7. Mordell 主定理的详细推导

### 7.1 在 $\mathbb Z[\sqrt d]$ 中分解

由

$$
y^2=x^3+d
$$

得到

$$
y^2-d=x^3.
$$

在

$$
D=\mathbb Z[\sqrt d]
$$

中，左边分解为

$$
(y+\sqrt d)(y-\sqrt d)=x^3.
$$

转为主理想：

$$
\langle y+\sqrt d\rangle\langle y-\sqrt d\rangle
=\langle x\rangle^3.
$$

记

$$
I=\langle y+\sqrt d\rangle,
\qquad
J=\langle y-\sqrt d\rangle,
\qquad
L=\langle x\rangle.
$$

则

$$
IJ=L^3.
$$

---

### 7.2 证明 $I,J$ 互素

需要证明

$$
\gcd(I,J)=1.
$$

手算证明思路如下：若某个素理想同时整除 $I$ 和 $J$，则它同时整除

$$
(y+\sqrt d)+(y-\sqrt d)=2y
$$

和

$$
(y+\sqrt d)-(y-\sqrt d)=2\sqrt d.
$$

因此公共因子只能来自 $2$、$y$、$d$ 的公共约束。

论文中用到两个辅助事实：

1. $y$ 与 $d$ 互素；
2. 在定理假设下，任何解都满足 $x$ 为奇数。

$x$ 为奇数可用模 $8$ 检查：若 $x$ 偶，则

$$
x^3\equiv 0\pmod 8.
$$

而平方模 $8$ 只可能是

$$
0,1,4.
$$

对 $d\equiv 2,3\pmod 4$ 的相关剩余类，

$$
y^2-d\equiv x^3\pmod 8
$$

会矛盾。因此 $x$ 必为奇数。

Lean 形式化中没有采用完全相同的纸笔证明，而是直接通过范数限制计算两个理想的 gcd。

---

### 7.3 理想下降

已经有

$$
IJ=L^3,
\qquad
\gcd(I,J)=1.
$$

由 Dedekind domain 中的理想下降定理，存在理想 $A,B$ 使得

$$
I=A^3,
\qquad
J=B^3.
$$

特别地，

$$
\langle y+\sqrt d\rangle=A^3.
$$

因为左边是主理想，所以 $A^3$ 是主理想。

---

### 7.4 类数条件推出 $A$ 主理想

在类群中，

$$
[A]^3=1.
$$

假设

$$
3\nmid h(D),
$$

即

$$
\gcd(3,h(D))=1.
$$

由有限群理论可得

$$
[A]=1.
$$

所以 $A$ 是主理想：

$$
A=\langle \alpha\rangle
$$

对某个

$$
\alpha\in D.
$$

于是

$$
\langle y+\sqrt d\rangle=\langle \alpha^3\rangle.
$$

两个主理想相等意味着生成元相差一个单位：

$$
y+\sqrt d=u\alpha^3,
\qquad
u\in D^\times.
$$

---

### 7.5 单位都是三次方

对

$$
D=\mathbb Z[\sqrt d],
\qquad d<0,
$$

单位可以通过范数方程刻画：

$$
N(a+b\sqrt d)=a^2-db^2=1.
$$

当 $d<-1$ 时，单位只有

$$
\pm 1.
$$

当 $d=-1$ 时，单位为

$$
\{\pm1,\pm i\}.
$$

这两个单位群的阶都是 $2$ 的幂，因此三次幂映射

$$
u\mapsto u^3
$$

是单位群的双射。换句话说，每个单位都是三次方。

所以可以把 $u$ 吸收到 $\alpha$ 中，不妨设

$$
y+\sqrt d=\alpha^3.
$$

---

### 7.6 展开 $\alpha^3$

写

$$
\alpha=a+b\sqrt d,
\qquad a,b\in\mathbb Z.
$$

先平方：

$$
(a+b\sqrt d)^2=a^2+2ab\sqrt d+b^2d.
$$

再乘一次：

$$
(a+b\sqrt d)^3
=(a^3+3ab^2d)+(3a^2b+b^3d)\sqrt d.
$$

也可写成

$$
(a+b\sqrt d)^3
=a(a^2+3b^2d)+b(3a^2+b^2d)\sqrt d.
$$

由于

$$
y+\sqrt d=(a+b\sqrt d)^3,
$$

比较 $\sqrt d$ 的系数，得到

$$
1=b(3a^2+b^2d).
$$

这是整数中的分解，所以

$$
b=\pm1.
$$

又因为 $b^2=1$，上式给出

$$
3a^2+d=b.
$$

因此

$$
d=b-3a^2.
$$

即

$$
d=1-3a^2
\qquad\text{或}\qquad
 d=-1-3a^2.
$$

令

$$
m=a,
$$

得到

$$
d=-3m^2\pm 1.
$$

再比较有理部分，得到

$$
y=a(a^2+3b^2d).
$$

由于 $b^2=1$，所以

$$
y=a(a^2+3d)=m(m^2+3d)=m(3d+m^2).
$$

这就是主定理中的 $y$ 公式。

---

### 7.7 推出 $x$ 公式

对

$$
y+\sqrt d=(a+b\sqrt d)^3
$$

取范数：

$$
N(y+\sqrt d)=N(a+b\sqrt d)^3.
$$

左边是

$$
N(y+\sqrt d)=y^2-d.
$$

由 Mordell 方程，

$$
y^2-d=x^3.
$$

右边是

$$
N(a+b\sqrt d)^3=(a^2-db^2)^3.
$$

因为 $b^2=1$，所以

$$
x^3=(a^2-d)^3.
$$

整数中立方映射单射，因此

$$
x=a^2-d=m^2-d.
$$

---

### 7.8 反方向验证

反方向更简单。若

$$
d=1-3m^2
\qquad\text{或}\qquad
 d=-1-3m^2,
$$

令

$$
x=m^2-d,
\qquad
 y=m(3d+m^2),
$$

则直接代入可证

$$
y^2=x^3+d.
$$

统一地，令

$$
s\in\{1,-1\},
\qquad
 d=s-3m^2.
$$

设

$$
t=m^2.
$$

则

$$
3d+m^2=3s-8t,
$$

$$
m^2-d=4t-s.
$$

于是

$$
y^2=m^2(3d+m^2)^2=t(3s-8t)^2.
$$

展开：

$$
t(3s-8t)^2
=t(9s^2-48st+64t^2).
$$

因为 $s^2=1$，所以

$$
y^2=9t-48st^2+64t^3.
$$

另一方面，

$$
x^3+d=(4t-s)^3+s-3t.
$$

展开：

$$
(4t-s)^3+s-3t
=64t^3-48st^2+12s^2t-s^3+s-3t.
$$

由于 $s^2=1$ 且 $s^3=s$，得到

$$
x^3+d=64t^3-48st^2+12t-s+s-3t.
$$

即

$$
x^3+d=64t^3-48st^2+9t.
$$

这与 $y^2$ 相同，因此

$$
y^2=x^3+d.
$$

Lean 中这个验证由 `ring` tactic 直接完成。

---

## 8. 论文最终形式化的 Mordell 方程结果

利用前面的类数计算：

$$
h(\mathbb Q(\sqrt{-1}))=1,
$$

$$
h(\mathbb Q(\sqrt{-2}))=1,
$$

$$
h(\mathbb Q(\sqrt{-5}))=2,
$$

$$
h(\mathbb Q(\sqrt{-6}))=2,
$$

$$
h(\mathbb Q(\sqrt{-13}))=2,
$$

这些类数都与 $3$ 互素，因此主定理可应用。

---

### 8.1 $d=-1$

方程：

$$
y^2=x^3-1.
$$

条件

$$
d=-3m^2\pm1
$$

给出

$$
-1=-1-3m^2
\quad\Rightarrow\quad
m=0.
$$

于是

$$
y=0,
\qquad
x=m^2-d=1.
$$

解为

$$
(x,y)=(1,0).
$$

论文 Lean theorem 写成：若 $y^2=x^3-1$，则

$$
y=0.
$$

---

### 8.2 $d=-2$

方程：

$$
y^2=x^3-2.
$$

有

$$
-2=1-3m^2
\quad\Rightarrow\quad
m^2=1.
$$

取 $m=1$：

$$
x=m^2-d=1-(-2)=3,
$$

$$
y=m(3d+m^2)=1(-6+1)=-5.
$$

取 $m=-1$ 得

$$
y=5.
$$

所以整数解为

$$
(x,y)=(3,5),(3,-5).
$$

论文 Lean theorem 写成：若 $y^2=x^3-2$，则

$$
y=5\quad\text{或}\quad y=-5.
$$

---

### 8.3 $d=-13$

方程：

$$
y^2=x^3-13.
$$

有

$$
-13=-1-3m^2
\quad\Rightarrow\quad
m^2=4.
$$

取 $m=2$：

$$
x=m^2-d=4-(-13)=17,
$$

$$
y=m(3d+m^2)=2(-39+4)=-70.
$$

取 $m=-2$ 得

$$
y=70.
$$

所以整数解为

$$
(x,y)=(17,70),(17,-70).
$$

论文 Lean theorem 写成：若 $y^2=x^3-13$，则

$$
y=70\quad\text{或}\quad y=-70.
$$

---

### 8.4 $d=-5$

方程：

$$
y^2=x^3-5.
$$

若有解，则必须满足

$$
-5=1-3m^2
\quad\text{或}\quad
-5=-1-3m^2.
$$

第一种给出

$$
3m^2=6,
\qquad
m^2=2,
$$

无整数解。

第二种给出

$$
3m^2=4,
\qquad
m^2=\frac43,
$$

无整数解。

因此无整数解。

论文 Lean theorem：

$$
y^2\neq x^3-5.
$$

---

### 8.5 $d=-6$

方程：

$$
y^2=x^3-6.
$$

若有解，则必须满足

$$
-6=1-3m^2
\quad\text{或}\quad
-6=-1-3m^2.
$$

第一种给出

$$
3m^2=7,
\qquad
m^2=\frac73,
$$

无整数解。

第二种给出

$$
3m^2=5,
\qquad
m^2=\frac53,
$$

无整数解。

因此无整数解。

论文 Lean theorem：

$$
y^2\neq x^3-6.
$$

---

## 9. 用到的主要定理与工具清单

| 定理 / 工具 | 在论文中的作用 |
|---|---|
| Dedekind domain 中理想唯一分解 | 把元素下降法替换为理想下降法 |
| 整数环是 Dedekind domain | 保证 $\mathbb Z[\sqrt d]$ 可用理想唯一分解，前提是它确实是 $\mathcal O_K$ |
| 二次数域整数环分类 | 证明当 $d\equiv2,3\pmod4$ 时 $\mathcal O_K=\mathbb Z[\sqrt d]$ |
| 理想下降定理 | 由 $IJ=L^3$ 且 $(I,J)=1$ 推出 $I=A^3$ |
| 类群有限性 | 类数 $h(D)$ 有意义，并可用有限群论 |
| Lagrange 定理 / 有限群幂映射 | 若 $\gcd(3,h(D))=1$ 且 $A^3$ 主理想，则 $A$ 主理想 |
| 主理想相等的单位差异 | $\langle u\rangle=\langle v\rangle$ 推出 $u=\epsilon v$，其中 $\epsilon$ 是单位 |
| 单位范数判定 | 用 $N(a+b\sqrt d)=a^2-db^2$ 计算单位群 |
| 元素范数乘法性 | 推导 $x=m^2-d$，也用于类群计算 |
| 理想范数乘法性 | 证明 $P_2$ 是素理想，以及计算类群上界/下界 |
| 广义带余除法判据 | 给出类群有限生成代表，从而限制类群大小 |
| Kummer-Dedekind 定理 | 在 $d=-13$ 情形中处理 $\langle3\rangle$ 的素理想分解 |
| 模 $8$ 平方剩余检查 | 证明 Mordell 解中 $x$ 必为奇数 |
| 模 $n$ 无解检查 | 对具体二次方程排除整数解，例如 $d=-5,-6$ |
| Lean `ring` tactic | 自动完成多项式恒等式验证 |
| Lean `linarith` tactic | 自动处理线性不等式估计 |
| Lean `dec_trivial` | 穷举有限环如 $\mathbb Z/n\mathbb Z$ 中的情况 |

---

## 10. 论文中讨论但不是主路线的方法

### 10.1 Minkowski bound

经典方法：数域 $K$ 的类群由范数满足

$$
N(P)\le
\sqrt{|\Delta_K|}
\left(\frac{4}{\pi}\right)^{r_2}
\frac{n!}{n^n}
$$

的素理想类生成。

其中：

- $n=[K:\mathbb Q]$；
- $r_2$ 是复嵌入共轭对数；
- $\Delta_K$ 是判别式。

对二次数域 $K=\mathbb Q(\sqrt d)$，$d$ 平方自由：

$$
\Delta_K=
\begin{cases}
 d, & d\equiv1\pmod4,\\
 4d, & d\equiv2,3\pmod4.
\end{cases}
$$

论文没有把这个作为主计算路线，而是采用了广义带余除法方法。

---

### 10.2 解析类数公式

对虚二次数域，解析类数公式给出有限和表达式：

$$
h(K)=\frac{w}{2\Delta_K}
\sum_{a=1}^{|\Delta_K|-1}
\left(\frac{\Delta_K}{a}\right)a,
$$

其中：

- $w$ 是单位群大小；
- $\left(\frac{\Delta_K}{a}\right)$ 是 Jacobi 符号。

论文认为这条路线需要形式化较多解析数论背景，因此没有采用。

---

### 10.3 椭圆曲线方法

方程

$$
y^2=x^3+d
$$

定义一条 Mordell 椭圆曲线。用椭圆曲线理论也可以求整数点，但这需要 Mordell-Weil 群、秩、扭点等更重的理论。论文选择类群下降法，是为了在 Lean 中推进代数数论式的 Diophantine 方程形式化。

---

## 11. 最核心的一页版总结

论文数学核心可以压缩为：

1. 在 $D=\mathbb Z[\sqrt d]$ 中分解

   $$
   y^2-d=(y+\sqrt d)(y-\sqrt d)=x^3.
   $$

2. 转为理想等式

   $$
   \langle y+\sqrt d\rangle\langle y-\sqrt d\rangle
   =\langle x\rangle^3.
   $$

3. 证明两个理想互素，于是 Dedekind 理想下降给出

   $$
   \langle y+\sqrt d\rangle=A^3.
   $$

4. 类数条件 $3\nmid h(D)$ 推出 $A$ 主理想。

5. 单位都是三次方，于是

   $$
   y+\sqrt d=(a+b\sqrt d)^3.
   $$

6. 展开并比较 $\sqrt d$ 系数：

   $$
   1=b(3a^2+b^2d).
   $$

7. 所以 $b=\pm1$，进而

   $$
   d=-3a^2\pm1.
   $$

8. 比较常数项：

   $$
   y=a(3d+a^2).
   $$

9. 取范数：

   $$
   x=a^2-d.
   $$

所以所有解都来自

$$
d=-3m^2\pm1,
\qquad
x=m^2-d,
\qquad
 y=\pm m(3d+m^2).
$$

对论文形式化的例子：

| $d$ | 类数 | 结论 |
|---:|---:|---|
| $-1$ | $1$ | 唯一解 $(x,y)=(1,0)$ |
| $-2$ | $1$ | 解 $(x,y)=(3,\pm5)$ |
| $-5$ | $2$ | 无整数解 |
| $-6$ | $2$ | 无整数解 |
| $-13$ | $2$ | 解 $(x,y)=(17,\pm70)$ |
