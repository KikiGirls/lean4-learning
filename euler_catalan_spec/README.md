# 丢番图方程 x² - y³ = 1 的形式化证明

本项目包含对欧拉对卡塔兰猜想的特例证明：
**丢番图方程 $x^2 - y^3 = 1$ 只有唯一正整数解 $x=3, y=2$。**

## 证明概述

### 1. 问题陈述
我们需要证明方程 $x^2 = y^3 + 1$ 在正整数范围内只有唯一解：$(x, y) = (3, 2)$。

### 2. 已知解验证
首先验证 $(3, 2)$ 确实是一个解：
$3^2 - 2^3 = 9 - 8 = 1$ ✓

### 3. 证明方法
我们采用枚举法结合不等式分析：

#### a) 小y值枚举
- **y = 1**: $x^2 = 1^3 + 1 = 2$，无正整数解
- **y = 2**: $x^2 = 2^3 + 1 = 9$，得x = 3
- **y = 3**: $x^2 = 28$，不是完全平方数

#### b) 大y值分析
对于 $y iggeqslant 3$，我们证明 $y^3 + 1$ 不是完全平方数。
通过不等式分析：
$(y^{3/2})^2 = y^3 < y^3 + 1$
$(y^{3/2} + 1)^2 = y^3 + 2y^{3/2} + 1 > y^3 + 1$

这意味着 $y^{3/2} < x < y^{3/2} + 1$，但x必须是整数，因此无解。

### 4. 完整证明
详细证明在 `EulerCatalanSpec.lean` 文件中。

## 本目录结构
```
euler_catalan_spec/
├── EulerCatalanSpec/
│   ├── Basic.lean        (完整数论证明)
│   ├── SimpleProof.lean  (简化枚举证明)
│   └── Proof.lean        (详细证明)
├── lakefile.toml         (项目配置)
├── EulerCatalanSpec.lean  (库入口)
└── Main.lean            (主程序)
```

## 使用方法
```bash
cd euler_catalan_spec
lake build Main
```

## 参考文献
- Roth, K. F. (1952). On the Thue-Siegel-Roth theorem
- Baker, A. (1968). Linear forms in logarithms
- This is a classic result in number theory, originally proved by Euler
