**Mordell Lean 4 项目模块结构与统计数据**

| **文件** | **目的** | **LOC** | **声明** |
| --- | --- | --- | --- |
| `ZsqrtdBasic.lean` | 二次整数环 $\mathbb Z[\sqrt d]$ 与有理二次代数的基础接口；整理范数、迹、基和有限模结构。 | 177 | 17 |
| `Approximation.lean` | 有理数取整逼近和范数估计；为 $d=-5,-6,-13$ 的类群代表约化提供计算引理。 | 327 | 11 |
| `Dedekind.lean` | 证明 $\mathbb Z[\sqrt d]$ 在相应同余与无平方因子条件下具有整环和 Dedekind 整环结构。 | 306 | 14 |
| `ClassGroupApprox.lean` | 形式化类群代表元约化准则，将逼近结果转化为关于理想类代表的有限性控制。 | 139 | 8 |
| `Descent.lean` | 形式化 Mordell 下降法主线：因式分解、理想互素、类群下降、单位处理和参数化结论。 | 549 | 26 |
| `EuclideanNegTwo.lean` | 构造 $\mathbb Z[\sqrt{-2}]$ 的显式除法算法，并给出 Euclidean domain 实例。 | 176 | 18 |
| `ClassNumberSmall.lean` | 验证 $d=-1,-2,-5,-6,-13$ 所需的小类数条件，并给出若干具体 cube-root 输入。 | 868 | 44 |
| `Extensions.lean` | 将下降法结论包装为更易复用的解集等价命题和无解判别准则。 | 104 | 6 |
| `Solutions.lean` | 给出具体 Mordell 方程的最终结论：$d=-1,-2,-13$ 的整数解以及 $d=-5,-6$ 的无解性。 | 188 | 12 |
| `Basic.lean` | 聚合导入基础证明模块，作为项目内部的统一入口。 | 5 | 0 |
| `Mordell.lean` | 导出项目主要模块，作为 Lake 默认目标。 | 5 | 0 |
| **合计** | **11 个 Lean 文件** | **2844** | **156** |
