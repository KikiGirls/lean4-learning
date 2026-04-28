# Summary of changes for run 0792928f-34de-422e-95a9-1e7cc5f40e86
## 形式化描述：对称群中哪个阶的元素最多

### 问题
设 $f_k(n)$ 为 $S_n$（$n$ 元对称群）中阶为 $k$ 的元素个数。问：对于哪些 $k$，$f_k(n)$ 取到最大值？

### 答案
对于 $n \geq 3$，$k = 2$ 时 $f_k(n)$ 取最大值。即**对合**（involutions，即由不相交对换之积构成的置换）在所有固定阶的置换中数量最多。

直观原因：阶为 2 的置换恰好是所有圈长为 1 或 2 的置换（且至少有一个 2-圈）。对合数 $a(n)$ 满足递推 $a(n) = a(n-1) + (n-1) \cdot a(n-2)$，其渐近增长量级远超其他任何固定阶的置换计数。

### 形式化代码

文件 `RequestProject/PermutationOrder.lean` 包含：

1. **核心定义** `permCountOfOrder n k`：$S_n$ 中阶恰好为 $k$ 的置换个数，定义为
   $$|\{\sigma \in S_n \mid \text{ord}(\sigma) = k\}|$$

2. **主定理**（陈述）`involutions_maximize_permCountOfOrder`：
   对 $n \geq 3$，任意 $k$ 均有 $f_k(n) \leq f_2(n)$。
   （此定理留有 `sorry`，因为完整证明需要大量关于圈结构的组合计数基础设施，目前 Mathlib 中尚未提供。）

3. **边界情况**（已完整证明）：
   - `permCountOfOrder_one_one`：$f_1(1) = 1$
   - `permCountOfOrder_two_cases`：$f_1(2) = 1$ 且 $f_2(2) = 1$

整个文件可通过 `lake build` 编译（主定理标记为 `sorry`）。