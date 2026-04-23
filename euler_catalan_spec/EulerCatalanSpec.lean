-- 证明丢番图方程 x² - y³ = 1 只有唯一正整数解 x=3, y=2
-- 使用完整的数论方法

import EulerCatalanSpec.CompleteProof

-- 主定理
#check complete_proof
#check solution_exists_unique

-- 证明简介
-- 这个证明使用了经典的数论方法：
-- 1. 因式分解 x² = y³ + 1 = (y + 1)(y² - y + 1)
-- 2. 证明两个因子互质
-- 3. 推导出这两个因子都是完全平方数
-- 4. 通过不等式分析证明唯一解