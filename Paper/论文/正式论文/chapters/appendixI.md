# 附录I：主要证明定理与 Lean 形式化对应关系

本附录汇总全文主要证明环节以及 Mordell Lean 4 项目中主要定理声明之间的对应关系。表中列出的声明是证明主线、有限类群计算和最终结果验证中反复使用的代表性入口；完整辅助引理和依赖关系以项目中的 Lean 源文件及附录 G 的完整蓝图为准。

| 证明或项目环节 | 数学内容 | Lean 文件 | 主要声明 |
|---|---|---|---|
| 项目入口 | 公开导入完整 Mordell 形式化项目，作为 Comparator 和外部引用的统一入口。 | `Mordell.lean` | 导入 `Mordell.ZomegaBasic` 与 `Mordell.Solutions` |
| 基础二次整数环接口 | 建立 `ℤ[√d]` 到二次有理代数的嵌入、迹、范数、有限生成与基表示唯一性，对应附录 A 中的 T9、T12、T13。 | `ZsqrtdBasic.lean` | `zsqrtdToQuadRat_injective`；`quadRat_norm`；`zsqrtd_algebra_norm`；`Module.Free`；`Module.Finite` |
| `d≡1 (mod 4)` 的二次整数模型 | 形式化 `ℤ[ω]` 型二次整数环、范数乘法性及其与 `ℤ[√d]` 的接口，是项目基础结构的一部分。 | `ZomegaBasic.lean` | `omega_sq`；`norm_mul`；`norm_pow`；`toQuadRat_injective`；`toQuadRat_fromZsqrtd` |
| Dedekind 条件（第 3 章、附录 A T3） | 证明满足平方自由与模 `4` 条件时，`ℤ[√d]` 是整环、整闭包并满足 Dedekind 整环条件。 | `Dedekind.lean` | `zsqrtd_isDomain_of_mod_four_eq_two_or_three`；`zsqrtd_isIntegrallyClosed_of_squarefree_mod`；`zsqrtd_isIntegralClosure_of_squarefree_mod`；`zsqrtd_isDedekindDomain_of_squarefree_mod` |
| 初等算术与互素输入（附录 A A.2--A.3） | 从整数解推出 `x>0`、`x` 为奇数、相关整数互素性，并把这些事实转化为共轭主理想互素。 | `Descent.lean` | `x_odd_two_three`；`int_isCoprime_four_mul_d_y_sq_sub_d`；`span_y_add_sqrtd_coprime` |
| 元素分解到理想分解（附录 A A.3） | 在 `ℤ[√d]` 中分解 `y²-d=x³`，并推出 `⟨y+√d⟩` 是某个理想的三次方。 | `Descent.lean` | `factor_y_sq_sub_d`；`span_y_add_sqrtd_eq_ideal_cube_of_coprime` |
| 类群下降（附录 A A.4、T4--T8） | 由理想三次方和类数与 `3` 互素，推出相关理想为主理想，并得到元素三次方表示。 | `Descent.lean` | `ideal_isPrincipal_of_cube_isPrincipal`；`cube_root_of_principal_cube_span`；`exists_cube_root_y_add_sqrtd_of_ideal_coprime`；`exists_cube_root_y_add_sqrtd_of_dedekind`；`exists_cube_root_y_add_sqrtd` |
| 单位处理（附录 A A.5、T10--T11） | 分类 `d≤-1` 情形下的单位，并证明单位因子可以吸收到三次方中。 | `Descent.lean` | `zsqrtd_units_eq_one_or_neg_one`；`zsqrtd_units_neg_one_cases`；`zsqrtd_units_cubes` |
| Mordell 主下降定理（第 3 章、附录 A A.6--A.7） | 展开 `y+√d=(a+b√d)³`，比较系数，得到 `d=-3m²±1` 与 `y=m(3d+m²)`，并给出反向构造和无解判别接口。 | `Descent.lean` | `mordell_arithmetic_of_cube`；`mordell_d`；`mordell_param_solution`；`mordell_d_solution_iff`；`mordell_d_no_solution_of_no_param`；`mordell_d_no_solution_of_three_dvd` |
| 近似引理与有限代表入口（第 3 章） | 用范数估计把每个理想类的代表限制到有限候选集合。 | `Approximation.lean` | `exists_int_two_mul_sub_sq_le_one_nine`；`exists_int_mul_sub_sq_le_one_twentyfive`；`approx_norm_expr_lt`；`approx_norm_expr_lt_neg_thirteen`；`exists_q_r_of_neg_six_le`；`exists_q_r_of_neg_thirteen` |
| 类群代表约化（第 3 章） | 将抽象类群元素替换为含有小整数 `2` 或 `12` 的整理想代表。 | `ClassGroupApprox.lean` | `exists_mk0_eq_mk0_of_approx`；`classGroup_exists_mk0_mem_two_of_neg_six_le`；`classGroup_exists_mk0_mem_twelve_neg_thirteen` |
| `d=-2` 的欧几里得结构 | 构造 `ℤ[√-2]` 的除法算法和欧几里得整环实例，用于类数为 `1` 的证明。 | `EuclideanNegTwo.lean` | `norm_mod_lt`；`natAbs_norm_mod_lt`；`instNontrivial`；`EuclideanDomain` 实例 |
| `d=-1,-2` 的类数输入 | 证明 `ℤ[i]` 和 `ℤ[√-2]` 的类数条件，并提供这两个参数下的三次根入口。 | `ClassNumber/Common.lean` | `quadClassNumber_neg_one`；`quadClassNumber_neg_two`；`classNumber_gcd_three_neg_one`；`classNumber_gcd_three_neg_two`；`exists_cube_root_y_add_sqrtd_neg_one`；`exists_cube_root_y_add_sqrtd_neg_two` |
| `d=-5` 的有限类群分类（附录 E） | 构造 `2` 上方候选理想类，并证明每个类群元素属于平凡类或该候选类，从而类数不被 `3` 整除。 | `ClassNumber/NegFive.lean` | `sqrtTwoIdealNegFive`；`class_mk0_eq_one_or_sqrtTwo_negFive`；`classGroup_negFive_eq_one_or_sqrtTwo`；`classNumber_gcd_three_neg_five` |
| `d=-6` 的有限类群分类（附录 E） | 对 `ℤ[√-6]` 进行同样的二元素候选分类，得到 Mordell 下降所需的类数条件。 | `ClassNumber/NegSix.lean` | `sqrtTwoIdealNegSix`；`class_mk0_eq_one_or_sqrtTwo_negSix`；`classGroup_negSix_eq_one_or_sqrtTwo`；`classNumber_gcd_three_neg_six` |
| `d=-13` 的有限类群分类（附录 E） | 处理 `12∈J` 的有限代表分类，并将所有候选压缩到两个理想类。 | `ClassNumber/NegThirteen.lean` | `sqrtTwoIdealNegThirteen`；`class_mk0_eq_one_or_sqrtTwo_negThirteen`；`class_mk0_eq_one_or_sqrtTwo_negThirteen_of_mem_four`；`class_mk0_eq_one_or_sqrtTwo_negThirteen_of_mem_twelve`；`classGroup_negThirteen_eq_one_or_sqrtTwo`；`classNumber_gcd_three_neg_thirteen` |
| 最终整数解定理（第 3 章、附录 F） | 将下降定理与具体类数输入结合，得到 `d=-1,-2,-5,-6,-13` 的最终整数解或无解结论；附录 F 的 Comparator 检查也以这些声明为规范目标。 | `Solutions.lean` | `mordell_minus1_solution_iff`；`mordell_minus2_solutions_iff`；`mordell_minus5`；`mordell_minus6`；`mordell_minus13_solutions_iff` |
