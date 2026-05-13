# 摘  要

形式化数学通过交互式定理证明器把数学命题和证明转化为可由计算机检查的严格表达，是提高复杂证明可靠性的重要方法。随着大语言模型和证明智能体的发展，人工智能开始参与数学证明生成、Lean 代码补全、定理检索和错误修复等环节。本文围绕人工智能辅助 Lean 4 形式化证明展开研究，并以 Mordell 方程整数解问题作为具体案例，考察传统数论证明在 Lean 4 与 Mathlib4 环境中的形式化过程。

本文首先梳理 AI 数学推理和形式化证明系统的发展现状，然后围绕 Mordell 方程
$$
y^2=x^3+d
$$
建立 Lean 4 形式化项目。证明主线从二次整数环 $\mathbb{Z}[\sqrt d]$ 中的元素分解出发，将方程转化为主理想分解，再利用 Dedekind 整环结构、共轭主理想互素性、类群下降和有限类群计算，得到 Mordell 基本结论，并将其应用于 $d=-1,-2,-5,-6,-13$ 等具体参数。最终项目包含 12 个 Lean 源文件，约 2800 行代码，完成了基础二次整数环接口、Dedekind 条件、类群代表元约化、若干小类数条件以及最终整数解定理的形式化；项目通过 `lake build` 验证，未使用 `sorry`、`admit` 或 `axiom` 占位。

在此基础上，本文进一步比较了不同人工智能模型在自然语言证明生成、Lean 证明代码生成和仓库级智能体实验中的表现。实验表明，当前 AI 能够有效提供证明路线、局部引理、代码草稿和编译错误修复建议，但在复杂代数数论形式化任务中仍难以脱离人类设计的证明结构和 Lean 编译反馈独立完成完整证明。本文的实践说明，人类给出数学路线、AI 辅助证明工程、Lean 负责最终核验的协作模式，已经能够支持具有一定复杂度的形式化数学项目。

{\heiti 关键词}：人工智能；Lean 4；形式化证明；Mordell 方程；

# ABSTRACT

Formal mathematics translates mathematical statements and proofs into rigorous expressions that can be checked by interactive theorem provers, providing an important way to improve the reliability of complex proofs. With the development of large language models and proof agents, artificial intelligence has begun to assist in proof generation, Lean code completion, theorem search, and error repair. This thesis studies AI-assisted formalization in Lean 4 through a case study on integral points of Mordell equations.

After reviewing recent progress in AI mathematical reasoning and formal proof systems, this thesis constructs a Lean 4 formalization project for the Mordell equation
$$
y^2=x^3+d.
$$
The formal proof starts from a factorization in the quadratic integer ring $\mathbb{Z}[\sqrt d]$, turns the equation into a statement about principal ideals, and then uses Dedekind domain structures, coprimality of conjugate ideals, class group descent, and finite class group computations. These ingredients yield the basic Mordell theorem and its applications to the parameters $d=-1,-2,-5,-6,-13$. The final project consists of 12 Lean source files and about 2800 lines of code, covering the basic interface of quadratic integer rings, Dedekind conditions, class group representative reduction, small class number conditions, and final theorems for integral solutions. The project passes `lake build` without using `sorry`, `admit`, or `axiom`.

The thesis also compares several types of AI assistance in natural-language proof generation, Lean proof generation, and repository-level agent experiments. The experiments show that current AI systems can provide useful proof outlines, local lemmas, code drafts, and suggestions for fixing compiler errors, but they still have difficulty completing complex algebraic number theory formalizations without human-designed proof structures and Lean feedback. This case study suggests that a workflow combining human mathematical planning, AI-assisted proof engineering, and Lean kernel verification is already practical for nontrivial formal mathematics projects.

**Key words**: artificial intelligence; Lean 4; formal proof; Mordell equation;
