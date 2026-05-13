# 基于人工智能和 Lean 的形式化及其应用 ——以 Mordell 方程整数解的 Lean 4 形式化为例

## 摘要

摘要主要写四点：

1. 形式化数学和 Lean 的研究背景；
2. AI 辅助 Lean 证明开发的意义；
3. 本文以 Mordell 方程整数解问题为案例，进行 Lean 4 形式化实践；
4. 对多个 AI 模型进行对比实验，分析其在数学理解、命题建模、代码生成、报错修复和复杂证明拆解中的表现。


⸻

## Abstract

英文摘要对应中文摘要即可。

⸻
## 绪论

### 引言

随着计算机科学与数学基础研究的不断发展，形式化数学逐渐成为提高数学证明可靠性的重要方向。传统数学证明通常以自然语言书写，虽然具有较强的表达灵活性，但其中往往包含大量省略步骤、直觉判断和隐含前提。对于结构复杂、推理链较长的数学命题，仅依赖人工阅读和检查容易出现理解偏差。形式化证明则通过交互式定理证明器，将数学定义、命题和证明转化为计算机能够验证的严格逻辑表达，从而提升证明的严谨性和可检查性。

Lean 是近年来发展较快的交互式定理证明器之一。Lean 4 结合了依赖类型理论、函数式编程和自动化证明策略，并依托 Mathlib4 数学库，已经能够支持大量代数、数论、分析和拓扑等领域的数学形式化工作。然而，复杂数学命题的形式化仍然具有较高门槛，使用者不仅需要理解数学证明本身，还需要熟悉 Lean 的类型系统、库函数、证明策略和错误信息。

近年来，大语言模型在自然语言理解、代码生成和数学推理方面表现出较强能力，为辅助 Lean 形式化证明开发提供了新的可能。AI 可以帮助解释数学证明、生成 Lean 代码、拆解复杂证明目标，并根据编译错误进行修改。但是，AI 生成的证明并不一定正确，仍然需要 Lean 编译器和人工审查共同验证。因此，研究人工智能辅助 Lean 形式化证明的方法，具有较强的理论意义和实践价值。

本文以 Mordell 方程整数解问题为案例，围绕原数学证明中的关键公式、证明思路和形式化目标，研究如何借助人工智能工具在 Lean 4 中进行数学命题建模与证明开发，并通过多个 AI 模型的对比实验，分析其在 Lean 形式化任务中的能力与局限。

### 本文主要研究内容

本文主要围绕人工智能辅助 Lean 4 数学形式化展开研究，选取 Mordell 方程整数解问题作为具体案例。Mordell 方程的一般形式为：

\[
y^2 = x^3 + d
\]

其中 \(x,y,d\in \mathbb{Z}\)。该问题涉及整数方程、二次整数环、范数、理想分解和类群下降法等数学内容，具有一定复杂度，适合作为 AI 辅助形式化证明的实验对象。

本文的主要研究内容包括以下几个方面：

第一，对 Mordell 方程整数解问题的数学证明进行分析，梳理其中涉及的关键公式、定理和证明思路。重点分析方程

\[
y^2-d=x^3
\]

在二次整数环中的分解形式：

\[
(y+\sqrt d)(y-\sqrt d)=x^3
\]

以及由此引出的理想分解、类群条件和参数化解构造。

第二，将普通数学证明拆解为 Lean 4 中可表达的形式化目标。本文关注如何将数学中的定义、命题、引理和证明步骤转化为 Lean 4 中的 `def`、`theorem`、`lemma` 和 tactic 证明，并分析普通数学证明到形式化证明转化过程中的困难。

第三，完成部分 Mordell 方程相关命题的 Lean 4 形式化实现，包括 Mordell 方程的定义、参数化解的验证、代数恒等式证明、部分特例方程验证以及二次整数环相关结构的形式化探索。

第四，借助人工智能工具辅助完成 Lean 4 形式化实践。本文在命题理解、Lean 代码生成、证明补全和错误修改等环节使用不同大语言模型作为辅助工具，并记录其在具体任务中的表现。

第五，对不同 AI 模型在 Lean 4 形式化任务中的辅助效果进行比较分析。本文选取若干具有代表性的形式化任务，包括数学证明理解、Lean 命题建模、简单证明生成、报错修改和复杂证明拆解等，比较不同模型输出结果的正确性、可编译性和人工修改成本，从而总结 AI 在 Lean 证明开发中的优势与局限。


### 本文研究意义

本文研究具有一定的理论意义和实践意义。

从理论意义上看，形式化数学能够将传统数学证明转化为机器可验证的逻辑结构，从而提高证明的严谨性和可靠性。Mordell 方程整数解问题涉及代数数论中的多个重要概念，以此为案例进行 Lean 4 形式化，有助于理解复杂数学证明在证明助手中的表达方式，也为相关数学内容的进一步形式化提供参考。

从技术意义上看，Lean 4 虽然提供了强大的类型系统和 Mathlib4 数学库，但复杂数学命题的形式化仍需要大量人工工作。本文研究 AI 辅助 Lean 证明开发的方法，可以为降低形式化证明门槛、提升证明开发效率提供实践经验。特别是在命题建模、证明拆解和错误修复等环节，大语言模型能够发挥一定辅助作用。

从应用意义上看，本文通过多个 AI 模型对比实验，分析了不同模型在 Lean 4 形式化任务中的表现。这不仅有助于了解当前 AI 在形式化数学中的实际能力，也有助于明确其局限。例如，AI 在简单代数恒等式和具体数值验证中表现较好，但在涉及复杂 Mathlib API、类型类推断、理想和类群等内容时仍然存在较大困难。因此，本文的研究可以为后续 AI 辅助形式化证明工具的设计和使用提供参考。

总体而言，本文将人工智能、Lean 4 形式化证明和 Mordell 方程整数解问题结合起来，既具有数学形式化实践价值，也具有 AI 辅助证明开发的方法研究意义。

### 本章小结

本章首先介绍了形式化数学、Lean 4 和 AI 辅助证明开发的研究背景，指出传统数学证明在严谨性和可验证性方面存在一定局限，而形式化证明能够通过计算机检查提高证明可靠性。随后，本章说明了本文以 Mordell 方程整数解问题为案例，研究 AI 辅助 Lean 4 形式化证明开发的主要内容，包括数学证明分析、Lean 4 形式化实现和多模型 AI 对比实验。最后，本章从理论意义、技术意义和应用意义三个方面阐述了本文研究的价值。

正文余下部分组织如下。第 1 章回顾形式化数学、Lean 4 与 AI 辅助证明的相关基础。第 2 章介绍 Mordell 方程的数学基础与证明思路。第 3 章展示 Mordell 方程相关命题的 Lean 4 形式化实现。第 4 章给出多模型 AI 辅助 Lean 4 形式化实验与分析。最后，第 5 章总结全文并展望未来工作。



## \subsection{论文正文}

## 1.1 形式化数学概述

形式化数学是指将数学中的定义、命题、定理和证明转化为计算机能够检查的严格逻辑表达。与普通数学证明相比，形式化证明不能依赖自然语言中的直觉判断和省略推理，而是要求每一步都符合证明助手的类型系统和逻辑规则。在 Lean 中，定义通常用 `def` 表示，定理和引理用 `theorem` 或 `lemma` 表示，证明则通过 tactic 或证明项完成。形式化证明具有严谨、可验证、可复用等优点，但也存在表达繁琐、类型要求严格、证明细节无法省略等困难。为了更清楚地理解 Lean 形式化证明，下面将从形式化证明工具、Lean 4 语言环境和 Mathlib4 数学库三个方面进行说明。

### 1.1.1 Lean 形式化证明的基础环境

* **交互式定理证明器**：这是形式化证明的主要工具形态，由用户编写证明步骤，系统逐步检查逻辑正确性，Lean、Coq、Isabelle/HOL 都属于此类系统。

* **Lean 4**：Lean 4 是本文使用的形式化证明环境，既是一门函数式编程语言，也是一种交互式定理证明器，支持依赖类型、命题即类型、tactic 证明和类型类机制。([Lean Language][1])

* **Mathlib4 数学库**：Mathlib4 是 Lean 4 的社区数学库，为形式化证明提供基础支撑，涵盖代数、数论、拓扑、分析等领域，并提供大量已有定理和自动化 tactic。([Lean 4 Dev][2])

### 1.1.2 数学证明到 Lean 形式化证明的转化

将普通数学证明转化为 Lean 证明时，最大的困难在于自然语言中的省略推理必须被显式表达。例如，普通证明中一句“显然成立”，在 Lean 中可能需要多个辅助引理、类型转换和 tactic 才能完成。Lean 证明不仅要表达结论，还要明确变量类型、前提条件、使用的定理和每一步推理方式。因此，数学形式化并不是对文字证明的简单翻译，而是将数学证明重新组织为机器可验证的逻辑结构。

| 普通数学证明特点 | Lean 形式化要求 |
| -------- | ------------------- |
| 省略显然步骤 | 每一步都要证明 |
| 变量类型模糊 | 必须声明类型 |
| 默认使用定理 | 必须引用或证明 |
| 使用自然语言推理 | 必须转化为 tactic 或 term |
| 隐含条件较多 | 必须显式写成假设 |




[1]: https://lean-lang.org/theorem_proving_in_lean4/?utm_source=chatgpt.com "Theorem Proving in Lean 4"
[2]: https://lean4.dev/tactics/mathlib/intro?utm_source=chatgpt.com "Introduction to Mathlib - The Lean Math Library"

## 1.2 AI 辅助 Lean 证明开发最新现状和相关工作

自 2025 年以来，基于大语言模型的数学推理智能体已经不再局限于单轮答案生成，而是逐渐发展为“生成—验证—修正”的结构化推理流程。在奥林匹克数学问题中，Huang 等提出的模型无关验证与修正流水线具有代表性。该方法结合 Gemini 2.5 Pro、Grok-4 和 GPT-5 等模型，在 IMO 2025 六道题中解决了五道，明显超过模型直接生成答案的基线表现，说明外部验证、候选筛选与迭代修正对于提升数学推理可靠性具有重要作用[1]。与此同时，Google DeepMind 的 Gemini Deep Think 在 IMO 2025 中达到金牌水平，也表明前沿模型已经具备较强的自然语言长程推导能力[2]。

在研究级数学任务中，Aletheia 是近期较有代表性的数学研究智能体。该系统由 Gemini Deep Think 系列模型驱动，采用生成、验证与修订相结合的工作方式，能够在自然语言层面处理文献检索、证明构造和结果修正等任务。相关研究表明，Aletheia 已经参与 Erdős 问题、算术几何中的 eigenweights 计算以及若干人机协作数学发现任务[2]。在 FirstProof 挑战中，Aletheia 面对十个未公开的研究级数学问题，最终有六个问题被多数专家评估为已解决[3]。这说明 AI 数学推理的应用场景已经从竞赛题逐渐扩展到研究级问题。

除完全自动化的推理系统外，另一类值得关注的方向是人机协作式数学发现。例如，Bryan 等人的代数几何工作展示了一种“AI 处理特殊情形—人类提炼关键结构—AI 辅助推进一般证明”的协作模式。AI 并非直接替代数学家完成全部证明，而是在特殊案例计算、候选结构发现和局部证明生成中发挥辅助作用，进而帮助人类研究者形成更一般的证明思路。

截至 2026 年 5 月，Erdős Problem #1196 是 AI 参与数学发现的最值得关注案例之一。该问题属于本原集理论，要求证明当 A⊂[x,∞) 为本原整数集时，是否有

a∈A
∑
	​

aloga
1
	​

<1+o(1).

此前 Lichtman 将该问题的上界推进到约 1.399+o(1)。随后，GPT-5.4 Pro 在 Liam Price 的提示下给出了一条不同于既有人类证明路线的新思路，利用 von Mangoldt 权重建立估计，证明了

a∈A
a>x
	​

∑
	​

aloga
1
	​

≤1+O(
logx
1
	​

).

该问题现已在 Erdős Problems 网站上标记为 “PROVED (LEAN)”[5,6]。此后，Alexeev、Barreto、Li、Lichtman、Price、Shah、Tang 和 Tao 将这一思路进一步发展为 “von Mangoldt chains” 方法[5]。这一案例表明，AI 在部分前沿数学问题中已经能够提出具有研究价值的证明路线，并推动后续的人类数学研究。

### 用于形式推理的代理

在形式化证明方向，近期系统的核心变化是从“一次性生成 Lean 代码”转向“与证明助手交互的智能体流程”。AlphaProof 是这一方向的重要里程碑。该系统将 Lean 形式验证与强化学习结合，在 IMO 2024 中达到银牌水平，并在相关论文中被描述为一个通过 Lean 环境搜索形式化证明的强化学习系统[7]。随后，Aristotle 将 Lean 证明搜索、自然语言推理和专用几何求解器结合，在 IMO 2025 问题上达到金牌水平[8]。这些工作说明，形式化证明系统已经不只是验证已有证明，而是开始参与复杂数学问题的自动搜索过程。

开源和半开源系统也在 2025—2026 年快速发展。DeepSeek-Prover-V2 通过子目标分解和强化学习提升 Lean 4 证明能力[9]；Goedel-Prover-V2 引入脚手架式数据合成、Lean 编译器反馈自我修正和模型平均策略，在开源形式化证明模型中取得了较强结果[10]。Seed-Prover 1.5 进一步将工具调用和 Lean 交互纳入训练过程，并在 Putnam 2025 问题上取得突出表现[11]。Numina-Lean-Agent 则将通用代码智能体、Lean MCP 工具、定理检索和非形式推理结合起来，完成了 Putnam 2025 全部 12 道题，并展示了面向更大规模形式化项目的潜力[12]。

除了竞赛基准测试之外，部分系统已经开始面向研究级形式化和真实证明工程。Aristotle 和 AxiomProver 都已用 Lean 形式化了 Erdős 未解问题的解决方案；AxiomProver 从 Fel 猜想的自然语言表述出发，自动生成可验证的形式化证明，解决了数值半群 syzygies 相关的开放猜想[14]。
在国内，北京大学AI4Math团队的Rethlas/Archon双智能体系统自主解决了悬置12年的交换代数开放问题——安德森猜想，生成约19000行Lean 4形式化证明代码。
在更多人为参与下，Numina-Lean-Agent 与两位人类专家合作，形式化了 Brascamp-Lieb 定理 [ liu2026numina ] ；
同时Mistral AI 最新发布的 Leanstral 智能体也说明，面向真实 Lean 仓库的证明工程智能体正在成为新的发展方向[13]。


1.2.3 本章小结

总体来看，AI 辅助数学证明正在经历从“自然语言解题工具”到“形式化证明工程助手”的转变。自然语言推理代理已经能够在竞赛题和部分研究级问题中提出有效证明思路；形式化证明代理则通过 Lean 编译反馈、定理检索、子目标分解和迭代修正，使证明结果获得机器可检查的可靠性。

陶哲轩曾预测，只要使用得当，2026 年水平的人工智能，将成为数学研究以及许多其他领域中值得信赖的合著者。【25】当前的发展已经在一定程度上印证了这一判断：AI 不仅能够辅助生成证明想法，还能够参与定理检索、证明拆解、Lean 代码生成、错误修复和大规模形式化项目开发。对本文而言，这些工作说明，基于 AI 的 Lean 4 证明开发已经具备现实研究价值，也为后续开展具体命题的形式化与 AI 辅助证明实验提供了技术背景和研究依据。

[1] Huang Y, Yang L F. Winning Gold at IMO 2025 with a Model-Agnostic Verification-and-Refinement Pipeline[EB/OL]. arXiv, 2025[2026-05-04]. https://arxiv.org/abs/2507.15855
.

[2] Google DeepMind. Advanced version of Gemini with Deep Think officially achieves gold-medal standard at the International Mathematical Olympiad[EB/OL]. Google DeepMind Blog, 2025[2026-05-04]. https://deepmind.google/blog/advanced-version-of-gemini-with-deep-think-officially-achieves-gold-medal-standard-at-the-international-mathematical-olympiad/
.

[3] Feng T, Trinh T H, Bingham G, et al. Towards Autonomous Mathematics Research[EB/OL]. arXiv, 2026[2026-05-04]. https://arxiv.org/abs/2602.10177
.

[4] Feng T, Jung J, Kim S, et al. Aletheia tackles FirstProof autonomously[EB/OL]. arXiv, 2026[2026-05-04]. https://arxiv.org/abs/2602.21201
.

[5] Bryan J, Elek B, Manners F, et al. The Motivic Class of the Space of Genus 0 Maps to the Flag Variety[EB/OL]. arXiv, 2026[2026-05-04]. https://arxiv.org/abs/2601.07222
.

[6] Alexeev B, Barreto K, Li Y, et al. Primitive sets and von Mangoldt chains: Erdős Problem #1196 and beyond[EB/OL]. arXiv, 2026[2026-05-04]. https://arxiv.org/abs/2605.00301
.

[7] Bloom T F. Erdős Problem #1196[EB/OL]. Erdős Problems, 2026[2026-05-04]. https://www.erdosproblems.com/1196
.

[8] Hubert T, Mehta S, Kanigicherla K, et al. Olympiad-level formal mathematical reasoning with reinforcement learning[J/OL]. Nature, 2025[2026-05-04]. https://www.nature.com/articles/s41586-025-09833-y
.

[9] Achim T, Best A, Der K, et al. Aristotle: IMO-level Automated Theorem Proving[EB/OL]. arXiv, 2025[2026-05-04]. https://arxiv.org/abs/2510.01346
.

[10] Ren Z Z, Shao Z, Song J, et al. DeepSeek-Prover-V2: Advancing Formal Mathematical Reasoning via Reinforcement Learning for Subgoal Decomposition[EB/OL]. arXiv, 2025[2026-05-04]. https://arxiv.org/abs/2504.21801
.

[11] Lin Y, Tang S, Lyu B, et al. Goedel-Prover-V2: Scaling Formal Theorem Proving with Scaffolded Data Synthesis and Self-Correction[EB/OL]. arXiv, 2025[2026-05-04]. https://arxiv.org/abs/2508.03613
.

[12] Chen J, Chen W, Du J, et al. Seed-Prover 1.5: Mastering Undergraduate-Level Theorem Proving via Learning from Experience[EB/OL]. arXiv, 2025[2026-05-04]. https://arxiv.org/abs/2512.17260
.

[13] Liu J, Zhou Z, Zhu Z, et al. Numina-Lean-Agent: An Open and General Agentic Reasoning System for Formal Mathematics[EB/OL]. arXiv, 2026[2026-05-04]. https://arxiv.org/abs/2601.14027
.

[14] Chen E, Cummins C, GSM, et al. Fel’s Conjecture on Syzygies of Numerical Semigroups[EB/OL]. arXiv, 2026[2026-05-04]. https://arxiv.org/abs/2602.03716
.

[15] Ju H, Gao G, Jiang J, et al. Automated Conjecture Resolution with Formal Verification[EB/OL]. arXiv, 2026[2026-05-04]. https://arxiv.org/abs/2604.03789
.

[16] Mistral AI. Leanstral: Open-Source foundation for trustworthy vibe-coding[EB/OL]. Mistral AI, 2026[2026-05-04]. https://mistral.ai/news/leanstral
.

[17] Mistral AI. Leanstral[EB/OL]. Mistral Docs, 2026[2026-05-04]. https://docs.mistral.ai/models/model-cards/leanstral-26-03
.

[18] Tao T, Sothanaphan N, et al. AI contributions to Erdős problems[EB/OL]. GitHub Wiki: teorth/erdosproblems, 2026[2026-05-04]. https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems
.

[19] Bloom T F. Erdős Problem #1051[EB/OL]. Erdős Problems, 2026[2026-05-04]. https://www.erdosproblems.com/1051
.

[20] Bloom T F. Erdős Problem #741[EB/OL]. Erdős Problems, 2026[2026-05-04]. https://www.erdosproblems.com/741
.

[21] Bloom T F. Erdős Problem #38[EB/OL]. Erdős Problems, 2026[2026-05-04]. https://www.erdosproblems.com/38
.

[22] Bloom T F. Erdős Problem #694[EB/OL]. Erdős Problems, 2026[2026-05-04]. https://www.erdosproblems.com/694
.

[23] Bloom T F. Erdős Problem #1202[EB/OL]. Erdős Problems, 2026[2026-05-04]. https://www.erdosproblems.com/1202
.

[24] Tao T. Primitive sets and von Mangoldt chains: Erdős Problem #1196 and beyond[EB/OL]. What’s new, 2026[2026-05-04]. https://terrytao.wordpress.com/2026/05/03/primitive-sets-and-von-mangoldt-chains-erdos-problem-1196-and-beyond/
.



【26】Tao, T. (2023, June 16). Embracing change and resetting expectations. In AI Anthology: Reflections on AI and the future of human flourishing. Microsoft Unlocked. https://unlocked.microsoft.com/ai-anthology/terence-tao/














# 第 2 章 Mordell 方程的数学基础与证明思路

本章重点讲你那篇数学论文的内容。

⸻

## 2.1 Mordell 方程概述

在开始之前，我们先简要介绍一下 Mordell 方程本身的历史。

1657 年，Fermat 在一封信中指出，方程 𝑦2 = 𝑥3 −2 在正
整数中的唯一解是 (𝑥, 𝑦) = (3, 5)【1】。1914 年，Mordell [2]
系统研究了一般形式的方程

𝑦2 = 𝑥3 + 𝑑：（1）
其中：

x, y, d \in \mathbb{Z}

主要关注两个方面
一是使方程不
存在任何整数解的关于 𝑑 的条件；二是基于理想下降法
为某些 𝑑 寻找解的方法。这个方程很快就被称为 Mordell
方程。
在二十世纪和二十一世纪，围绕 Mordell 方程的研究不断深入，人们开发出了有效解决 Mordell方程的技术
Mordell【2】【3】【4，第26章】，Baker【5】、Stark【6】、Bennett 和 Ghadermarzi [7]等人的研究为 Mordell 方程的理论发展和具体求解提供了重要基础。

在本文后续形式化过程中， 使用了 Mordell [2, 第 8 节] 中的一个基于类群下降法得到的存在性结论来求特殊负整数参数下的整数解。例如：

d = -1, -2, -5, -6, -13

【1】Fermat, P. de. (1894). Lettre à Digby (15 Août 1657) & Lettres de défi de 1657[M]. In Tannery, P., & Henry, C. (Eds.), Oeuvres de Fermat (Vol. 2, pp. 332–346). Paris: Gauthier-Villars et fils.


[2] Louis Mordell. 1914. The Diophantine Equation 𝑦2 − 𝑘 = 𝑥3. Pro-
ceedings of the London Mathematical Society s2-13, 1 (01 1914), 60–80.
https://doi.org/10.1112/plms/s2-13.1.60


【3] Louis Mordell. 1920. A Statement by Fermat. Proceedings of the Lon-
don Mathematical Society s2-18 (1920), v–vi. https://doi.org/10.1112/
plms/s2-18.1.1-s

[4] Louis Mordell. 1969. Diophantine equations. Academic Press.

[5] Alan Baker. 1968. Contributions to the Theory of Diophantine Equa-
tions. II. the Diophantine Equation 𝑦2 = 𝑥3 +𝑘. Philosophical Transac-
tions of the Royal Society of London. Series A, Mathematical and Physi-
cal Sciences 263, 1139 (1968), 193–208. http://www.jstor.org/stable/734
29

[6] Harold Stark. 1973. Effective estimates of solutions of some Dio-
phantine equations. Acta Arithmetica 24, 3 (1973), 251–259. http:
//eudml.org/doc/205226

[7] Michael A. Bennett and Amir Ghadermarzi. 2015. Mordell’s equation:
a classical approach. LMS Journal of Computation and Mathematics
18, 1 (2015), 633–646. https://doi.org/10.1112/S1461157015000182


⸻

## 2.2 使用的主要结论

**Theorem 2.1** 令 $d < 0$ 为无平方因子的整数，满足 $d \equiv 2$ 或 $3 \pmod{4}$，且假设 $3 \nmid h(\mathbb{Z}[\sqrt{d}])$。则 Mordell 方程 (1) 有整数解当且仅当存在 $m \in \mathbb{N}$，使得 $d = -3m^2 \pm 1$；此时方程的解满足 $y = \pm m(3d + m^2)$。

简要证明见附录 A。



3.2 方程的基本变形

从：

y^2 = x^3 + d

得到：

y^2 - d = x^3

在二次扩张中分解为：

(y+\sqrt d)(y-\sqrt d)=x^3

这一分解是后续使用代数数论方法的核心入口。

⸻

3.3 二次数域与二次整数环

介绍：

K = \mathbb{Q}(\sqrt d)

以及二次整数环：

\mathcal{O}_K

在特定条件下，可以使用：

\mathbb{Z}[\sqrt d]

作为工作对象。

重点说明论文中常见条件：

d < 0
d \equiv 2 \text{ or } 3 \pmod 4

此时二次整数环形式较简单。

⸻

3.4 二次整数环中的范数

对于元素：

a + b\sqrt d

其共轭为：

a - b\sqrt d

范数为：

N(a+b\sqrt d)
=
(a+b\sqrt d)(a-b\sqrt d)
=
a^2 - db^2

这一公式在 Lean 形式化中可以转化为代数恒等式证明。

⸻

3.5 理想与理想分解

由：

(y+\sqrt d)(y-\sqrt d)=x^3

可转化为主理想乘积：

\langle y+\sqrt d\rangle
\langle y-\sqrt d\rangle
=
\langle x\rangle^3

令：

I = \langle y+\sqrt d\rangle
J = \langle y-\sqrt d\rangle

则：

IJ = \langle x\rangle^3

若能证明 I 和 J 互素，则可以利用理想分解的唯一性推出相关理想本身具有三次方结构。

⸻

3.6 类群与类数条件

介绍理想类群的作用。

若类群阶数为：

h(\mathcal{O}_K)

且满足：

3 \nmid h(\mathcal{O}_K)

那么在理想类群中可以消去三次幂相关障碍，从而推出某些理想为主理想。

这是从理想等式回到元素等式的关键。

⸻

3.7 类群下降法的证明思路

整体证明链可以写成：

Mordell 方程
    ↓
二次整数环中因式分解
    ↓
主理想乘积等式
    ↓
证明两个理想互素
    ↓
由唯一分解得到理想三次方结构
    ↓
利用类群条件推出主理想
    ↓
得到元素三次方表示
    ↓
展开比较系数
    ↓
得到整数参数条件

⸻

3.8 关键公式推导

设：

y+\sqrt d = (a+b\sqrt d)^3

展开：

(a+b\sqrt d)^3
=
a^3 + 3a^2b\sqrt d + 3ab^2d + b^3d\sqrt d

整理为：

(a+b\sqrt d)^3
=
a(a^2+3b^2d)
+
b(3a^2+b^2d)\sqrt d

比较 √d 的系数：

1 = b(3a^2+b^2d)

因此：

b = \pm 1

于是得到：

d = 1 - 3a^2

或：

d = -1 - 3a^2

令：

m = a

可得到参数形式：

d = 1 - 3m^2

或：

d = -1 - 3m^2

进一步可得到：

x = m^2 - d
y = m(3d+m^2)

并验证：

y^2 = x^3 + d

⸻

3.9 原论文中涉及的主要定理

可以列出：

1. 二次整数环结构定理；
2. 二次元素范数公式；
3. 主理想乘法性质；
4. 互素理想乘积的三次方分解性质；
5. 理想类群与类数条件；
6. 负二次整数环单位性质；
7. 代数恒等式展开；
8. 模运算与整数解限制；
9. 特例参数下的整数解分类。

⸻

3.10 面向 Lean 4 的形式化目标拆解

将数学内容拆成 Lean 任务：

数学内容	Lean 4 形式化目标	难度
Mordell 方程	定义 y ^ 2 = x ^ 3 + d	低
参数化解	证明给定参数满足方程	低
三次展开	使用 ring 证明代数恒等式	低
模运算限制	使用 ZMod、omega、norm_num	中
二次整数环	建模 a + b√d	中
范数公式	证明 N(a+b√d)=a²-db²	中
理想乘法	表示主理想乘积	高
理想互素	证明两个理想互素	高
类群下降	形式化类群条件	很高

⸻

第 4 章 AI 辅助 Lean 4 形式化方法设计

本章是方法论核心。

⸻

4.1 整体方法框架

本文采用如下流程：

数学论文内容
    ↓
数学证明结构分析
    ↓
形式化目标拆解
    ↓
Lean 4 命题建模
    ↓
AI 生成证明代码
    ↓
Lean 编译器检查
    ↓
错误反馈给 AI
    ↓
人工修正和验证
    ↓
形成最终 Lean 4 代码

⸻

4.2 形式化任务划分

将任务分为六类：

任务编号	任务类型	内容
T1	数学证明理解	解释原论文证明思路
T2	Lean 命题建模	将数学命题写成 Lean theorem
T3	简单证明生成	生成 ring、norm_num 等证明
T4	报错修复	根据 Lean 报错修改代码
T5	证明拆解	将复杂证明拆成小引理
T6	复杂结构建模	处理理想、类群、二次整数环

⸻

4.3 Lean 4 命题建模策略

介绍如何把数学命题转化为 Lean 定理。

例如数学命题：

d = 1 - 3m^2
x = m^2 - d
y = m(3d+m^2)

推出：

y^2 = x^3 + d

Lean 中可以写为：

theorem mordell_param_identity_pos
    (m d : ℤ)
    (hd : d = 1 - 3 * m ^ 2) :
    (m * (3 * d + m ^ 2)) ^ 2 =
      (m ^ 2 - d) ^ 3 + d := by
  subst d
  ring

⸻

4.4 Prompt 设计策略

可以设计几类 Prompt。

4.4.1 数学解释型 Prompt

用于让 AI 解释数学证明。

请解释下面 Mordell 方程证明的数学思路，并指出其中使用了哪些代数数论定理。

4.4.2 Lean 建模型 Prompt

用于把数学命题写成 Lean theorem。

请将下面数学命题转写为 Lean 4 theorem statement，变量类型使用整数 ℤ。

4.4.3 证明生成型 Prompt

用于生成 Lean 证明。

请为下面 Lean 4 theorem 补全证明，优先使用 Mathlib 中已有 tactic。

4.4.4 报错修复型 Prompt

用于错误修复。

下面是 Lean 4 编译错误，请根据错误信息修复代码，不要使用不存在的定理名。

4.4.5 证明拆解型 Prompt

用于复杂证明规划。

请将下面数学定理拆解为 Lean 4 中容易证明的若干辅助引理。

⸻

4.5 编译器反馈驱动的迭代修复

本文采用：

AI 输出代码
    ↓
Lean 编译
    ↓
记录错误
    ↓
反馈给 AI
    ↓
再次生成
    ↓
人工审查

每个任务最多进行若干轮，例如 3 轮。

记录内容包括：

* 第一次输出是否能编译；
* 出现了什么错误；
* AI 是否理解错误；
* 修复后是否引入新错误；
* 最终是否通过。

⸻

4.6 人工介入策略

说明 AI 不是完全自动证明工具，人工主要负责：

1. 判断数学命题是否正确；
2. 检查 AI 是否改变原命题；
3. 查证 Mathlib 定理是否真实存在；
4. 调整证明粒度；
5. 将复杂证明拆成辅助引理；
6. 最终确认 Lean 编译通过。

⸻

4.7 评价指标设计

设计多维度指标。

4.7.1 可编译性指标

指标	含义
一次通过率	首次生成代码是否可编译
多轮通过率	经报错反馈后是否可编译
最终通过率	规定轮数内是否完成
平均修复轮数	从错误到通过需要几轮

4.7.2 数学正确性指标

指标	含义
命题忠实度	是否保持原数学含义
假设完整性	是否遗漏必要条件
推理合理性	证明思路是否正确
结论一致性	是否得到原证明结论

4.7.3 Lean 专项指标

指标	含义
语法正确率	是否符合 Lean 4 语法
API 准确率	使用定理是否真实存在
tactic 合理性	tactic 是否适合目标
类型处理能力	是否正确处理 ℤ、ℕ、ZMod 等类型
证明简洁性	证明是否简洁可读

4.7.4 AI 行为指标

指标	含义
定理名幻觉率	是否编造不存在定理
报错理解能力	是否能根据错误修复
稳定性	多轮输出是否稳定
人工修改成本	需要人工修改的比例

⸻

第 5 章 Mordell 方程相关命题的 Lean 4 形式化实现

本章写你的具体实现。

⸻

5.1 项目环境

介绍：

* Lean 4 版本；
* Mathlib4 版本；
* Lake；
* VS Code；
* 操作系统；
* 使用的 AI 工具；
* 项目目录结构。

示例目录：

MordellFormalization/
├── lakefile.lean
├── lean-toolchain
├── MordellFormalization/
│   ├── Basic.lean
│   ├── AlgebraIdentity.lean
│   ├── Modular.lean
│   ├── QuadraticRing.lean
│   ├── Mordell.lean
│   └── Examples.lean
└── README.md

⸻

5.2 Mordell 方程的 Lean 4 表示

可以定义：

def MordellEq (d x y : ℤ) : Prop :=
  y ^ 2 = x ^ 3 + d

说明：

* d 是方程参数；
* x、y 是整数变量；
* 使用 ℤ 而不是 ℕ，因为 y 可能为负；
* 指数运算在 Lean 中写作 ^。

⸻

5.3 参数化解的形式化

定义候选解：

x = m^2 - d
y = m(3d+m^2)

证明其满足 Mordell 方程。

5.3.1 正号情形

假设：

d = 1 - 3m^2

证明：

(m(3d+m^2))^2 = (m^2-d)^3+d

Lean 证明可使用：

subst d
ring

5.3.2 负号情形

假设：

d = -1 - 3m^2

证明类似恒等式。

⸻

5.4 三次展开公式的形式化

证明：

(a+b\sqrt d)^3
=
a(a^2+3b^2d)
+
b(3a^2+b^2d)\sqrt d

在 Lean 中可以先抽象成代数恒等式。

如果暂时不直接建模 √d，可以将其拆成两个系数公式：

\operatorname{realPart}((a+b\sqrt d)^3)
=
a(a^2+3b^2d)
\operatorname{sqrtPart}((a+b\sqrt d)^3)
=
b(3a^2+b^2d)

⸻

5.5 模运算与奇偶性条件的形式化

处理类似：

d \equiv 2 \text{ or } 3 \pmod 4

以及一些整数平方模运算性质。

可以使用：

* ZMod 4；
* ZMod 8；
* norm_num；
* omega；
* decide；
* 有限枚举。

这一节可以作为 AI 辅助证明生成的中等难度案例。

⸻

5.6 特例方程的形式化验证

针对：

d=-1,-2,-5,-6,-13

可以分别建立定理。

例如验证某个候选解：

70^2 = 17^3 - 13

即：

4900 = 4913 - 13

Lean 中可用：

norm_num

5.6.1 d = -1 情形

方程：

y^2 = x^3 - 1

5.6.2 d = -2 情形

方程：

y^2 = x^3 - 2

5.6.3 d = -5 情形

方程：

y^2 = x^3 - 5

5.6.4 d = -6 情形

方程：

y^2 = x^3 - 6

5.6.5 d = -13 情形

方程：

y^2 = x^3 - 13

可以根据你实际完成情况写：

方程	形式化内容	完成情况
y² = x³ - 1	候选解验证 / 解分类	已完成 / 部分完成
y² = x³ - 2	候选解验证 / 解分类	已完成 / 部分完成
y² = x³ - 5	无解条件分析	已完成 / 部分完成
y² = x³ - 6	无解条件分析	已完成 / 部分完成
y² = x³ - 13	候选解验证	已完成 / 部分完成

⸻

5.7 二次整数环相关命题的形式化探索

这一节写高难部分，不一定要求全部完成。

包括：

* 二次整数环元素表示；
* 共轭；
* 范数；
* 乘法公式；
* 主理想；
* 理想乘法；
* 理想类群条件。

可以说明：

理想与类群部分属于本文形式化中难度最高的部分。本文完成了相关数学对象的 Lean 4 表达和部分辅助引理的尝试，并分析了其困难来源。

⸻

5.8 实现过程中的典型问题

可以列出：

1. 整数、自然数、有理数之间的类型转换；
2. 指数运算的化简；
3. ring 使用前需要整理等式；
4. ZMod 与 Int 之间转换复杂；
5. Mathlib 定理名称难以查找；
6. AI 容易编造 Lean 中不存在的定理；
7. 理想和类群相关 API 使用困难。

⸻

第 6 章 多模型 AI 辅助 Lean 4 形式化实验与分析

本章是你的实验核心。

⸻

6.1 实验目的

实验主要回答以下问题：

1. 不同 AI 模型在 Lean 4 形式化任务中的表现是否存在明显差异？
2. AI 更擅长哪些类型的 Lean 任务？
3. AI 在复杂数学形式化中主要失败在哪里？
4. 编译器反馈能否显著提高 AI 输出代码的成功率？
5. AI 在 Lean 证明开发中适合作为什么角色？

⸻

6.2 实验模型

可以选择 3 到 5 个模型。

例如：

模型编号	模型类型	说明
M1	GPT 系列	通用推理和代码能力较强
M2	Claude 系列	长文本理解和证明解释能力较强
M3	Gemini 系列	多模态和代码生成能力较强
M4	DeepSeek 系列	数学推理和代码能力较强
M5	国产通用模型	用于比较中文 prompt 下的表现

论文中可以不写太多商业宣传，保持中立。

⸻

6.3 实验环境

包括：

* Lean 4 版本；
* Mathlib4 版本；
* VS Code；
* Lake；
* 同一组 prompt；
* 同一组任务；
* 每个任务最多交互 3 轮；
* 统一记录编译结果。

⸻

6.4 实验任务设计

建议设置六类任务。

任务编号	任务类型	示例	难度
T1	数学证明理解	解释 Mordell 方程证明路线	低
T2	Lean 命题建模	将数学命题转写为 theorem	中
T3	简单证明生成	使用 ring 证明恒等式	低
T4	报错修复	根据 Lean 报错修改代码	中
T5	证明拆解	将主定理拆成辅助引理	中高
T6	复杂结构建模	理想、类群、二次整数环	高

⸻

6.5 实验流程

统一流程：

给定同一任务
    ↓
向不同 AI 输入相同 Prompt
    ↓
记录首次输出
    ↓
放入 Lean 4 编译
    ↓
记录编译结果
    ↓
若失败，将错误信息反馈给 AI
    ↓
最多迭代 3 轮
    ↓
记录最终结果

实验中应记录：

* 首次是否通过；
* 第几轮通过；
* 是否改变数学命题；
* 是否编造不存在定理；
* 是否需要人工修改；
* 失败原因。

⸻

6.6 评分标准

可以采用 5 分制。

分数	标准
5 分	代码可编译，数学含义正确，证明简洁
4 分	代码基本正确，少量人工修改后通过
3 分	思路正确，但代码存在较多错误
2 分	有部分相关内容，但无法完成任务
1 分	输出基本无效或严重偏离任务

⸻

6.7 实验结果统计

可以设计以下表格。

6.7.1 各模型总体表现

模型	T1	T2	T3	T4	T5	T6	平均分
M1							
M2							
M3							
M4							
M5							

6.7.2 可编译性统计

模型	任务数	一次通过数	多轮通过数	最终失败数	一次通过率	最终通过率
M1						
M2						
M3						
M4						
M5						

6.7.3 错误类型统计

错误类型	M1	M2	M3	M4	M5
Lean 4 语法错误					
Mathlib API 幻觉					
类型错误					
tactic 失败					
数学条件遗漏					
证明粒度过大					
改变原命题					

⸻

6.8 成功案例分析

选择 2 到 3 个成功案例。

案例一：代数恒等式证明

说明 AI 能够识别这类目标适合用：

ring

案例二：候选解验证

例如验证：

70^2 = 17^3 - 13

Lean 中：

norm_num

案例三：报错修复

展示 AI 根据 Lean 报错修改代码，最终通过。

⸻

6.9 失败案例分析

选择 2 到 3 个失败案例。

失败案例一：编造 Mathlib 定理

AI 可能生成看似合理但不存在的 theorem 名称。

失败案例二：类型类实例无法推断

在理想、环、代数结构相关内容中，容易出现：

failed to synthesize instance

失败案例三：证明粒度过大

AI 直接试图证明主定理，但没有拆分辅助引理，导致失败。

失败案例四：遗漏数学条件

例如忽略：

d < 0

或：

d \equiv 2,3 \pmod 4

或：

3 \nmid h(\mathcal{O}_K)

⸻

6.10 多模型对比结论

可以从几个角度总结：

1. 所有模型在简单代数恒等式上表现较好；
2. 不同模型在数学解释和证明拆解上差异明显；
3. 所有模型在理想和类群相关任务上都存在困难；
4. 编译器反馈能显著提升最终通过率；
5. AI 更适合作为 Lean 证明开发辅助工具，而不是完全自动证明工具。

⸻

第 7 章 总结与展望

⸻

7.1 本文工作总结

总结全文：

1. 本文研究了 AI 辅助 Lean 4 数学形式化方法；
2. 以 Mordell 方程整数解问题为案例；
3. 分析了原数学证明中的关键公式和定理；
4. 将部分数学内容转化为 Lean 4 定义、引理和定理；
5. 使用多个 AI 模型进行形式化辅助实验；
6. 分析了 AI 在 Lean 4 证明开发中的优势和局限。

⸻

7.2 本文主要结论

可以写：

1. AI 对 Lean 4 中简单代数证明有明显帮助；
2. AI 能辅助数学证明拆解和 theorem statement 生成；
3. AI 在复杂 Mathlib API 和类型类问题上仍然不稳定；
4. Lean 编译器反馈是提高 AI 生成代码质量的关键；
5. 对复杂数学形式化，应采用“小引理拆解 + AI 辅助 + 编译验证 + 人工审查”的方法。

⸻

7.3 本文不足

一定要写，显得真实。

可以写：

1. 本文没有完整形式化原论文中的全部类群计算；
2. 理想和类群相关内容仍存在较大形式化难度；
3. 多模型实验任务数量有限；
4. 实验结果可能受 prompt 设计影响；
5. AI 模型版本更新较快，实验结论具有一定时效性。

⸻

7.4 未来工作展望

可以写：

1. 继续完善 Mordell 方程主定理的 Lean 4 形式化；
2. 深入研究二次整数环和类群在 Mathlib4 中的表达；
3. 扩大 AI 模型和任务数量；
4. 构建 Lean 报错自动反馈系统；
5. 结合检索增强技术减少 AI 的 Mathlib API 幻觉；
6. 将方法推广到更多数论形式化问题。

⸻

参考文献

建议至少包括几类：

Lean 与 Mathlib

* Lean 官方文档；
* Mathlib4 文档；
* Theorem Proving in Lean 4。

形式化数学

* 交互式定理证明相关论文；
* Lean 社区形式化项目；
* 数学证明形式化相关研究。

AI 辅助证明

* 大语言模型辅助代码生成；
* AI for theorem proving；
* Lean 自动证明相关研究。

Mordell 方程与原论文

* 原论文 Formalized Class Group Computations and Integral Points on Mordell Elliptic Curves；
* Mordell 方程相关数学文献；
* 代数数论教材或参考书。

⸻

附录

建议放这些内容。

附录 A：部分 Lean 4 代码

放你最终通过编译的核心代码。

附录 B：实验 Prompt 示例

放几类 Prompt：

* 数学解释 Prompt；
* Lean 建模 Prompt；
* 证明生成 Prompt；
* 报错修复 Prompt；
* 证明拆解 Prompt。

附录 C：AI 输出示例

展示不同 AI 对同一任务的输出差异。

附录 D：典型编译错误与修复记录

记录：

错误信息	错误原因	修复方法

附录 E：实验数据统计表

放完整实验表格。

⸻

最终推荐目录版

可以直接采用下面这个目录：

# 基于人工智能和 Lean 的形式化及其应用
## ——以 Mordell 方程整数解的 Lean 4 形式化为例
## 摘要
## Abstract
## 第 1 章 绪论
### 1.1 研究背景
### 1.2 研究意义
### 1.3 国内外研究现状
### 1.4 本文研究内容
### 1.5 本文创新点
### 1.6 论文结构安排
## 第 2 章 Lean 形式化与 AI 辅助证明基础
### 2.1 形式化数学概述
### 2.2 交互式定理证明器简介
### 2.3 Lean 4 基础
### 2.4 Mathlib4 数学库简介
### 2.5 数学证明到 Lean 形式化证明的转化
### 2.6 AI 辅助 Lean 证明开发
## 第 3 章 Mordell 方程的数学基础与证明思路
### 3.1 Mordell 方程概述
### 3.2 方程的基本变形
### 3.3 二次数域与二次整数环
### 3.4 二次整数环中的范数
### 3.5 理想与理想分解
### 3.6 类群与类数条件
### 3.7 类群下降法的证明思路
### 3.8 关键公式推导
### 3.9 原论文中涉及的主要定理
### 3.10 面向 Lean 4 的形式化目标拆解
## 第 4 章 AI 辅助 Lean 4 形式化方法设计
### 4.1 整体方法框架
### 4.2 形式化任务划分
### 4.3 Lean 4 命题建模策略
### 4.4 Prompt 设计策略
### 4.5 编译器反馈驱动的迭代修复
### 4.6 人工介入策略
### 4.7 评价指标设计
## 第 5 章 Mordell 方程相关命题的 Lean 4 形式化实现
### 5.1 项目环境
### 5.2 Mordell 方程的 Lean 4 表示
### 5.3 参数化解的形式化
### 5.4 三次展开公式的形式化
### 5.5 模运算与奇偶性条件的形式化
### 5.6 特例方程的形式化验证
### 5.7 二次整数环相关命题的形式化探索
### 5.8 实现过程中的典型问题
## 第 6 章 多模型 AI 辅助 Lean 4 形式化实验与分析
### 6.1 实验目的
### 6.2 实验模型
### 6.3 实验环境
### 6.4 实验任务设计
### 6.5 实验流程
### 6.6 评分标准
### 6.7 实验结果统计
### 6.8 成功案例分析
### 6.9 失败案例分析
### 6.10 多模型对比结论
## 第 7 章 总结与展望
### 7.1 本文工作总结
### 7.2 本文主要结论
### 7.3 本文不足
### 7.4 未来工作展望
## 参考文献
## 附录
### 附录 A：部分 Lean 4 代码
### 附录 B：实验 Prompt 示例
### 附录 C：AI 输出示例
### 附录 D：典型编译错误与修复记录
### 附录 E：实验数据统计表

本文以 Mordell 方程整数解问题为案例，构建了 AI 辅助 Lean 4 数学形式化流程，并通过多模型对比实验分析了大语言模型在复杂数学证明形式化中的能力边界。