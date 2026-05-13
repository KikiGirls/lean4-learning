# AI 数学证明最新现状和相关工作

## 自然语言推理

自 2025 年以来，基于大语言模型的数学推理系统逐渐从单轮答案生成，转向“生成—验证—修正”的多阶段流程。在奥林匹克数学问题中，Huang 等提出的模型无关验证与修正流水线较具代表性。该方法综合使用 Gemini 2.5 Pro、Grok-4、GPT-5 等模型，在 IMO 2025 的六道题中解决了五道，效果明显优于直接生成答案的方式。这表明，在复杂数学推理中，引入外部验证、候选筛选和迭代修正机制，能够有效提高模型输出的可靠性[@Huang2025IMO]。同年，Google DeepMind 的 Gemini Deep Think 在 IMO 2025 中达到金牌水平，也进一步说明前沿模型在自然语言长程数学推导方面已经展现出较强能力[@DeepMind2025IMO]。

在研究级数学任务中，Aletheia 是近期较受关注的数学研究智能体。该系统由 Gemini Deep Think 系列模型驱动，采用生成、验证与修订相结合的工作方式，能够在自然语言层面参与文献检索、证明构造和结果修正等环节。相关研究表明，Aletheia 已经被用于 Erdős 问题、算术几何中的 eigenweights 计算，以及若干人机协作数学发现任务[@Feng2026AutonomousMath]。在 FirstProof 挑战中，Aletheia 面对十个未公开的研究级数学问题，其中六个问题最终被多数专家评估为已解决[@Feng2026FirstProof]。这说明 AI 数学推理的应用范围正在从竞赛数学进一步延伸到真实的研究问题。

除自动化推理系统外，人机协作式数学发现也是近年来值得关注的方向。Bryan 等人在代数几何中的工作展示了一种更接近数学研究实践的协作模式：AI 先处理特殊情形和具体计算，人类再从中提炼关键结构，并借助 AI 继续推进一般情形的证明。在这一过程中，AI 并不是完全替代数学家完成证明，而是在特殊案例分析、候选结构发现和局部证明生成中提供辅助，从而帮助研究者形成更一般的证明思路[@Bryan2026Motivic]。

截至 2026 年 5 月，Erdős Problem #1196 是 AI 参与数学发现的最值得关注案例之一。该问题是 Erdős、Sárközy 和 Szemerédi 关于本原集的猜想：对任意 $x$，若 $A\subset[x,\infty)$ 是本原整数集，即 $A$ 中任意两个不同元素互不整除，则是否有

$$

\sum_{a\in A}\frac{1}{a\log a}<1+o(1).

$$

其中 $o(1)$ 随 $x\to\infty$ 趋于 $0$[@Erdos1196, @Tao2026Primitive]。此前 Lichtman 证明了该问题的较弱上界[@Lichtman2023Primitive]

$$

\sum_{a\in A}\frac{1}{a\log a}<e^\gamma\frac{\pi}{4}+o(1)\approx 1.399+o(1).

$$

随后，GPT-5.4 Pro 在 Liam Price 的提示下给出了一条不同于既有人类证明路线的新思路，利用 von Mangoldt 权重建立估计。更准确地说，它证明了对任意本原集 $A\subset\mathbb{N}$，都有尾部估计

$$

\sum_{\substack{a\in A\\a>x}}\frac{1}{a\log a}
\le 1+O\left(\frac{1}{\log x}\right).

$$

该估计蕴含上述 $1+o(1)$ 型结论，因此 Erdős Problems 网站已将该问题标记为 “PROVED (LEAN)”[@Erdos1196]。此后，Alexeev、Barreto、Li、Lichtman、Price、Shah、Tang 和 Tao 将这一思路进一步发展为基于 von Mangoldt 权重的 Markov 链方法，并以 “von Mangoldt chains” 的形式系统化[@Alexeev2026Primitive, @Tao2026Primitive]。这一案例表明，AI 在部分前沿数学问题中已经能够提出具有研究价值的证明路线，并推动后续的人类数学研究。

## 形式化证明推理

在形式化证明方向，近期研究的一个明显变化，是系统不再满足于一次性生成 Lean 代码，而是逐渐转向与证明助手持续交互的智能体流程。AlphaProof 是这一方向中较有代表性的工作。该系统将 Lean 形式验证与强化学习结合起来，通过在 Lean 环境中搜索可验证的证明，在 IMO 2024 中达到银牌水平[@Hubert2025AlphaProof]。此后，Aristotle 进一步结合 Lean 证明搜索、自然语言推理以及专用几何求解器，在 IMO 2025 问题上取得金牌水平的结果[@Achim2025Aristotle]。这些工作表明，形式化证明系统的作用正在发生变化：它们不再只是检查已有证明是否正确，也开始参与到复杂数学问题的证明搜索之中。

与此同时，开源和半开源形式化证明系统也在 2025—2026 年间持续推进。DeepSeek-Prover-V2 通过子目标分解和强化学习提升了 Lean 4 证明生成能力[@Ren2025DeepSeekProverV2]；Goedel-Prover-V2 则利用脚手架式数据合成、Lean 编译器反馈自我修正和模型平均等方法，在开源形式化证明模型中取得了较好表现[@Lin2025GoedelProverV2]。Seed-Prover 1.5 将工具调用和 Lean 交互纳入训练与推理流程，并在 Putnam 2025 问题上展现出较强能力[@Chen2025SeedProver]。Numina-Lean-Agent 则把通用代码智能体、Lean MCP 工具、定理检索和非形式化推理结合起来，完成了 Putnam 2025 的全部 12 道题，体现了智能体方法在大规模形式化证明任务中的应用潜力[@Liu2026NuminaLeanAgent]。

除了竞赛基准测试之外，部分系统已经开始面向研究级形式化和真实证明工程。Aristotle 和 AxiomProver 都已用 Lean 形式化了 Erdős 未解问题的解决方案；AxiomProver 从 Fel 猜想的自然语言表述出发，自动生成可验证的形式化证明，解决了数值半群 syzygies 相关的开放猜想[@Chen2026FelConjecture]。在国内，北京大学 AI4Math 团队的 Rethlas/Archon 双智能体系统自主解决了悬置 12 年的交换代数开放问题安德森猜想，生成约 19000 行 Lean 4 形式化证明代码[@Ju2026Rethlas]。在更多人为参与下，Numina-Lean-Agent 与两位人类专家合作，形式化了 Brascamp-Lieb 定理[@Liu2026NuminaLeanAgent]；同时 Mistral AI 最新发布的 Leanstral 智能体也说明，面向真实 Lean 仓库的证明工程智能体正在成为新的发展方向[@Mistral2026LeanstralNews, @Mistral2026LeanstralDocs]。

## 本章小结

总体来看，AI 辅助数学证明正在经历从“自然语言解题工具”到“形式化证明工程助手”的转变。自然语言推理代理已经能够在竞赛题和部分研究级问题中提出有效证明思路；形式化证明代理则通过 Lean 编译反馈、定理检索、子目标分解和迭代修正，使证明结果获得机器可检查的可靠性。

陶哲轩曾预测，只要使用得当，2026 年水平的人工智能，将成为数学研究以及许多其他领域中值得信赖的合著者[@Tao2023AIAnthology]。当前的发展已经在一定程度上印证了这一判断：AI 不仅能够辅助生成证明想法，还能够参与定理检索、证明拆解、Lean 代码生成、错误修复和大规模形式化项目开发。对本文而言，这些工作说明，基于 AI 的 Lean 4 证明开发已经具备现实研究价值，也为后续开展具体命题的形式化与 AI 辅助证明实验提供了技术背景和研究依据。
