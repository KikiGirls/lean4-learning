# 附录B：评价框架

评价方式参考 Erdős Problems Wiki 中对 AI 数学贡献的整理方式[@TaoErdosAIWiki2026]。该页面的用途不是建立统一 benchmark，而是记录 AI 在具体数学问题中的贡献位置、贡献完整性以及人类和文献参与情况。本文只评估 Mordell 方程 Lean 4 形式化这一固定案例，因此将该页面的贡献分区改造为适用于同一题目、三类实验模式的多维记录框架。

| Erdős Wiki 分区 | 文献资料状态 | 人类参与程度 | 本文中的对应含义 |
| --- | --- | --- | --- |
| Primary: AI standalone | 未知有可比文献 | 人类参与不显著 | AI 在未提供核心证明资料的情况下生成主要证明路线或主要 Lean 证明。 |
| Primary: AI alongside literature | 可比文献在事后发现 | 人类参与不显著 | AI 输出与既有文献相近，但实验时未显式提供该文献。 |
| Primary: AI building on literature | 实验前已知相关文献 | 人类参与不显著 | AI 基于论文、Lean3 证明、README 或已有 Lean 文件完成证明补全。 |
| Primary: AI collaborating with humans | 任意 | 人类参与显著 | 人类提供关键证明结构、核心 lemma 或实质性修复，AI 与人共同完成。 |
| Secondary: Literature search | 需要寻找资料 | 可有可无 | AI 查找并定位相关论文、Lean3 源码、项目文档或 Mathlib 定理。 |
| Secondary: Formalization | 已有数学证明或证明路线 | 可有可无 | AI 将自然语言证明、已有 Lean 证明思路或局部证明转化为 Lean 4 代码。 |
| Secondary: Artifact generation | 需要生成辅助产物 | 可有可无 | AI 生成实验记录表、脚本、证明依赖摘要或可复现实验材料。 |
| Secondary: Rewriting | 已有文本或证明说明 | 可有可无 | AI 改写证明解释、指出证明缺口、重组论文段落或优化论证表达。 |
| Secondary: Computation | 有明确计算任务 | 可有可无 | AI 编写或调用程序完成有限检验、统计、表格生成或构建结果汇总。 |

| 等级 | 含义 | 本文中的判定标准 |
| --- | --- | --- |
| Full | 完整贡献 | 输出完整满足当前实验目标；自然语言证明经人工复核正确，或 Lean 代码通过 `lake build` 且无 `sorry`。 |
| Partial | 部分贡献 | 输出包含实质性有用内容，例如正确证明框架、关键引理定位或接近可运行的 Lean 代码，但尚未独立完成目标。 |
| Incorrect | 错误贡献 | 输出存在数学错误、Lean 代码无法形成有效证明、削弱了定理陈述，或引用不存在的关键结论。 |
| Pending | 待确认 | 输出尚未经过人工复核或 Lean 构建验证，暂不能判定最终有效性。 |

| 维度 | 取值或记录方式 | 说明 |
| --- | --- | --- |
| AI 贡献角色 | Primary / Secondary | Primary 表示 AI 生成核心证明思路或完成主要证明构造；Secondary 表示 AI 主要承担解释、形式化、检索、改写、计算等辅助工作。 |
| 贡献类型 | Standalone / Alongside literature / Building on literature / Collaboration / Literature search / Formalization / Artifact generation / Rewriting / Computation | 参考 Erdős 页面中的分区，但映射到本文的 Mordell 形式化任务。 |
| 文献资料状态 | 未提供文献 / 提供论文或 Lean3 证明 / AI 自行检索 / 事后发现相关文献 | 用来区分模型是独立生成，还是基于已知证明路线、已有论文或已有形式化代码。 |
| 文献检索行为 | 无检索 / 人提供文献 / AI 检索并引用 / AI 检索但未有效使用 | 用来评价模型是否能主动找到并正确利用相关论文、README、Lean3 源码或项目内文档。 |
| 人类辅助程度 | 无 / 低 / 中 / 高 | 低表示人只提供题目或 Lean 报错；中表示人提供关键 lemma 名称、证明方向或文献入口；高表示人重写证明结构或实质性补全关键步骤。 |
| 验证方式 | 人工数学复核 / `lake build` / diff 审查 / 组合验证 | 自然语言证明以人工复核为主，Lean 证明以构建验证为主，智能体实验还需检查文件差异。 |
| 形式化完整性 | 无 Lean 代码 / Lean 片段 / 完整定理证明 / 项目级构建通过 | 用来区分自然语言贡献、局部代码贡献和完整形式化贡献。 |
