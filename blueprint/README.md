# Mordell Blueprints

本目录包含 Mordell Lean 4 项目的两个蓝图版本：

- `mordell_blueprint_simplified.svg`：论文中使用的简化依赖图，保留主证明链和最终结论。
- `mordell_blueprint_simplified_paper.svg` 和 `.png`：去掉图内标题和说明后的论文插图版本。
- `mordell_blueprint_full.html`：完整交互式声明蓝图，包含 156 个公开顶层声明节点和 262 条项目内依赖边。
- `mordell_blueprint_full.json`：完整蓝图的数据源，便于后续检查或重新绘图。

可用于论文正文的表述：

> Mordell 形式化分布在 12 个 Lean 源文件中。图 X 给出了主要结果的依赖关系图，该图是从完整蓝图（包含 156 个公开顶层声明节点）中简化而来。完整交互式蓝图见项目文档中的 `mordell_blueprint_full.html`。

论文插图可使用已经复制到 `Paper/论文/正式论文/figures/` 的无标题 PNG：

```tex
\begin{figure}[htbp]
  \centering
  \includegraphics[width=0.95\textwidth]{mordell_blueprint_simplified_paper.png}
  \caption{Mordell 形式化依赖关系的简化蓝图。方框表示 Lean 声明或声明组；虚线轮廓按证明层次分组。箭头从依赖项指向被依赖项。}
  \label{fig:mordell-blueprint-simplified}
\end{figure}
```

重新生成：

```bash
python3 Proj/Mordell/docs/generate_blueprints.py
```

完整图中的依赖边由源码中的项目内声明文本引用自动抽取，用作工程蓝图和导航图；严格证明正确性仍以 Lean kernel 和 `lake build` 为准。
