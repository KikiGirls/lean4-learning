# 正式论文 LaTeX 工程

这是根据 `Paper/2024年重庆大学论文模版/LaTeX版本.tex` 拆分出来的正式论文目录。

## 目录结构

- `main.tex`：论文主文件，包含封面、英文扉页、目录、全局格式和各章节引用。
- `chapters/abstract.tex`：中英文摘要。
- `chapters/chapter1.tex` 至 `chapters/chapter5.tex`：正文各章。
- `chapters/references.tex`：参考文献。
- `chapters/appendix.tex`：附录。
- `chapters/acknowledgements.tex`：致谢。
- `figures/`：图片资源，目前包含模版中的校徽和示例图。
- `out/`：建议作为 LaTeX 编译输出目录。

## 编译方式

建议使用 XeLaTeX：

```bash
cd /Users/kikigirl/Desktop/lean4-learning/Paper/论文/正式论文
xelatex -output-directory=out main.tex
xelatex -output-directory=out main.tex
```

目前封面中的学院、专业、指导教师仍是 `待填写`，后续确认信息后在 `main.tex` 顶部的命令区修改即可。
