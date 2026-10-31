# PRA 双语初稿

**A unified construction of multiqubit elegant joint measurements**<br>
**多比特优雅联合测量的统一构造**

作者：Tingyu Zhang、Yan Cen（通讯作者）。单位及邮箱已按给定信息排版。

- [英文 PDF](main.pdf) · [英文主源文件](main.tex)
- [中文 PDF](main-zh.pdf) · [中文主源文件](main-zh.tex)
- [参考文献](references.bib)
- [精确复算程序与说明](reproduce/README.md)
- [新版 Lean 工程](../lean-unified/README.md) · [逐项形式化对应](../lean-unified/COVERAGE.md)

采用 REVTeX 4.2 的 PRA 双栏格式，按既定结构组织七节正文、四个正式附录、三张主图和一张结论表。中文与英文的公式、定理条件和引用编号对应。本目录保存当前双语稿，配套材料包括 Lean 证明、精确复算程序与验证记录；[GitHub 仓库](https://github.com/emmm1e3m/odd-qubit-ejm) 的 Git 历史保留上一版奇数构造。

## 编译

安装 TeX Live（含 REVTeX、BibTeX、XeLaTeX 及 Fandol 中文字体）后，在本目录执行：

```text
python build.py
```

也可使用 `python build.py en` 或 `python build.py zh`。英文用 pdfLaTeX，中文用 XeLaTeX；辅助文件写入 `.build/`，最终 PDF 保留在本目录。

正文和附录位于 `sections/`，图形位于 `figures/`。图形代码为 `figures/make_figures.py`，其依赖列于同目录的 `requirements-figures.txt`；绘图使用正文闭式公式。

## 验证入口

精确复算只需 Python 与 SymPy：

```text
python reproduce/verify_exact.py --output reproduce/verification_results.json
```

Lean 4.35.0 和 mathlib v4.35.0 的版本、构建入口、主定理和公理审计见上方 Lean 工程。论文证明保留在正文与附录中，代码用于独立复算及形式检查。

版式依据：[PRA 作者指南](https://journals.aps.org/pra/authors)、[REVTeX](https://journals.aps.org/revtex)。稿件包含按 [APS AI 使用要求](https://journals.aps.org/authors/appropriate-use-ai-tools) 给出的工具用途说明。
