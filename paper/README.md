# PRA 双语校阅稿

**A unified construction of continuously tunable multiqubit elegant joint measurements**<br>
**连续可调多比特优雅联合测量的统一构造**

作者：Tingyu Zhang、Yan Cen（通讯作者）。共同单位：Department of Physics, Fudan University, Shanghai, China。

- [英文 PDF](main.pdf) · [英文源文件](main.tex)
- [中文 PDF](main-zh.pdf) · [中文源文件](main-zh.tex)
- [参考文献](references.bib)
- [精确复算程序与说明](reproduce/README.md)
- [Lean 工程](../lean-unified/README.md) · [形式化对应](../lean-unified/COVERAGE.md)

2026-11-02 版本采用 REVTeX 4.2 的 PRA 双栏排版，包含八节正文、四个附录、三张图与五张表。讨论与结论独立成节；两版采用对应的章节、数学内容和稳定标签，共用英文图表及完整图注。

## 编译与图表

安装 TeX Live（含 REVTeX、BibTeX、XeLaTeX 与 Fandol 中文字体）后，在本目录运行：

```text
python build.py
```

`python build.py en` 或 `python build.py zh` 可单独编译。英文使用 pdfLaTeX，中文使用 XeLaTeX；辅助文件位于 `.build/`，最终 PDF 位于本目录。

正文、附录和共享图表片段位于 `sections/`，矢量图位于 `figures/`。科学图表按正文闭式公式生成；安装 `figures/requirements-figures.txt` 中的依赖后运行：

```text
python figures/make_figures.py
```

配套 Lean 工程位于相邻的 `../lean-unified/`，其基础依赖位于 `../lean/`。复制形式化材料时需保留这两个相邻目录。论文的解析论证完整保留在正文与附录中。

## 作者校阅说明

- 后续术语修订已同步中英文及图表：“四律”改为“四种允许的半径变化规律”，“存活字符”改为“配对后未相消的字符”，颜色模型改用“四组输入及其相位”的直接描述；引言删除括号命名。110 个显示公式及交叉引用编号不变，重新编译与相关页排版检查通过。
- 已按中文批注稿统一术语、补足各节目的、重写讨论并将汇总表移入讨论；六比特结果改为定理后的简述，四比特论述按问题、直线限制、弯曲构造组织。附录按证明依赖重排，增加系数比较表，说明换元与估计的用途。
- 文献从 7 篇增至 15 篇，新增来源均已核对并在双语引言中引用。
- 稿件不显示日期；致谢采用作者提供的 OpenAI Codex（GPT-6 Astra）用途及人工审阅说明。
- 结论已说明主要数学结果已在 Lean 中完成形式化证明；代码可用性声明链接至已发布的 [Zenodo 归档](https://doi.org/10.5281/zenodo.23882488)，版本 1.0.0，含证明源码、依赖配置和复现说明，采用 MIT 许可。
- 两版已重新编译并逐页检查：英文 17 页、中文 18 页；132 个交叉引用标签及 15 项文献编号一致。原有 107 个显示公式保留，附录 D 的局部变量按批注重命名，另增加 3 个用于展开既有推导的显示公式。无未定义引用、缺字、越栏或浮动阻塞。
- 批注中的 `n>5` 与五比特已证结论不一致，本文保留 `n≥5`。本次为编辑修订，Lean 源码未改，形式化证据沿用[既有证明审查](../VERIFICATION.md)。

## 既有验证入口

精确复算使用 Python 与 SymPy：

```text
python reproduce/verify_exact.py --output reproduce/verification_results.json
```

Lean 4.35.0、mathlib v4.35.0 的环境、构建方式及范围见上方工程链接。

版式依据：[PRA 作者指南](https://journals.aps.org/pra/authors)、[REVTeX](https://journals.aps.org/revtex)。
