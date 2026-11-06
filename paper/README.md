# PRA 双语校阅稿

**A unified construction of continuously tunable multiqubit elegant joint measurements**<br>
**连续可调多比特优雅联合测量的统一构造**

作者：Tingyu Zhang、Yan Cen（通讯作者）。共同单位：Department of Physics, Fudan University, Shanghai, China。

- [英文 PDF](main.pdf) · [英文源文件](main.tex)
- [中文 PDF](main-zh.pdf) · [中文源文件](main-zh.tex)
- [参考文献](references.bib)
- [精确复算程序与说明](reproduce/README.md)
- [Lean 工程](../lean-unified/README.md) · [形式化对应](../lean-unified/COVERAGE.md)

2026-11-06版本采用REVTeX 4.2的PRA双栏排版，包含九节正文、五个附录、四张图与五张表。英文21页、中文22页；156个交叉引用标签和22项文献编号双语一致。图表及图注共用英文。

第VII节包含全n真正多体纠缠与精确并发度、零半径端点性质和完整测量酉的Clifford层级。附录B已合并被更强低维结果覆盖的重复证明，正文保留关键步骤，附录承接详细推导。全n证书见[独立复现包](reproduce/all_n_gme/README.md)。

## 编译与图表


安装 TeX Live（含 REVTeX、BibTeX、XeLaTeX 与 Fandol 中文字体）后，在本目录运行：

```text
python build.py
```

`python build.py en` 或 `python build.py zh` 可单独编译。英文使用 pdfLaTeX，中文使用 XeLaTeX；辅助文件位于 `.build/`，最终 PDF 位于本目录。

正文、附录和共享图表片段位于 `sections/`，矢量图位于 `figures/`。科学图表按正文闭式公式生成；安装 `figures/requirements-figures.txt` 中的依赖后运行：

```text
python figures/make_figures.py
python figures/make_clifford_figure.py
```

配套 Lean 工程位于相邻的 `../lean-unified/`，其基础依赖位于 `../lean/`。复制形式化材料时需保留这两个相邻目录。论文的解析论证完整保留在正文与附录中。

## 验证与复现

双语编译、交叉引用与相关页面排版检查均通过，图4在两版均位于第9页。现有证明与计算记录见[验证说明](../VERIFICATION.md)。论文保留主要数学结果已在Lean中完成形式化证明的声明。

精确复算使用Python、SymPy和NumPy；安装`reproduce/requirements.txt`后运行：

```text
python reproduce/verify_exact.py
python -B reproduce/all_n_gme/verify.py
```

版式依据：[PRA作者指南](https://journals.aps.org/pra/authors)、[REVTeX](https://journals.aps.org/revtex)。
