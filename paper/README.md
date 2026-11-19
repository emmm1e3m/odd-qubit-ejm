# 双语论文与编译说明

**A unified construction of continuously tunable multiqubit elegant joint measurements**<br>
**连续可调多比特优雅联合测量的统一构造**

作者：Tingyu Zhang、Yan Cen（通讯作者）。共同单位：Department of Physics, Fudan University, Shanghai, China。

- [英文 PDF](main.pdf) · [英文源文件](main.tex)
- [中文 PDF](main-zh.pdf) · [中文源文件](main-zh.tex)
- [参考文献](references.bib)
- [精确复算程序与说明](reproduce/README.md)
- [Lean 工程](../lean-unified/README.md) · [形式化对应](../lean-unified/COVERAGE.md)

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

[完整复现归档1.2.0](../archives/multiqubit-ejm-verification-1.2.0.zip)将当前Lean工程、依赖配置与附录E1精确脚本和证书放在一个可下载包中；版本区别见[归档说明](../archives/README.md)。

形式化证明与计算结果见[验证记录](../VERIFICATION.md)。

精确复算使用Python、SymPy和NumPy；安装`reproduce/requirements.txt`后运行：

```text
python reproduce/verify_exact.py
python -B reproduce/all_n_gme/verify.py
```

版式依据：[PRA作者指南](https://journals.aps.org/pra/authors)、[REVTeX](https://journals.aps.org/revtex)。
