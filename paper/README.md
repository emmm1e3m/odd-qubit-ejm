# PRA 双语校阅稿

**A unified construction of continuously tunable multiqubit elegant joint measurements**<br>
**连续可调多比特优雅联合测量的统一构造**

作者：Tingyu Zhang、Yan Cen（通讯作者）。共同单位：Department of Physics, Fudan University, Shanghai, China。

- [英文 PDF](main.pdf) · [英文源文件](main.tex)
- [中文 PDF](main-zh.pdf) · [中文源文件](main-zh.tex)
- [参考文献](references.bib)
- [精确复算程序与说明](reproduce/README.md)
- [Lean 工程](../lean-unified/README.md) · [形式化对应](../lean-unified/COVERAGE.md)

2026-11-01 版本采用 REVTeX 4.2 的 PRA 双栏排版，包含八节正文、四个附录、三张图与四张表。讨论与结论独立成节；两版采用对应的章节、数学内容和稳定标签，共用英文图表及完整图注。

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

- 主线保留全 $n≥5$ 的统一可调族、两值相位直线精确界、偶数 $n≥8$ 二维嵌入以及低维刚性与弯曲增强。已删除旧奇数稿的版本叙述与单独自引；重复的有限算术移至附录 A。
- 致谢及资助待填写：`[ACKNOWLEDGMENTS AND FUNDING TO BE COMPLETED]`。
- 数据与代码可用性待确认：`[DATA AND CODE AVAILABILITY TO BE CONFIRMED]`。以上占位符需在正式提交前由作者补全。
- 两版已重新编译并渲染检查：英文 15 页、中文 16 页。附录 B 直接复用通用相位公式，附录 D 合并重复的约化态和不等价证书展示，共删去 9 处重复显示公式；保留的 107 个显示公式块、关键证明及摘要不变。130 个交叉引用标签与 7 项文献编号双语一致，无未定义引用、缺字或公式越栏。最新 Lean 审查已补齐六比特一般几何桥与原门序入口；本次精简未改 Lean 源码，沿用同一源码的隔离重编及公理审计证据。详见[证明审查](../VERIFICATION.md)。

## 既有验证入口

精确复算使用 Python 与 SymPy：

```text
python reproduce/verify_exact.py --output reproduce/verification_results.json
```

Lean 4.35.0、mathlib v4.35.0 的环境、构建方式及范围见上方工程链接。

版式依据：[PRA 作者指南](https://journals.aps.org/pra/authors)、[REVTeX](https://journals.aps.org/revtex)。
