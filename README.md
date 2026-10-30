# 任意奇数比特的显式可调 EJM

中文 | [English](README.en.md)

**作者：Tingyu Zhang**  
**日期：2026-10-30**

对每个奇数 $n\ge5$，本仓库给出一个通过已知多比特优雅联合测量（Elegant Joint Measurement，EJM）的显式连续族。所有测量态始终正交归一，每个比特的局部 Bloch 向量保持固定正四面体方向，全部比特及结果共享半径

$$
r_n(t)=\frac{\sqrt3}{2^{n-1}}(1-\sin t),\qquad
t\in[-\pi/2,\pi/2].
$$

在 $t=0$ 逐态恢复已知 EJM；精确半径范围为 $[0,\sqrt3/2^{n-2}]$，上端为已知点半径的两倍。零端点的所有单比特约化态均为 $I/2$。构造使用同一个固定五变量布尔函数及两个内部坐标块的奇偶校验，覆盖所有奇数 $n\ge5$。

## 阅读入口

- [中文论文 PDF](paper/main.pdf)：完整背景、构造、任意比特数的证明与物理解释。
- [LaTeX 源码](paper/main.tex)及[参考文献](paper/references.bib)。
- [Lean 说明](lean/README.md)及[主定理](lean/OddEJM/Main.lean)：形式化实现与定理对应。

## 复现

以下命令从仓库根目录开始。Python 检查使用 **Python 3.10+ 标准库**，无需安装科学计算包：

```text
python paper/verify_certificate.py
python paper/verify_measurement.py
```

第一条生成十六项精确 Walsh 证书；第二条从原相位及逐门作用出发，在 $n=5,7,9,11$ 上精确核对归一化、全部局部分量、背景零期望及顶点重数。结果分别写入 [certificate.json](paper/certificate.json) 和 [exact_results.json](paper/exact_results.json)。有限规模计算用于交叉检查；任意 $n$ 的结论由论文证明与 Lean 定理给出。

Lean 工程固定为 **Lean 4.35.0、mathlib v4.35.0**，精确依赖由 [lake-manifest.json](lean/lake-manifest.json) 锁定。安装 elan 后执行：

```text
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

依赖已就绪时可跳过缓存下载。最后一条输出主定理类型及其传递公理依赖；保存的核查结果见 [axioms.txt](lean/axioms.txt)。

编译论文需要 XeLaTeX、latexmk、BibTeX 和 ctex/Fandol 字体；已使用 TeX Live 2026 构建。从仓库根目录运行：

```text
latexmk -cd -xelatex -interaction=nonstopmode -halt-on-error paper/main.tex
```

## 形式化覆盖

`OddEJM.odd_ejm_family` 仅假设 $n\ge5$ 且 $n$ 为奇数，证明实际电路产生的全部测量列正交归一、投影完备、全部单比特偏迹的正四面体公式、标签重数、已知点对应，以及半径连续性、严格单调性和精确像集。附加定理覆盖实际局部矩阵的重数、约化谱特征根和纯度。

证明不使用 `sorry`、自定义公理或 `native_decide`；公理依赖为 Lean 的标准 `propext`、`Classical.choice`、`Quot.sound`。论文中的基 2 对数纠缠熵公式保留为由约化谱得到的解析推论，未纳入 Lean 工程。

所给最大半径是这条构造路径的精确端点；全体 EJM 的最优半径不在本结果范围内。
