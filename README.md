# 多比特优雅联合测量的统一构造

中文 | [English](README.en.md)

**Tingyu Zhang、Yan Cen（通讯作者）**<br>
Department of Physics, Fudan University, Shanghai, China<br>
邮箱：[23300190021@m.fudan.edu.cn](mailto:23300190021@m.fudan.edu.cn) · [cenyan@fudan.edu.cn](mailto:cenyan@fudan.edu.cn)<br>
**版本：2026-10-31，PRA 格式双语初稿**

- 论文 PDF：[英文，15 页](paper/main.pdf) · [中文，16 页](paper/main-zh.pdf)
- LaTeX 源码：[英文](paper/main.tex) · [中文](paper/main-zh.tex)
- 复现：[精确计算](paper/reproduce/README.md) · [Lean 工程](lean-unified/README.md) · [论文与形式化对应](lean-unified/COVERAGE.md)

本研究考察经过指定优雅联合测量（Elegant Joint Measurement，EJM）的连续相位变形，要求完整测量保持正交归一，各比特的局部 Bloch 向量保持共同半径的正四面体结构。记基准半径为 $r_E(n)=\sqrt3/2^{n-1}$。

## 主要结果

1. **全部整数 $n\ge5$ 的统一增强族。** 同一个四特征 Boolean 核给出完整测量，保持固定四面体方向，半径为

   $$r_n(t)=r_E(n)(1-\sin t).$$

   在 $[-\pi/2,\pi/2]$ 上，半径连续且严格递减，精确覆盖 $[0,2r_E(n)]$；$t=0$ 逐列恢复基准测量，右端点的所有单比特约化态为 $I/2$。
2. **Boolean 相位直线的精确最优值。** 对固定相位表示中经过该基点、在基点邻域保持规则几何的全部 Boolean 生成元和所有实参数取最大值，结果为 $r_E(n)$（$n=2,3,4$）或 $2r_E(n)$（$n\ge5$），且均可达到。结论也适用于去除整体相位并重标参数后的两值实生成元。
3. **偶数比特的二维包含。** 对所有偶数 $n\ge8$，前作偶数族与统一增强族是同一完整测量族的两个坐标截面。在论文给定域 $\Omega$ 上，$r_n(\alpha,\beta)=r_E(n)(\cos\alpha-\sin\beta)$，精确像为 $[0,2r_E(n)]$；两轴逐列恢复对应测量，两个方向在有序测量投影层面独立。
4. **四比特直线障碍与弯曲增强。** 固定相位表示中经过该基点的任意实相位直线，若在邻域保持规则几何，其半径始终不超过 $r_E(4)$。一条显式弯曲路径则从同一基点出发，在整个 $[0,\pi/4]$ 上严格增加半径，精确达到 $(1+1/\sqrt2)r_E(4)$。

论文还证明指定三比特基点在固定 Pauli 轨道表示中的局部刚性。六比特直接叠加的**带符号局部分量相等**当且仅当 $\sin\alpha\sin\beta=0$；在论文的四颜色相位模型（含独立全零串相位）内，基点附近的规则解恰为两条相交分支。

上述最优值针对指定相位模型。前作另有半径达到 $3r_E(4)$ 的四比特参数段；本研究证明该段内没有测量与本研究指定基点在共同局域酉、比特置换及结果重标号下等价，不主张全体 EJM 的全局最优性。

## 形式化与复现

[Lean 4.35.0 / mathlib v4.35.0 工程](lean-unified/README.md) 从实际电路的全部测量列和真实约化矩阵出发，形式化上述构造、模型最优界、低维结论与不等价性。覆盖还包括实际约化谱 $\lambda_\pm=(1\pm r)/2$、von Neumann 熵等于二元熵 $h_2((1+r)/2)$，以及统一路径上熵的严格单调性和端点。完整条件与声明入口见 [COVERAGE.md](lean-unified/COVERAGE.md)。相邻的 `lean/` 目录保留所需的通用基础依赖。

[精确复算程序](paper/reproduce/README.md) 使用 Python 与 SymPy，独立核对原相位、电路、有限字符和、导数证书、曲线恒等式及多项式不等价证书，并提供运行结果。有限维复算与任意维数的 Lean 证明分别承担交叉核验和普遍结论。

旧奇数比特版本保留在 Git 历史中。新版使用不同的四特征核，结果扩展至全部 $n\ge5$；当前论文、源码和验证入口均以上述链接为准。
