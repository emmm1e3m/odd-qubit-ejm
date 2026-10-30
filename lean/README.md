# 任意奇数比特 EJM 的 Lean 形式化

本工程证明任意奇数 `n ≥ 5` 的统一连续可调测量族。主入口是 [Main.lean](OddEJM/Main.lean) 中的 `OddEJM.odd_ejm_family`；其参数仅为 `n ≥ 5` 与 `Odd n`。

主定理覆盖实际测量态的正交归一性、投影完备性、全部单比特偏迹的固定正四面体公式、每个局部标签的 `2^(n−2)` 重数，以及共同半径

`rₙ(t) = √3 (1 − sin t) / 2^(n−1)`

在 `[-π/2, π/2]` 上的连续性、严格递减及精确像 `[0, √3/2^(n−2)]`。`t=0` 的每一列严格恢复原基本对称相位生成的测量。

## 构建与核查

版本固定为 Lean **4.35.0**、mathlib **v4.35.0**；精确依赖由 `lake-manifest.json` 锁定。已安装 elan 的环境中，在此目录执行：

```text
lake exe cache get
lake build
lake env lean Audit.lean
```

本地依赖已就绪时可直接执行后两条。`Audit.lean` 显示最终定理类型并打印其传递公理依赖；核查输出保存在 [axioms.txt](axioms.txt)。证明使用标准 Lean 内核，未使用 `sorry`、自定义公理或 `native_decide`。标准公理为 `propext`、`Classical.choice`、`Quot.sound`。

## 与论文的对应

| 论文对象或步骤 | 实际形式化入口 |
| --- | --- |
| 基本对称多项式相位、整个参数相位与已知点 | `OriginalPhase.lean`、`measurement_original_phase` |
| 逐门 CNOT 链、末位 H、完整 H 张量列 | `CNOT.lean`、`Quantum.lean`、`Tensor.lean` |
| 任意列正交与投影之和为恒等矩阵 | `Orthonormal.lean`、`Completeness.lean` |
| 固定 Q、整数证书和一般维数压缩 | `Finite.lean`、`Compress.lean` |
| 任意奇数维的字符消去与稀疏掩码条件 | `Walsh.lean`、`FourWalsh.lean`、`Masks.lean` |
| 实际背景、物理零点缺陷与种子分量 | `WeightPhase.lean`、`Defect.lean`、`BackgroundBridge.lean`、`SeedExpectations.lean` |
| 实际群轨道、偏迹、固定方向和真实标签 | `Pauli.lean`、`Density.lean`、`FamilyGeometry.lean`、`Labels.lean` |
| 无额外物理假设的完整主定理与纯度 | `Main.lean` |
| 真实约化谱特征根与非零半径下的实际矩阵重数 | `Spectrum.lean`、`Consequences.lean` |

`reduced` 直接对其余比特的振幅乘共轭求和；目标 Bloch 公式由定理证明。任意维数由带自然数变量的证明处理，不依赖有限规模枚举。固定五变量函数是统一构造中的工具。

论文的基 2 对数熵表达式保留为解析推论，不在本工程的形式化范围内。

论文及精确复算程序位于 [paper](../paper/)。在仓库根目录运行 `python paper/verify_certificate.py` 与 `python paper/verify_measurement.py`，只需要 Python 标准库。
