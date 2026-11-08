# EJM 论文的 Lean 形式化

本工程对应当前双语论文，从实际测量列和约化矩阵证明统一构造、模型最优值、偶数母族、低维结果，以及全 n 的真正多体纠缠和端点不等价性。精确条件和声明入口见 [COVERAGE.md](COVERAGE.md)。

主入口为 [UnifiedEJM.lean](UnifiedEJM.lean)。复制工程时请保留 `lean/` 与 `lean-unified/` 两个相邻目录，前者提供通用门电路、位串和线性代数基础。

## 复现

工具链为 Lean **4.35.0**，mathlib **v4.35.0** 的精确提交由 `lake-manifest.json` 锁定。在本目录执行：

```text
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean AllAxioms.lean
```

`Audit.lean` 打印关键声明的完整类型与公理依赖；`AllAxioms.lean` 检查全部导入的本地声明，包括私有辅助证明和自动生成声明，仅允许 `propext`、`Classical.choice`、`Quot.sound`。

## 当前覆盖与验证

2026-11-08 完成此前待补的全 n GME、统一端点与稳定子轨道不等价、余弦端点纯度及两族端点不等价，以及任意至多两值实生成元的规范化和模型最优值。

全 n GME 定理覆盖任意整数 n≥5、任意实参数及全部原始测量列，给出 GME=√(1−r²)>0，并证明极小割恰为单体割及其补割。Lean 采用 n=5…8 的有限核验和 n≥9 的更紧解析尾界，结合任意长度背景归纳与精确前缀系数证明。论文附录 E1 的原有 Python 证书作为独立复现路径保留，其中456项有限切分未全部逐项移植到Lean。

当前生产入口导入 **735** 个 UnifiedEJM 模块和 **29** 个基础模块。新增源码经过逐模块检查，未修改的既有证明保留已核验结果；统一入口重新编译，最终定理类型及全部 **105633** 项声明（其中 **89376** 项定理）的公理审计通过，非标准公理依赖为 **0**。本轮使用最多三个 Lean 检查进程并监测系统剩余内存，不设单进程内存上限。

详细结果见 [verification.json](verification.json)。其中较早日期的条目保留历史检查范围；本轮记录为 `all_n_formalization_2026_11_08`。独立精确复现程序的完整计算沿用此前结果，本轮没有重跑。
