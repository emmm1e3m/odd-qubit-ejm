# 新版 EJM 论文的 Lean 形式化

本工程对应 [PRA 双语初稿](../paper/README.md)。使用新四特征核，覆盖全部整数 `n ≥ 5`，并形式化 Boolean 相位直线的模型最优值、偶数母族、低维刚性和曲线，以及谱熵和四比特测量不等价性。各结论的条件、真实物理对象和声明入口见 [COVERAGE.md](COVERAGE.md)。

主入口为 [UnifiedEJM.lean](UnifiedEJM.lean)。本工程复用相邻 [基础依赖](../lean/README.md) 的通用门电路、有限位串及线性代数定义。复制工程时请保留 `lean` 和 `lean-unified` 两个相邻目录。

## 版本与复现

- Lean：`leanprover/lean4:v4.35.0`。
- mathlib：`v4.35.0`，锁定提交见 `lake-manifest.json`。
- 新增生产源码均位于 `UnifiedEJM/`；个人任务目录和开发缓存不是构建所需输入。

已安装对应 Lean 工具链后，在本目录执行：

```text
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean AllAxioms.lean
```

已有依赖缓存时直接执行构建与审计命令即可。`Audit.lean` 打印关键声明的类型与传递公理依赖；预期仅出现 Lean/mathlib 的标准基础 `propext`、`Classical.choice`、`Quot.sound`（部分声明所需更少）。

## 验证记录

当前包包含186个UnifiedEJM模块及29个基础依赖模块。已有2026-11-04验证及收尾复核记录包括77个有限划分证书、统一入口编译和4944项声明（4271项定理）的公理检查，非标准公理依赖为零。

- [当前源码清单](../verification/141/physics_sources.json)与[整合记录](../verification/141/finite_integration.json)。
- [收尾源码核对](../verification/163/delivery_check.json)、[编译结果](../verification/163/compile_results.json)及[4944项声明审计](../verification/163/all_axioms.txt)。
- [27项最终接口检查](../verification/164/FinalDeliveryCheck.lean)及[输出](../verification/164/final_delivery_check.txt)。
- [验证汇总](verification.json)与[发布验证说明](../VERIFICATION.md)。

`axioms.txt`和`all_axioms.txt`保留2026-11-01的历史审计；后者的3050项计数对应当时版本。最新已有收尾输出为上方4944项声明审计。

论文的精确复算入口见[说明](../paper/reproduce/README.md)，全n GME整数证书见[独立复现包](../paper/reproduce/all_n_gme/README.md)。
