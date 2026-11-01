# EJM 复用基础

本目录保留[新版形式化](../lean-unified/README.md)所需的有限位串、门电路、Pauli 轨道、偏迹、谱、计数及 Walsh 恒等式。`OddEJM` 命名空间沿用既有定义；部分模块同时含旧构造的辅助定义，以保持新版证明源码与依赖稳定。

入口为 [OddEJM.lean](OddEJM.lean)。本目录共保留 29 个模块（含显式CNOT门序桥），使用 Lean 4.35.0 与 mathlib v4.35.0；具体依赖由 [lake-manifest.json](lake-manifest.json) 锁定。

完整构建和公理审计请从相邻 [lean-unified](../lean-unified/README.md) 工程运行。新版数学结论及论文对应见 [COVERAGE.md](../lean-unified/COVERAGE.md)。

旧奇数构造的论文、完整证明入口与复算记录保留在[历史版本](https://github.com/emmm1e3m/odd-qubit-ejm/tree/b4bf945139de081514effc228cf40724fb8bca4e)。
