# 新版 EJM 论文的 Lean 形式化

本工程对应 [PRA 双语初稿](../paper/README.md)。使用新四特征核，覆盖全部整数 `n ≥ 5`，并形式化 Boolean 相位直线的模型最优值、偶数母族、低维刚性和曲线，以及谱熵和四比特测量不等价性。各结论的条件、真实物理对象和声明入口见 [COVERAGE.md](COVERAGE.md)。

主入口为 [UnifiedEJM.lean](UnifiedEJM.lean)。新版复用相邻 [基础库](../lean/README.md) 的通用门电路、有限位串及线性代数基础；旧奇数核没有被当作新版任意维构造。复制工程时请保留 `output/lean` 和 `output/lean-unified` 两个相邻目录。

## 版本与复现

- Lean：`leanprover/lean4:v4.35.0`。
- mathlib：`v4.35.0`，锁定提交见 `lake-manifest.json`。
- 新增生产源码均位于 `UnifiedEJM/`；个人任务目录和开发缓存不是构建所需输入。

已安装对应 Lean 工具链后，在本目录执行：

```text
lake exe cache get
lake build
lake env lean Audit.lean
```

已有依赖缓存时直接执行后两条即可。`Audit.lean` 打印关键声明的类型与传递公理依赖；预期仅出现 Lean/mathlib 的标准基础 `propext`、`Classical.choice`、`Quot.sound`（部分声明所需更少）。

## 验证记录

正式工程已经完成构建、关键声明公理审计和独立语义审查。审计入口为 [Audit.lean](Audit.lean)，实际类型与公理输出为 [axioms.txt](axioms.txt)。源码中没有 `sorry`、自定义公理或 `native_decide`。

构建及精确复算结果见 [验证说明](../VERIFICATION.md)。有限维计算用于交叉核验；任意维数由 Lean 中带自然数变量的证明处理。
