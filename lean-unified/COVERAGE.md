# 论文与形式化逐项对应

对应 [`paper/main.tex`](../paper/main.tex) 与 [`paper/main-zh.tex`](../paper/main-zh.tex) 的同一组数学结果。下表的声明名均以 `UnifiedEJM.` 为前缀；点击模块可查看完整量词和定义。Lean 使用零起始位索引，论文使用一开始位索引。

| 论文位置 | 正式声明入口 | 覆盖内容 |
|---|---|---|
| II、附录 A：真实测量 | [Physical](UnifiedEJM/Physical.lean)：`Physical.measurement_orthonormal`、`Physical.measurement_complete`、`Physical.measurement_eq_original_gate_sequence` | 原相位及指定电路的全部列；内积、投影完备性和真实单体偏迹 |
| II、附录 A：几何条件 | [Regularity](UnifiedEJM/Regularity.lean)：几何与种子平方分量等价 | 任意四面体方向和结果标签，包含零半径；没有将相等分量直接定义成全部几何条件 |
| III、定理 1 | [Main](UnifiedEJM/Main.lean)：`unified_ejm_family` | 仅假设 `5 ≤ n`；同一核、原门列、完整测量、真实偏迹、固定四面体、基点、端点、精确半径像及严格单调 |
| III、附录 A：核与支撑 | [Features](UnifiedEJM/Features.lean)、[Kernel](UnifiedEJM/Kernel.lean)、[Walsh](UnifiedEJM/Walsh.lean)、[Masks](UnifiedEJM/Masks.lean) | 四特征公式、固定证书、所有 `n ≥ 5` 的背景消去及物理零点支撑计数 |
| III：连续性、重数、纯度 | [Analytic](UnifiedEJM/Analytic.lean)、[Main](UnifiedEJM/Main.lean)：`measurement_projector_continuous`、`measurement_reduced_multiplicity`、`measurement_purity` | 实际投影连续、正半径时每个实际约化矩阵的重数、真实偏迹纯度及完全混合端点 |
| III：局部谱与熵 | [EntropyFamily](UnifiedEJM/EntropyFamily.lean)：`measurement_actual_spectrum`、`measurement_vonNeumann_entropy`、`measurement_entropy_strictMonoOn` | 实际 Hermitian 约化矩阵的完整两根谱；以谱和定义的 von Neumann 熵等于二元熵，严格单调和端点 |
| IV、附录 B：四律 | [BooleanOriginal](UnifiedEJM/BooleanOriginal.lean)、[BooleanMeasurement](UnifiedEJM/BooleanMeasurement.lean)：`BooleanLines.original_four_laws`、`BooleanLines.regular_global_measurement` | `n ≥ 3` 的任意原始 Boolean 相位直线；由基点邻域几何条件推出四种解析形式，不预设背景为零 |
| IV、定理 2 | [BooleanMeasurement](UnifiedEJM/BooleanMeasurement.lean)：`BooleanLines.actual_boolean_model_exact_maximum` | 对 `n ≥ 2` 的全部 admissible 生成元与所有实参数取真正最大值；低维界及高维达到性均已证明 |
| IV：至多两值实生成元 | [BooleanNormal](UnifiedEJM/BooleanNormal.lean)：`BooleanLines.two_rate_phase`、`BooleanLines.originalLine_complement` | 逐点相位规范化及补集恒等式；包含常值生成元。最大值定理以规范化Boolean模型陈述，未另设任意实函数半径集合相等的包装定理 |
| V：前作偶数族 | [EvenLow](UnifiedEJM/EvenLow.lean)：`EvenLow.even_cosine_family` | 所有偶数 `n ≥ 2`，包括二比特空乘积、四比特支持；实际全部列、偏迹及基点 |
| V、定理 3 | [EvenAxes](UnifiedEJM/EvenAxes.lean)、[EvenGeometry](UnifiedEJM/EvenGeometry.lean)：`EvenFamily.measurement_reduced`、`EvenEmbedding.radius_image_exact`、`EvenFamily.ordered_measurement_parameter_injective` | 所有偶数 `n ≥ 8`，联合背景消去、Ω 上精确像、两轴逐列恢复及有序投影层面参数独立性 |
| V、附录 C：六比特 | [SixGeometry](UnifiedEJM/SixGeometry.lean)、[SixFamily](UnifiedEJM/SixFamily.lean)、[SixDirect](UnifiedEJM/SixDirect.lean)：`SixFamily.geometric_local_crossing`、`SixFamily.actual_local_crossing`、`SixFamily.direct_regular_iff` | 真实四联合颜色和独立零点相位模型；存在含基点的开邻域，其中一般几何正则测量恰为两支。邻域内全部带符号分量的正性由连续性证明，无额外正性假设。全实直接叠加条件仍针对带符号分量相等 |
| VI、附录 D：三比特刚性 | [ThreeQubitGeometry](UnifiedEJM/ThreeQubitGeometry.lean)：`ThreeQubit.geometric_three_qubit_rigidity`；[ThreeQubitDeterminant](UnifiedEJM/ThreeQubitDeterminant.lean)：`ThreeQubit.derivative_determinant` | 原门、原基点、七维约束导数、行列式 `1/4096` 和逆函数定理，结论针对完整测量几何 |
| VI、定理 4：所有实直线 | [LowDimensionalGeometry](UnifiedEJM/LowDimensionalGeometry.lean)：`LowDimensional.geometric_line_iff_planes`、`LowDimensional.geometric_real_line_measurement_radius_bound` | 去整体相位后的两个方向平面完整分类；任意实方向和全部测量列的半径不超过 `√3/8` |
| VI、定理 4：弯曲增强 | [CurvedMain](UnifiedEJM/CurvedMain.lean)：`Curved.curved_ejm_family` | 论文闭式根、整段 `[0, π/4]`、真实十六列和偏迹、基点、连续性、半径严格增加及精确像；无待证的 `H=T` 或种子前提 |
| VI、附录 D：初始斜率 | [CurvedSlope](UnifiedEJM/CurvedSlope.lean)：`Curved.radius_hasDerivAt_zero` | 直接对原闭式根求导，得到 `δ′(0) = −4/3`、`q′(0) = 4/3` 和 `r₄′(0) = √3/6` |
| 附录 D：不等价证书 | [ResultantCertificate](UnifiedEJM/ResultantCertificate.lean)、[MeasurementInequivalence](UnifiedEJM/MeasurementInequivalence.lean)：`FiniteInvariants.measurements159_not_equivalent` | 原始四比特相位与真实纯度；两必要多项式不共根、resultant 非零；共同局域酉、任意比特置换、结果重标号及列相位均被包括 |

## 证据的读法

`Physical` 从实际复振幅构造测量和偏迹；`Regularity` 把通常的四面体几何条件与种子约束连接。最优界和低维排除使用这些连接，结论不限于预先固定的分量等式。四比特不等价性使用真实 `Fin 16 → ℂ` 态上的张量局域酉与坐标置换，纯度保持是证明所得。

论文和 Lean 可以使用不同的消元顺序：例如四比特线性核以完整核分类验证，非零 resultant 由精确多项式证书验证。论文列出的辅助有限矩阵及数值还由精确复算程序单独核验。形式化的交付单位是上述精确数学结论及其物理定义链条。

本篇已删去的核最小唯一性、一般编码分类、距离二背景码及更宽流形全局连接不在本工程的新增结论中；它们也不是本文主定理的证明前提。对前作和上一版的文献归属、期刊状态及引文通过文献核查处理。
