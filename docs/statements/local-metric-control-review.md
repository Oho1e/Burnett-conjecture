# 局部控制交付的独立回读

2026-11-16。原文SHA256仍为`e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`。准确解释见[local-metric-control.md](local-metric-control.md)，冻结源码及24项新增支持目标见[绑定](local-metric-control-source-bindings.json)。

| 模块 | 正向 | 独立回读 | 准确范围 |
| --- | --- | --- | --- |
| InversePerturbation | N2 | N1 | 真实sup范数、矩阵复合、常数4/16/2/32、实际FiberMetric逆律；20声明通过 |
| InverseField | N2 | N3 | 显式矩阵逆、连续逆、紧性推B、实际uniform序列控制；16声明及非对角块压力例通过 |
| InverseSequence | N2 | N3 | 同一B及最终小量/界实际接contravariant与K子类型uniform；2声明通过 |
| BackgroundConnection | N2 | N3 | 局部C¹→实际ambient fderiv jet/Γ连续，紧性推G；8声明通过 |
| ConnectionError | N1 | N3 | 实际E定义及恒等式、6/192、固定K及uniform；14声明通过 |
| PerturbationJet | N1 | N3 | norm8及raw→J→E消费者，明确原r接口仍开；8声明通过 |
| ConnectionErrorSequence | N1 | N3 | 最终实际局部坐标组合17b524，全源及3定理完整类型/公理exit0，消除中间B/G/J/small/hcΓ前提 |
| UniformLInfinity | root | N2 | 真实Lp∞/restrict、无有限总测度假设、有限上界先于toReal、MemLp显式；3声明及边界例通过 |
| PositiveFunctional | N3 | root | 真实C_c/子空间、正性条件、C0范数与实际Urysohn局部界；4声明通过 |

独立回读从完整冻结源码、实际类型和重要定义出发；已有逆核心的相同哈希可作为消费者输入，不以作者摘要代替回读。声明查询条数是防漏证据，不是论文结果数。所有已完成回读的Lean与传递公理查询均exit0，仅三允许基础公理。原InversePerturbation保留一个未使用hB参数警告，非数学错误，未为清理警告改动已冻结类型。

九份生产源均已独立PASS，无未解决must-fix，共78显式公开声明（71定理、7定义）经完整类型/传递公理核签。N3六源汇总51声明，另有N1逆核心20、N2的Lp∞三条及root正泛函四条；不将额外压力实例重复计作生产声明。最终组合直接取得实际G，不需要此前说明中的backgroundConnectionOn连续性中转；该中间路径不作为新的开放义务。

非对角矩阵压力检查确认块`[[2,1],[1,2]]⊕I₂`的逆非对角元为−1/3，区别于逐项倒数。UniformLInfinity的零界/空集边界已实际核签，未用有限测度实例掩盖假设。PositiveFunctional独立Lean本身exit0；最初终端包装器在写成功回执后发生GBK打印失败，后以UTF-8读取核实四项公理报告，保留原日志，不虚构原包装器整体exit0。

本次最重要的范围核对是原文的`D=∇ʳ`及物理r范数。当前最终坐标组合、一般Lp∞及正泛函界均不能代替这一未闭合几何桥；不把新增一般工具的显式输入视为原PDO或admissible前提已满足。F04/F05父项和整篇未提升为已证，新作者确认待记录。

原PR7已由用户合并且真实main CI成功，当前基线是d5c3d06；本批代码/目标/说明一并进入新候选，实际组合机器与远端证据另取，不继承旧176目标绿色。最终合并仍交人类执行，子代理报告不是另一GitHub账号的Approve。
