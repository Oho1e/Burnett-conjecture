# X03生产源码的独立反向核验

10源194公开声明已实际独立回读完整源码、重要定义、全部类型和传递公理；实际exit0，仅约定三基础公理，无警告。Model的四个具名继承实例纳入计数。工程整合、作者确认和远端CI分别记录，源码核验本身不代替后三者。

| 模块 | 声明数 | 独立报告SHA256 |
| --- | --- | --- |
| AngularHamilton | 24 | `bb6b7a6903ac689035660e902854ef1a2d0e40efa887290e2164abb9c7721116` |
| RotatingTensor | 23 | `bb6b7a6903ac689035660e902854ef1a2d0e40efa887290e2164abb9c7721116` |
| TimeIntegral | 2 | `bb6b7a6903ac689035660e902854ef1a2d0e40efa887290e2164abb9c7721116` |
| ScaledCutoffs | 19 | `bb6b7a6903ac689035660e902854ef1a2d0e40efa887290e2164abb9c7721116` |
| SpacetimeSplit | 7 | `bb6b7a6903ac689035660e902854ef1a2d0e40efa887290e2164abb9c7721116` |
| HamiltonIdentification | 17 | `bb6b7a6903ac689035660e902854ef1a2d0e40efa887290e2164abb9c7721116` |
| MeasureEstimates | 7 | `bb6b7a6903ac689035660e902854ef1a2d0e40efa887290e2164abb9c7721116` |
| SpacetimeCutoffs | 35 | `bb6b7a6903ac689035660e902854ef1a2d0e40efa887290e2164abb9c7721116` |
| MeasureModel | 56 | `d65bd3f5f02f58bda4da5bbd1349c81841e6d61eb94e2dc01c4f22d8874b8162` |
| NoTransport | 4 | `0c258539b7f374da60d721074afcd5fb0bdf744b194ed0de760c4568a579f436` |

前八源五项逐字推广、三项body不变并添加正常production imports；Model和最终NoTransport另有完整生产前缀核签，最终从未import私有证据目录。Model初次缺两个显式Mathlib imports的生产构建失败已排除，接受版本为补齐Bochner.Set/Lebesgue.Basic的实际成功源码。

反向核验确认原单位相空间、正Measure、仅原空间LF、同一T完整对称矩测试及canonical输运类；00与两half的12矩因子正确。generic total integral公式与真实可积性分开：最终所有μ积分和大R缩放消费者的可积性均实际证明，不靠不可积默认零。

最后四定理真正消除额外积分/误差假设，并将全部T性质和完整¬∃μ汇入同一个总定理；R=B/A+1和约去R²合法，A/B/R均有实际正性。全局坐标测试是原I域合法子类，较少假设下无表示足够推出原不可能，不倒置强弱。两时间方向保留，物理Q=1未与Pi sup单位球混淆。

独审者未构造所审新源；既有依赖和曾审支持结果的角色分别记录。原T不是被替换的G(m)，不宣称真空极限反例，不宣称原fold/branch那条可选路线也已认证。源/报告/回执/旧main输入见[绑定](rotating-null-moment-source-bindings.json)。

新增解释的作者确认尚未记录。新354目标/115源完整候选机器检查、实际main组合CI及工件核验另取当前回执；旧main绿色不覆盖本批。整篇、F04/F05及其他未闭合研究结果仍OPEN。
