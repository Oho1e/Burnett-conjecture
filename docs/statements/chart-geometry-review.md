# 图内几何桥的独立复核

实际源、完整类型和重要定义先独立读回，再与锁定原文91–105、333–340、352–389行比较。新增人类语义确认未记录，开发合并不提升全文状态。每项接受结论绑定冻结源及实际查询回执，详见[源码绑定](chart-geometry-source-bindings.json)。

| 模块 | 正向构造 | 独立回读 | 接受范围 |
| --- | --- | --- | --- |
| MixedTensorNorm | N1 | N3 | 真实(1,2)收缩、范数及紧集比较 |
| TensorCoordinateChange | root | N1 | 真正全槽拉回及物理范数不变 |
| MixedConnectionError | root | N2 | 实际标量物理误差Lp∞ |
| ChartVolume | N3 | N1 | 正定密度和真实图Jacobian推前 |
| ManifoldMetric | N2 | root | 实际切丛r的图内正定/光滑 |
| ManifoldConnectionError | root | N2 | 消费已证明的r图数据 |
| LorentzVolume | N1 | root | 绝对det密度、局部∞转移和推前 |
| LorentzConnectionError | root | N2 | 用固定g₀体积的真实物理误差 |
| ManifoldMetricTransition | N3 | root | 真实frame、一般B矩阵law与同r测度 |
| ManifoldLorentzVolume | root | N2 | 同B的绝对det坐标measure相容 |

N2构造前置ManifoldMetric，不把其自身工作当独审；该依赖由root核查，N2只独立核root的新消费者。N1/N3在其他任务构造过的通用依赖各有独立记录，不将角色改名算作自审独立。N3完成Transition时N2仅询问进度，未提供证明或改源，不将其记为参与构造；root未参与该Transition实际证明。

原源查询同时覆盖两个重要model/metric abbrev，未仅按theorem名字核对。额外实际核验包括(1,2)与全协变范数在4I及各向异性对角度量下的区别、可逆A=2I的全槽权重及A=0反例、真实φ=2x的Jacobian16、Minkowski det−1的新density1和旧positive-only rho0。失败探针及未闭自动化只留历史，不计入通过。

其余明确边界：smooth-order的C∞是↑ENat.top而非analytic WithTop.top，Lp∞是ENNReal.top；图只在实际source/target上声明性质；总延拓域外无额外正性/光滑要求；没有增加有限测度、额外MemLp或uniform高阶gₙ界。当前Lp对象是标量物理norm函数的真实Lp∞，不虚构全bundle Lp。

局部图相容性不等于构造全局volume；原内在LC与全局序列条件尚未全部接入。旧正式结果、确认范围、信任A及父项OPEN保持，新的完整机器检查和实际CI另按当前候选取证。

本批10源105条显式公开声明（17定义、2abbrev、86定理）的独立原源/完整类型/传递公理回执均实际exit0。下表绑定实际独立报告，完整回执的字节SHA另见源码绑定：

| 模块 | 独立报告SHA256 |
| --- | --- |
| MixedTensorNorm | `d4d7384e9cf9c589fc36c689af5ebc35feb219383f6fffa3865200e8f0c14f2e` |
| TensorCoordinateChange | `091a7716ec5748d2850f8ee93c1ca7606b326172e2c6fe365240e6c26cbfeb58` |
| MixedConnectionError | `9b1053d01b1bc6191c337504c69c7d4c2b269f3aeb69b3bfa553899115f1b7af` |
| ManifoldMetric | `a4ff657b716f4852b919b05813e2fc47f314d36e0fefd24a71d5df6ae06fa15f` |
| ChartVolume | `b3a66b9595a282ef451d018d88abc87037b62209c315751ad22e4d2ba67781d3` |
| ManifoldConnectionError | `9e081a34574ec705fdd56414e3e1ab4d46b13df43f4446d600da423fb517358e` |
| LorentzVolume | `c17945a910b2016b1823912e79fcdab5d194ae6c9ecb7dc1b79f14fc3dc1050e` |
| LorentzConnectionError | `cf35eed5e346202159afa0d3721b1422c235807929047b13e44b650968377de0` |
| ManifoldMetricTransition | `fbdf71e98f7f089e6092862194520f207f821a9976b3faddd0fbd86f0b2c379e` |
| ManifoldLorentzVolume | `5b92b8b213eafec66649c318f62f3e1bda2a601fc37161f339e7bfd97f59e13c` |

新的254目标/84源完整候选、实际CI与工件另按最终版本检查；不将旧227绿色当作新结果。
