# 辅助r局部控制的独立复核

本文档汇总本批冻结源码的实际反向回读。数学解释以实际类型、重要定义及锁定原文91–105、352–389行为依据。完整源码哈希与支持目标见[绑定](auxiliary-r-control-source-bindings.json)；语义确认尚未由用户/作者记录，整篇verified保持false。

| 模块 | 正向实现 | 独立回读 | 准确范围 |
| --- | --- | --- | --- |
| GramCoordinateBound | N1 | N3 | 实际Gram能量、构造Hilbert范数、逆对角坐标界 |
| CovariantTensorNorm | N2 | N1 | 具体二/三张量Kronecker、flatten、物理收缩及紧集常数 |
| LocalAeBound | N3 | N2 | 较大邻域ae到逐点、实际volume、F值MemLp∞ |
| AuxiliaryConnection | root | N1 | 实际Γr辅助导数、compact统一连接界及raw反解 |
| ConnectionErrorLInfinity | root | N3 | 实际E连续性、MemLp∞和同一E/K的实际类趋零 |
| AuxiliaryPhysicalBound | root | N3 | 局部物理L∞到实际E的uniform/L∞组合 |
| PositiveDensity | N1 | root | 实际正密度的限制测度及L∞桥 |
| RiemannianVolume | N2 | root | sqrt(detR)实际坐标测度及r消费者 |

N1是generic Gram的作者，但未参与N2的具体张量模块构造；其独立范围明确限于后者，generic Gram另由N3审核。N3是LocalAeBound作者，在root的E/Physical模块复核中只将其作为已冻结依赖消费，该依赖本身由N2独立核查。root不是正密度或坐标体积模块的正向实现者。

已经核对的压力例包括R=4I、纯坐标三张量的物理norm3=1/8而Pi norm=1，正确比较因子8取等，使用R⁻¹对角的错误方向被实际Lean反驳；还包括零测K={0}的ae界不能直接推出点态界，以及无限μ(K)下实际F值连续函数的MemLp∞。这些压力例补充源码与全类型核签，不替代一般证明。

完整回读须覆盖所有显式公开声明，另做定义与传递公理查询；只接受propext、Classical.choice、Quot.sound。未完成探针产生的sorryAx和编译失败分别保留为失败历史，不计入已接受回执。原InversePerturbation的unused hB提示保留，不据此宣称全工程无警告。

本批仍是局部坐标成果。原流形图、几何D与体积的推前识别、混合(1,2)误差的物理r范数和F04分析闭合未完成。原−B符号、旧确认范围、全部17项编号及3项必做未编号目标、信任A和原文字节不变。新增数学解释待所需人类确认；PR合并仅是开发整合。

最终8模块85条显式声明（15定义、70定理）的独立全源/完整类型/传递公理回执均实际exit0。下表绑定实际独立报告；完整回执的字节哈希另见源码绑定，归档保留原日志与失败历史。

| 模块 | 独立报告SHA256 |
| --- | --- |
| GramCoordinateBound | `fc5331ed502b7c9a88d8a39b6ef26a9dd25287c7df6a1d9dfea8ab930029fb30` |
| CovariantTensorNorm | `8fc8d169fe6f93bb240320d0a812a998f460faf30010472d2900773a379d11c5` |
| LocalAeBound | `c476e9bfa21c70e2de25e481e7a1cae9e500ca62252b537cd6f93bee5742f377` |
| AuxiliaryConnection | `bc03caba07537d7eb3bacd8f33745c6960f87702fcfac8c091f7648ea8fd7c03` |
| ConnectionErrorLInfinity | `3cb29cb03d065f2efc78b28826a718949d53ebf0781288c40fac92854b4d4879` |
| AuxiliaryPhysicalBound | `5176a7f60be7dfa9330add3f3482cbf1f6513d20b046213c99d799b975beebe4` |
| PositiveDensity | `e5351bf15f410fae8c48956b6865f76ce5211116268c1aa60d1af1ef991033a9` |
| RiemannianVolume | `fd320129665fa02199de13fb259bc12e0c481335bb6ddbbeaa7abe5db5347645` |

完整227目标/74源候选、实际合并候选CI和工件核对另外执行；旧200目标的绿色状态不作为新候选证据。

提交前将两份新源的CRLF统一为仓库规定的LF，实际归一化字节完全相同，数学解释据此继承；这19条声明在当前LF源下又全部实际核签。上表与源码绑定采用新LF回执，旧报告和首次227/74回执保留历史身份，完整候选另按最终LF输入重跑，不回写旧证据。
