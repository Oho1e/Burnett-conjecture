# 原文索引与陈述入口

[English](README.en.md)

下文保留初始清点时的状态。当前进度见[范围清单](../formalization/scope.json)与[复核记录](../formalization/review.md)。

锁定原文：`paper/burnett.tex`，SHA256 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`。行号为该源文件的1起算行号，不是PDF页码。

初始索引定位17个正式结果环境（3 theorem、6 lemma、6 proposition、2 corollary），并登记33项未编号结果候选、15项定义候选。现已实现实非特征消去、完整实B展开、实零锥核/B公式及实规范交叉；一般极化、复Hermitian与商正性仍开放；17项正式结果仍待完成，父依赖仍仅部分形式化。候选范围及必要依赖闭包继续核对。环境编号按TeX计数器推得，尚未经编译PDF核验。

- [逐项原文陈述与未来Lean对照](main.md)
- [机器可读完整索引](source-index.json)
- [初始结构清点及候选说明](intake.zh-CN.md)
- [主定理的精确接口](main-interface.md)
- [角向 Fourier 交换子与固定低频正则化](angular-cutoff-commutator.zh-CN.md)
- [正矩阵值测度表示](positive-matrix-measure.zh-CN.md)
- [首个 Ricci 符号片段](ricci-symbol.md)及[独立实际声明回读](ricci-symbol-review.md)
- [线性化 Ricci 的局部强 H⁻¹ 收敛](geometric-Hminus-closure.md)及[独立复核](geometric-Hminus-closure-review.md)
- [内禀曲率、Ricci 迹与图内真空](intrinsic-curvature-Ricci.md)及[独立复核](intrinsic-curvature-Ricci-review.md)
- [有限维变分与 Ward 恒等式](transport-ward.md)及[独立复核](transport-ward-review.md)
- [多尺度 Rosen 真空序列](rosen-multiscale.md)及[数学复核](rosen-multiscale-review.md)
- [一般双极化 Rosen 命题](rosen-two-polarization.md)及[数学复核](rosen-two-polarization-review.md)
- [局部加权分解与基底测度试验](local-disintegration.zh-CN.md)
- [固定联合测度的可数覆盖测度分解](countable-fiber-disintegration.zh-CN.md)
- [F05 首选坐标图重叠域的几何估计](chart-overlap-geometry.zh-CN.md)
- [辅助度量变换下的真空序列假设](auxiliary-metric-admissibility.zh-CN.md)
- [三次能量交换子的 Fourier 符号](cubic-energy-fourier-symbols.zh-CN.md)
- [四维极大函数与环带平方估计](harmonic-maximal-and-square-estimates.zh-CN.md)
- [条件角核的变换](angular-kernel-transforms.zh-CN.md)
- [四维移位 Fourier 窗估计](shifted-fourier-window-estimates.zh-CN.md)
- [双侧空间截断的紧 Fourier 乘子](compact-frequency-localization.zh-CN.md)
- 主范围及进度仅在 `../formalization/scope.json` 维护；本目录保留来源与对应材料。

| 原文预计编号 | 类型 | 标签 | 源码行 | Lean状态 |
| --- | --- | --- | --- | --- |
| 1.1 | theorem | `thm:main` | 139–168 | 未建模 |
| 2.1 | theorem | `thm:quadratic` | 354–356 | 未建模 |
| 2.2 | corollary | `cor:base-marginal` | 487–506 | 未建模 |
| 3.1 | lemma | `lem:commutator` | 566–575 | 未建模 |
| 3.2 | lemma | `lem:cubic-continuity` | 613–623 | 未建模 |
| 3.3 | lemma | `lem:freezing` | 736–764 | 未建模 |
| 3.4 | lemma | `lem:analytic-near` | 1026–1057 | 未建模 |
| 3.5 | lemma | `lem:analytic-correction-bounds` | 1380–1394 | 未建模 |
| 4.1 | proposition | `prop:general-projection` | 1600–1616 | 未建模 |
| 5.1 | theorem | `thm:variational-transport` | 1729–1735 | 未建模 |
| 6.1 | lemma | `lem:lift` | 2989–2991 | 未建模 |
| 6.2 | corollary | `cor:strong` | 3063–3078 | 未建模 |
| A.1 | proposition | `prop:shear` | 3121–3123 | [证明与独立复核](harmonic-shear.zh-CN.md) |
| B.1 | proposition | `prop:cubic` | 3175–3181 | 未建模 |
| C.1 | proposition | `prop:bianchi` | 3245–3247 | [证明与独立复核](bianchi-counterexample.zh-CN.md) |
| D.1 | proposition | `prop:rosen` | 3307–3312 | [证明与独立复核](rosen-two-polarization.md) |
| D.2 | proposition | `prop:flat-rigidity` | 3390–3392 | [证明与独立复核](flat-rigidity.zh-CN.md) |
