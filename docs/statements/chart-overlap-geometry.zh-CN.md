# F05 首选坐标图重叠域的几何估计

[English](chart-overlap-geometry.en.md)

原文第 392–428 行用几何体积定义局部缺陷配对，并比较同一张量在不同坐标图中的表示。以下八项支持结论涉及一个给定度量场、两个首选坐标图及其过渡映射的 Jacobian。

- `geometricMeasure_chartSource_inner_eq_halfDensity` — 对光滑度量场，在图的源上按几何体积积分两个复标量场的内积。若该内积几乎处处强可测，则此 Bochner 积分等于目标坐标域的 Lebesgue 积分，其中两个因子都先拉回坐标域并各乘一次图半密度。在应用中判定积分有限还需要可积性。

- `coordinateMeasure_restrict_L2_inner_eq_halfDensity` — 在图像的可测子集上，若两个代表元都属于几何体积的 L²，并且相应的两个半密度加权代表元都属于 Lebesgue L²，则两种 Hilbert 空间的内积相等。

- `coordinateMeasure_memLp_two_iff_halfDensity` — 对光滑非退化度量和图像可测子集上的任意复值代表元，按几何体积平方可积等价于乘以半密度后按 Lebesgue 体积平方可积。因此在上一项内积恒等式中，两个几何 L² 条件便推出两个加权 L² 条件。

- `chartHalfDensity_transition` — 对两个首选图之间的过渡 Φ，源图的半密度在 x 处等于 √|det DΦ(x)| 乘以目标图在 Φ(x) 处的半密度。行列式的绝对值也涵盖反转定向的过渡。

- `overlapKernel_geometry_bounds` — 在光滑图重叠域的紧凸子集上，给定光滑非退化度量场，DΦ 和 Jacobian 平方根权重均为 Lipschitz，权重有界，DΦ 对向量长度有统一正下界。这些界给出一个正半径，在此半径内 DΦ 的变化量至多为该下界的一半。

- `overlapFar_uniform_arguments` — 在图重叠域的紧子集上，若 |x−y| 大于等于某个固定正数，则 |Φ(x)−Φ(y)| 和 |DΦ(x)(x−y)| 同时具有统一正下界。

- `exists_transportOverlapCutoff` — 闭支撑包含于源重叠域的实光滑紧支撑截断函数，在目标图中有实光滑紧支撑代表。沿 Φ 拉回后在整个重叠域上等于原截断，其目标支撑包含于原闭支撑的像。

- `exists_countable_chartTransition_windows` — 给定每一点的源、目标邻域，可逐点选择正半径并选取可数个中心。这些中心处半径减半的源开球覆盖整个重叠域。所有闭球都位于指定邻域和坐标域内，Φ 将每个源闭球映入相应目标开球。

要得到原文的坐标协变性，还需证明共轭算子的低阶误差在二次极限中消失，并在同一子序列上识别全部有序协方差分量。

两位独立复核者分工回读了自己未参与编写的证明，并用锁定依赖重编。四个模块的 31 项公共声明已逐项核对实际类型和传递公理，八项支持结论进入工程的常规检查。 [源码与原文位置](chart-overlap-geometry-source-bindings.json)
