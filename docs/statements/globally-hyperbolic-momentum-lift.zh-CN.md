# 全局双曲时空的全动量提升

论文 `lem:lift` 第 2989–2991 行从同一余球面测度及其 Einstein 矩和 Hamilton 输运方程出发。全流形入口直接在原时空上构造零余切 Radon 测度，保留每个紧底集上的确切二次矩，得到原 Einstein 矩等式和对所有光滑紧支撑全余切测试的输运等式。时向以光滑类时场表示。紧因果菱形和局部无因果返回使用内禀有限分段 \(C^1\) 曲线，并保留闭段端点的单侧导数。库给出闭未来锥和严格正则分段两种入口。

证明以连续体积时间构造光滑、正、一次齐次的仿射脉冲第一积分，再使用它的倒数构造流不变截面。径向权重保持二次矩。开子时空版本限制同一个环境余球面测度，保留两条原方程并对限制测度实施全动量提升。

两个全流形入口和两个区域入口已经按固定源码与原论文联合通过 Lean 核验，公理使用限于 `propext`、`Classical.choice`、`Quot.sound`。见 [源码与回执绑定](globally-hyperbolic-momentum-lift-source-bindings.json)。作者语义确认待记录。应用到主定理时需要先由真空序列证明原余球面输运方程。

| 论文切片 | Lean 声明 |
| --- | --- |
| `L01` | `Burnett.Geometry.CausalOrbitPulse.exists_fullMomentumEinsteinLift_of_regularIntrinsicPiecewise` |
| `L01` | `Burnett.Geometry.CausalOrbitPulse.exists_fullMomentumEinsteinLift_of_intrinsicPiecewise` |
| `L01` | `Burnett.Geometry.CausalOrbitPulse.exists_completeNullTime_of_chartGlobalHyperbolicity` |
| `L01` | `Burnett.Geometry.CausalOrbitPulse.exists_smooth_canonicalPulseFirstIntegral` |
| `L01` | `Burnett.Geometry.CausalOrbitPulse.exists_actualFullMomentumLift_of_completeNullTime` |
| `L01` | `Burnett.Geometry.FiniteCausalVolume.chartCausalRelation_eq_intrinsicPiecewiseCausalRelation` |
| `L01` | `Burnett.Geometry.FiniteCausalVolume.chartGlobalHyperbolicity_iff_intrinsicPiecewise` |
| `L01` | `Burnett.Geometry.FiniteCausalVolume.chartCausalRelation_eq_regularIntrinsicPiecewiseCausalRelation_of_compactDiamonds` |
| `L02` | `Burnett.Geometry.OpenRegion.hasCosphereEinsteinMoments_openSubtype` |
| `L02` | `Burnett.Geometry.OpenRegion.unitNullMeasureOfOpen_transport` |
| `L02` | `Burnett.Geometry.OpenRegion.exists_openRegionEinsteinLift_of_intrinsicPiecewise` |
| `L02` | `Burnett.Geometry.OpenRegion.exists_openRegionEinsteinLift_of_regularIntrinsicPiecewise` |
