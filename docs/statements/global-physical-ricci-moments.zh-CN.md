# 全局正物理测度与逐图 Ricci 矩

本批落实锁定原文 `paper/burnett.tex` 第 467–479 行的测度拼接、正性和局部矩识别。输入为原真空度量列、光滑 Lorentz 极限、局部一致收敛、紧集一阶导数界及任意给定的严格子列。构造选取一次严格细化。非空流形上的可数图族覆盖底流形，各图沿这同一子列保有原导数配对和固定投影配对的原表示。

在每张原图的截断非零域，将已经构造的有限正物理测度乘以该图原截断的倒数平方。较小的公共平台给出两侧相容性，再由可数平台穷尽推到整个非零重叠域。底集上的正阈值覆盖保证紧集上可有限次控制这一权重。拼接所得环境余切测度正则、在紧底集的原像上有限，并集中在由辅助度量指定的单位零壳。实际单位余球丛的测度沿包含映射推回这一环境测度。

对沿所选子列表示原配对的一张图，取紧支撑光滑标量测试 \(\psi\)，其支撑位于原截断的非零域。原坐标导数乘积与弱 Ricci 极限使用同一背景体积和同一表示。Ricci 核代数使离零壳的贡献为零，并在零壳上给出带 \(1/4\) 的物理缩并。该图的分量满足

$$
\int \psi(y)\,\operatorname{Ric}_{bd}(y)\,\mathrm dV_B(y)
  = \int_{\pi^{-1}U_q} \psi(y(p))\,\xi_b(p)\xi_d(p)\,\mathrm d\mu(p).
$$

这里 \(U_q\) 是底流形上的原截断非零域，\(\xi\) 是实际辅助单位余向量。Lean 给出等式两侧的可积性。右侧使用同一拼接测度的限制。空底流形的测度及图限制存在结论由零测度给出。

二次定理 `thm:quadratic` 仍待任意全局紧支撑张量测试、逐点标量曲率零、Einstein 矩、全局振幅协方差及辅助截面变化。下列声明登记为 F07 支持结果。

- `Burnett.Microlocal.CountableAuxiliaryCharts.exists_countable_compactChartInput_cover`
- `Burnett.Microlocal.Overlap.normalizedCotangentPhysicalMeasure_lt_top_of_cutoff_lower_bound`
- `Burnett.Microlocal.Overlap.normalizedCotangentPhysicalMeasure_compl_null`
- `Burnett.Microlocal.Overlap.isCompact_commonPatchBasePlateau`
- `Burnett.Microlocal.Overlap.map_comap_subtype_coe_restrict_withDensity`
- `Burnett.Microlocal.Overlap.originalVacuum_normalizedCotangentPhysicalMeasure_restrict_commonPatch`
- `Burnett.Microlocal.Overlap.originalVacuum_normalizedCotangentPhysicalMeasure_restrict_overlap`
- `Burnett.Microlocal.Overlap.exists_glued_originalVacuum_physicalMeasure`
- `Burnett.Microlocal.Overlap.exists_originalVacuum_globalPhysicalMeasure`
- `Burnett.Microlocal.Overlap.exists_originalVacuum_globalPhysicalMeasure_and_chartLaw`
- `Burnett.Geometry.UnitCosphere.map_fromAmbient_eq_of_unitNull`
- `Burnett.Geometry.UnitCosphere.fromAmbient_regular`
- `Burnett.Geometry.UnitCosphere.fromAmbient_finiteOnCompactBase`
- `Burnett.Geometry.UnitCosphere.fromAmbient_offNull`
- `Burnett.Microlocal.Overlap.exists_originalVacuum_physicalMeasure_on_cosphere`
- `Burnett.Analysis.PartialJetReplacement.vacuum_Ricci_raw_coordinateMeasure_limit_of_original`
- `Burnett.Microlocal.RawCovariance.rawJetCross_eq_jet_sum`
- `Burnett.Microlocal.Overlap.original_cutoff_products_of_represented`
- `Burnett.Microlocal.Overlap.original_products_of_represented_on_nonzero_cutoff`
- `Burnett.Microlocal.Overlap.original_Ricci_eq_normalized_jetContraction`
- `Burnett.Microlocal.RawCovariance.rawJetContraction_eq_nullMoment_of_factored`
- `Burnett.Microlocal.Overlap.original_chartRicci_eq_physical_secondMoment`
- `Burnett.Microlocal.Overlap.original_chartRicci_eq_cotangent_secondMoment`
- `Burnett.Microlocal.Overlap.exists_originalVacuum_globalPhysicalMeasure_and_representedChartMoments`
- `Burnett.Microlocal.Overlap.exists_originalVacuum_physicalMeasure_on_cosphere_and_representedChartMoments`

[共同源码对应](global-physical-ricci-moments-source-bindings.json)
