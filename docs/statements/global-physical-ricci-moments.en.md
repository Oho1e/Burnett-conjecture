# Global physical measure and chart Ricci moments

This batch implements measure gluing, positivity, and the local moment identification in lines 467–479 of the locked `paper/burnett.tex`. The inputs are the original vacuum metrics, a smooth Lorentzian limit, locally uniform convergence, compact first-derivative bounds, and any given strict subsequence. The construction selects a single strict refinement. On a nonempty manifold the selected countable charts cover the base and retain representations of both the original derivatives and the fixed projected pairings along that refinement.

On a chart's nonzero cutoff locus, weight its finite positive physical measure by the reciprocal square of its original cutoff. Agreement on smaller common plateaus extends by countable exhaustion to the entire nonzero overlap. Positive cutoff thresholds give finite local bounds on every compact base set. The glued ambient cotangent measure is regular, finite over each compact base set, and carried by the actual auxiliary unit null shell. The measure on the auxiliary unit cosphere pushes forward along its inclusion to this ambient measure.

For a chart representing the original pairings along the selected subsequence, take a smooth compactly supported scalar test \(\psi\) supported on the nonzero locus of the original cutoff. The raw coordinate products and the weak Ricci limit use the same background volume and representation. The Ricci kernel cancels the contribution off the null shell and gives the quarter physical contraction on the null shell. Each chart component satisfies

$$
\int \psi(y)\,\operatorname{Ric}_{bd}(y)\,\mathrm dV_B(y)
  = \int_{\pi^{-1}U_q} \psi(y(p))\,\xi_b(p)\xi_d(p)\,\mathrm d\mu(p).
$$

Here \(U_q\) is the base nonzero cutoff locus and \(\xi\) is the actual auxiliary unit covector. Lean proves integrability on both sides. The right side uses the restriction of the same glued measure. The zero measure provides the existence and chart restriction statements on the empty base.

The quadratic theorem `thm:quadratic` still requires arbitrary global compactly supported tensor tests, pointwise scalar-flatness, the Einstein moment, global amplitude covariance, and the auxiliary-section change. The following declarations are registered as F07 supporting results.

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

[Shared source bindings](global-physical-ricci-moments-source-bindings.json)
