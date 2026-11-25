# Globally hyperbolic full momentum lift

The input to `lem:lift` at lines 2989–2991 is the original cosphere measure with the Einstein moment and Hamilton transport equations. The ambient result constructs a Radon measure on the punctured null cotangent bundle, preserves the exact second moment over each compact base set, and gives the Einstein moment equation for the original smooth compactly supported symmetric test tensors and the transport equation for every compactly supported smooth full cotangent test. A smooth timelike field specifies the time orientation. Compact causal diamonds and local no causal return use intrinsic finite piecewise \(C^1\) curves with their one-sided derivatives at segment endpoints. The library provides the closed future cone and strictly regular piecewise versions.

A continuous volume time gives a smooth, positive, degree-one affine pulse first integral. Its reciprocal defines a flow-invariant section. The radial weight preserves the second moment. The open-subspacetime version restricts the same ambient cosphere measure, preserves the original equations and applies the full momentum lift to that restriction.

The two ambient entries and the two open-region entries passed joint Lean replay on the pinned source and manuscript using only `propext`, `Classical.choice` and `Quot.sound`. See the [source and receipt bindings](globally-hyperbolic-momentum-lift-source-bindings.json). Author semantic confirmation remains pending. Applying the lift in the main theorem still requires the original cosphere transport equation from the vacuum sequence.

| Paper slice | Lean declaration |
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
