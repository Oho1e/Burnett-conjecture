# Assembly of the original gauge and far corrections

This batch formalizes supporting lemmas for V08, V11 and C02–C04. The two corrections use the same original projected field, spatial cutoffs and subsequence. The common wide screen is fixed before the thin screen is chosen. At fixed positive patch scale and thin-cone width, both actual Fourier pairings recover the angular expansion and upper frequency cutoff in the order used in the paper.

The original projected patch family supplies estimates for the thin-screen cubic replacement, thin-screen gradient difference and normalized phase gradient. The original gauge and physical far corrections use the projected source for that family. At fixed scale, summing the separate absolute values of the two Fourier integrals over the patches gives a bound proportional to the scale plus an arbitrary positive error on a tail of the same subsequence. The C04 fixed-scale limit uses the same patches and Fourier weights and includes each correction with its factor of 3 in the residual estimate.

The joint Lean replay covers 24 declarations and uses only `propext`, `Classical.choice` and `Quot.sound`. The source identities and paper ranges are in the [binding manifest](original-correction-assembly-source-bindings.json). Completing `thm:variational-transport` still requires the original variational residual limit, actual cubic localization and freezing, and the near and phase bounds. Author semantic confirmation remains pending.

| Paper slice | Lean declaration |
| --- | --- |
| `V08` | `Burnett.V11.originalGaugeTestedOperator_eq_orderedEntries` |
| `V11` | `Burnett.V10.OriginalGaugeCompatibility.exists_actualFar_cutoff_recovery` |
| `V11` | `Burnett.V11.exists_actualGauge_cutoff_recovery` |
| `V11` | `Burnett.V11.originalPatchSource_fullIdentity` |
| `V11` | `Burnett.V11.exists_actualCorrections_consume_sameProjectedPatch` |
| `V11` | `Burnett.V11.exists_intrinsicCorrection_jets_of_jointWideScreen` |
| `C02` | `Burnett.C02.exists_originalWideL3_cubicWindow_withJointScreen` |
| `C02` | `Burnett.C02.exists_uniform_originalThinCubicC03Replacement_withFixedJointScreen` |
| `C02` | `Burnett.V11.exists_uniform_originalFrequencyTest_jets` |
| `C02` | `Burnett.C02.exists_uniform_originalThinCubicC03Replacement_withFixedJointScreen_andGradientPair` |
| `C02` | `Burnett.C02.exists_originalThinCubicReceivingFamily_withFixedJointScreen_andGradientPair` |
| `C03` | `Burnett.V11.exists_receivingPatchFields_of_originalCutoffs` |
| `C03` | `Burnett.V11.originalCorrectionFourierSum_of_sharedBudget` |
| `C03` | `Burnett.V11.exists_originalCorrectionPatchFourierTail` |
| `C04` | `Burnett.C04.fixed_patch_summed_residual_bound_of_actualCorrectionSum` |
