# Weighted change of auxiliary unit section

The proof concerns `eq:norm-change` in lines 481–485 of the locked paper. On the original unit cosphere for the auxiliary metric $r$, write $s_0(x,\xi)=|\xi|_{r'}$ and $F_0(x,\xi)=(x,\xi/s_0)$. The base point is preserved. Both auxiliary metrics use the same strict refinement of the original vacuum sequence, the same chart cutoffs, and the same local matrix-measure witnesses. The two physical measures are the contractions of their respective original intrinsic amplitude covariances.

The change of trace control uses the weight $s_0^2t$, where $t$ is the trace of the old covariance in the new metric. Pulling the new density back to the same base fiber gives $t^{-1}$ times the old density almost everywhere. The factors of $t$ cancel. For every real-linear, complex-valued test of the amplitude fiber that is integrable against the contracted density, the corresponding complex measures satisfy the weighted pushforward on all Borel sets. The test may depend on the entire new cosphere point. The physical measures satisfy $\mu'=F_{0*}(s_0^2\mu)$.

The shared-witness construction uses a nonempty base and retains all locally represented classical pairings in either auxiliary metric. These four supporting theorems cover the change-of-section proof. The complete quadratic theorem and the transport theorem have separate scope entries. The supporting results have passed independent mathematical review and native replay. Author confirmation is pending.

## Registered declarations

- `Burnett.Microlocal.Overlap.cotangentAuxiliaryWeight_eq_ofReal_norm_sq_on_cosphere`
- `Burnett.Microlocal.Overlap.hasIntrinsicAmplitudeWeightedPushforward_of_traceChange`
- `Burnett.Microlocal.Overlap.intrinsicAmplitude_testMeasure_changeAuxiliary`
- `Burnett.Microlocal.Overlap.exists_originalVacuum_sameWitnesses_intrinsicAmplitude_weightedPushforward`

[Source bindings](weighted-auxiliary-section-change-source-bindings.json)
