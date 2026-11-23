# Vacuum Ricci kernel and auxiliary unit cosphere amplitudes

Lines 412–428 of the locked paper use a first-order Ricci constraint on the range of the gradient-defect amplitude. Lines 1703–1709 apply that constraint to the fixed gauge-complement projection. This batch derives their local forms in the preferred charts from the original vacuum sequence and constructs the corresponding amplitude component measures on the actual auxiliary unit cosphere.

Fix a smooth auxiliary Riemannian metric $r$, a smooth symmetric nondegenerate background $B$, and a smooth symmetric nondegenerate intrinsic vacuum sequence $g_n$. Assume local uniform convergence to $B$ in the $r$ norm and a uniform essential bound on the covariant derivative difference on each compact set with background volume. Each prescribed preferred chart has a closed coordinate ball $K$ contained in the chart and a smooth real cutoff supported in the ball. Every strict subsequence has a common strict refinement on which the original volume-weighted gradient pairings and the actual fixed projected derivative pairings use the same trace $\tau$ in each chart.

## Vacuum Ricci kernel and projection

Apply Bessel regularization to the coordinate Ricci principal rows obtained from intrinsic vacuum with the same cutoff and background inverse metric. The rows tend strongly to zero in complex $L^2$. Their angular principal coefficient gives the Ricci row constraint on the original trace density. Write $G=B^{-1}$, let $\xi$ be the round covector, and let $A$ be the round amplitude of that covariance. On one trace-conull set, $A\succeq0$ and $Av$ is symmetric and satisfies $\mathcal R_{G,\xi}(Av)=0$ for every complex ordered two-index vector $v$.

The fixed gauge-complement symbol $P(\xi)$ compresses the same amplitude to $PAP^*$. This projected amplitude is positive semidefinite, vanishes where $G^{ab}\xi_a\xi_b\ne0$, and obeys the Lorenz contraction $q_b=\xi_b t/2$ on the null cone. Applying null-shell restriction and the same quarter physical contraction to the original and projected amplitudes gives equal measures on $K\times S^3$, with equality on every Borel event.

## Actual auxiliary unit cosphere

Let $s_r(x,\xi)=\sqrt{r^{ab}(x)\xi_a\xi_b}>0$. The preferred cotangent trivialization assembles $(x,\xi/s_r)$ to a covector $F_r(x,\xi)$ in the actual cotangent bundle. Its $r$ dual energy is $1$. On the same trace the auxiliary unit amplitude is $S_r=s_r^2 A$, and the two derivative factors are $(\xi/s_r)_\alpha(\xi/s_r)_\beta$. The range of $S_r$ satisfies the Ricci constraint at that unit direction.

For every Borel set $E$ of the cotangent bundle, the ordered covariance components are

$$
\Sigma^K_{r,ij}(E)=\int_{F_r^{-1}(E)}s_r(x,\xi)^2 A_{ij}(x,\xi)\,d\tau .
$$

The components give a positive semidefinite matrix on each Borel set and the component measures are concentrated on the auxiliary unit cosphere. The construction uses the same refinement as the original and projected pairings, with their trace in each preferred chart. Coordinate covariance, cutoff compatibility on overlaps, global gluing, and the moment identity of the original theorem remain to be proved.

## Registered declarations

- `Burnett.Microlocal.RicciRemainder.chartRicciPrincipal_tendsto_zero_of_intrinsicVacuum`
- `Burnett.Microlocal.RicciRow.roundBesselCoefficient_eq_ricciJetMatrix_of_cutoff_eq_one`
- `Burnett.Microlocal.CurlDensity.factoredAmplitude_in_complexRicciKernel`
- `Burnett.F05.ActualCoordinateRicciDensity.ae_originalVolume_ricciRows_same_density`
- `Burnett.F05.ActualCoordinateRicciDensity.ae_originalVolume_roundAmplitude_in_ricciKernel`
- `Burnett.F05.ActualCoordinateRicciDensity.exists_countable_originalVolume_RicciKernel_projected_pairings`
- `Burnett.F05.ActualChartAuxiliarySection.chartAuxiliaryRay_unit`
- `Burnett.F05.OriginalVolumeAuxiliaryAmplitude.ae_originalVolume_auxiliaryAmplitude`
- `Burnett.F05.ChartCotangentAmplitudeMeasure.cotangentAmplitudeMeasure_apply_round`
- `Burnett.F05.ChartCotangentAmplitudeMeasure.cotangentAmplitudeMeasure_positive`
- `Burnett.F05.ChartCotangentAmplitudeMeasure.cotangentAmplitudeMeasure_zero_off_unit`
- `Burnett.F05.ChartCotangentAmplitudeMeasure.exists_countable_originalVolume_cotangentAmplitudes`
- `Burnett.P01.ae_originalVolume_projectedCovariance_ricciPolarization`
- `Burnett.P01.originalVolume_roundNullMeasure_projected_eq`

[Shared source bindings](original-volume-ricci-amplitudes-source-bindings.json)
