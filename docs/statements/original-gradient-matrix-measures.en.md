# Local positive matrix measures for the original metric gradients

The F05 construction in lines 390–429 of the locked paper uses one subsequence for the microlocal defect. This batch proves the local measure construction needed in lines 398–407 for the actual coordinate gradients weighted by the fixed volume half-density.

## Original sequence, cutoffs, and subsequence

Let the smooth metrics $g_n$ converge locally uniformly to a smooth nondegenerate background $B$. Assume the differences have a uniform essential bound for their auxiliary covariant gradients on each compact set, with respect to the volume measure of $B$. In each prescribed preferred chart fix a coordinate closed ball $K$ contained in the chart target and a real smooth cutoff $\chi$ supported in $K$. The derivative axis and ordered tensor indices form a slot $i=(\alpha,a,b)$. The actual Lebesgue $L^2$ input is

$$
w_{n,i}=|\det B|^{1/4}\chi\,\partial_\alpha(g_n-B)_{ab}.
$$

For any prescribed countable chart family and any strictly increasing subsequence $s$, a single strictly increasing $t$ gives the following representation in every chart along $s\circ t$. Taking $s=\mathrm{id}$ starts from the original sequence.

## Measures and finite separated pairings

Each chart has a family of positive, finite, regular compression measures on $K\times S^3$. Polarization gives the matrix entries, and the matrix is positive semidefinite on every Borel set. All entries are absolutely continuous with respect to one finite trace measure $\tau$. Its Radon–Nikodym matrix density $J$ is positive semidefinite and has trace one $\tau$-almost everywhere.

For every finite sum $T=\sum_m a_m(x)b_m(D)$, the complex-valued $a_m$ may be bounded and continuous, and the $b_m$ bounded, smooth away from zero, and homogeneous of degree zero under positive dilation. All such tests and all $64\times64$ ordered pairings use the same $s\circ t$ and satisfy

$$
\lim_{n\to\infty}\langle w_{s(t(n)),i},T w_{s(t(n)),j}\rangle_{L^2}
= \int_{K\times S^3}\bigl(\sum_m a_m(x)b_m(\omega)\bigr)J_{ij}(x,\omega)\,d\tau.
$$

The Lean inner product is linear in the second entry. In the covariance convention of the projected pairings in batch 56, the same integrand uses $N_{ji}$ with $N=J^{\mathsf T}$. The numerical-limit result realizes each of the previously selected rational angular limits by this integral on a common refinement. It retains the constant chosen in each chart before the spatial multiplier, and the original convergence before refinement. The integral identification uses continuous spatial multipliers.

The result covers the local separated tests above. The next use of the same density is to apply the coordinate curl and vacuum Ricci-kernel constraints, obtain the two derivative factors and metric amplitude, and establish compatibility on the auxiliary cospheres and chart overlaps.

## Registered declarations

- `Burnett.F05.OriginalCoordinateCurl.exists_originalGradient_sourceSchwartz_inputs`
- `Burnett.F05.ChartVolumeAmplitude.originalGradient_volumeWeightedL2_ae`
- `Burnett.Microlocal.CountableAuxiliaryCharts.exists_countable_originalVolume_rational_pairing_limits`
- `Burnett.Microlocal.CompactOrderedFunctional.exists_commonCompactMatrixFunctional_positive`
- `Burnett.Microlocal.CompactChartMatrixMeasure.exists_compactChartMatrixMeasure_of_localized_weak_zero`
- `Burnett.Microlocal.CompactChartDensity.exists_compactChartMatrixDensity_of_localized_weak_zero`
- `Burnett.Microlocal.FixedSubsequenceSeparableExtension.exists_compactChartMatrixDensity_allFiniteSmoothPairings`
- `Burnett.Microlocal.CountableAuxiliaryCharts.exists_countable_originalVolume_matrixDensities`
- `Burnett.Microlocal.CountableAuxiliaryCharts.exists_originalVolume_measures_realizing_rational_limits`

[Shared source bindings](original-gradient-matrix-measures-source-bindings.json)
