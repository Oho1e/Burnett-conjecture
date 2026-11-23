# Curl factorization and projected pairings of the original metric gradients

The argument in lines 412–428 of the locked paper applies the coordinate curl constraint and factors the defect into two derivative directions and a metric amplitude. This batch applies that step to the local matrix measure of batch 57 and obtains the preferred-chart mixed derivative pairings for the projection in lines 1703–1709.

Fix a smooth symmetric nondegenerate background $B$ and a smooth symmetric sequence $g_n$. Assume local uniform convergence to $B$ and uniform essential bounds on the auxiliary covariant gradients of the differences on each compact set. Each prescribed preferred chart uses a coordinate closed ball $K$ and a real smooth cutoff $\chi$ supported there. Write $J$ and $\tau$ for the density and finite trace measure of the volume-weighted raw derivative pairings on $K\times S^3$.

## Curl constraint on the same density

Use $N=J^{\mathsf T}$, with the Lean inner product complex-linear in the second slot. For a round unit covector $\xi$, set $E_\xi k=\xi\otimes k$. The strong vanishing of the angular Bessel curl rows of the actual gradients gives $\operatorname{curl}(\xi)N=0$. The symmetry of the original metric components also passes to $N$. Almost everywhere for the same $\tau$,

$$
A=E_\xi^* N E_\xi\succeq0,\qquad N=E_\xi A E_\xi^*,\qquad
J_{(\alpha,i),(\beta,j)}=\xi_\alpha\xi_\beta A_{ji}.
$$

The two factors and the positive semidefinite amplitude therefore represent all the existing finite separated pairings. Integrability of each weighted amplitude entry follows from the corresponding original trace density entry.

## Pairings of the actual projected field

For any prescribed countable chart family and any strict subsequence $s$, a single strict refinement $t$ gives both the raw and the projected pairings along $s\circ t$ with the same $\tau$ in each chart. The actual coordinate field $z_n=\chi(g_{s(t(n))}-B)$ is extended by zero. A smooth real compactly supported multiplier $d$ agrees with the background volume half-density on $\operatorname{tsupp}\chi$. The same fixed projection $\Pi$ has principal symbol $P(\xi)$.

Take a real smooth compactly supported spatial symbol $a$ and a bounded angular symbol $m$ that is smooth away from zero and homogeneous of degree zero under positive dilation. The pairing with left and right slots $d\,\partial_\alpha(\Pi z_n)_i$ and $d\,\partial_\beta(\Pi z_n)_j$ respectively tends to

$$
\int_{K\times S^3} a(x)m(\xi)\,\xi_\alpha\xi_\beta
   (P(\xi)A(x,\xi)P(\xi)^*)_{ji}\,d\tau.
$$

The declarations give mixed pairings on the round cosphere of the preferred chart. The actual vacuum Ricci-kernel constraint, passage to auxiliary metric cospheres, and cross-chart identification of the physical angular measure remain to be established.

## Registered declarations

- `Burnett.Microlocal.RowKernelDensity.rowPrincipal_density_kernel_of_strong_zero`
- `Burnett.Microlocal.CurlDensity.positive_factorCovariance_of_curl_compression`
- `Burnett.Microlocal.FixedChartGeometricDensity.ae_chartPhysicalCovariance_symmetry_of_same_pairings`
- `Burnett.F05.ActualCoordinateCurlDensity.ae_originalVolume_curlRows_same_density`
- `Burnett.F05.ActualCoordinateCurlDensity.ae_originalVolume_round_covariance_factor`
- `Burnett.F05.ActualCoordinateCurlDensity.originalVolume_pairing_tendsto_roundAmplitude`
- `Burnett.F05.ActualCoordinateCurlDensity.originalVolume_round_mixedPairing_witness`
- `Burnett.P01.representsVolumeProjectedPairings_of_matrixDensity`
- `Burnett.P01.exists_countable_originalVolume_projected_mixedPairings`

[Shared source bindings](original-volume-curl-amplitudes-source-bindings.json)
