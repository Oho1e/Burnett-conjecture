# Projected vacuum remainder and whole-space divergence source

[简体中文](projected-vacuum-source.zh-CN.md)

This delivery covers manuscript lines 1602–1612, 1644–1672, and 1685–1695. Fix a smooth compactly supported cutoff $\chi$, extend $z_n=\chi(g_n-g_0)$ by zero, and set $u_n=\Pi z_n$ for the existing fixed matrix Fourier projection $\Pi$.

The coordinate Ricci identity separates the principal wave term from the symmetric gradient of the lowered gauge covector. After applying the vacuum equation and moving $\chi$ inside the gradient by the product rule, the wave source $Q_Az_n$ is the sum of a compactly supported symmetric gradient and a local remainder. The projection annihilates that gradient, so the local remainder controls $\|\Pi Q_Az_n\|_{L^2}$. The uniform remainder estimate uses first-order metric and inverse-metric data, second-order data of the smooth background, and the fixed cutoff.

The whole-space negative divergence has an actual $L^2$ representative. With $Q_A=\sum_{a,b}A^{ab}\partial_{ab}$ it satisfies

$$
-\sum_{a,b}\partial_a(A^{ab}\partial_bu_n)
=-\Pi Q_Az_n+\sum_{a,b}[\Pi,A^{ab}]\partial_{ab}z_n
-\sum_{a,b}(\partial_aA^{ab})\partial_bu_n .
$$

The middle term uses the matrix commutator estimate for the same $\Pi$. The estimates cover the entire $\mathbb R^4$, including the projection tails outside $\operatorname{supp}\chi$. The matrix norm is the maximum of the component $L^2$ norms.

The open-chart theorem accepts actual coordinate components and coordinate vacuum. The intrinsic theorem obtains these data from the original smooth vacuum sequence in a standard $\mathrm{chartAt}$ chart. The final result first fixes one $z_n$ so that the same $u_n$ has finite-$L^p$ gradient bounds and tends to zero in $L^p$ and $L^\infty$. For a common Lipschitz bound $L$ it then gives one $C\ge 0$ for the whole-space negative divergence over all smooth extension families and all $n$. Each extension agrees with the true coordinate inverse metric in a neighborhood of $\operatorname{tsupp}\chi$. Only the first-order Lipschitz bound of the extensions enters the estimate.

The intrinsic transfer to arbitrary compatible smooth charts and identification of the original sequence's full angular measure remain to be connected. Author confirmation is pending.

- `Burnett.P01.twice_coordinateRicci_eq_wave_symmetrizedGauge_remainder`
- `Burnett.P01.localizedVacuumSource_eq_symmetrizedGauge_add_remainder`
- `Burnett.P01.exists_localizedVacuumSourceRemainder_majorant`
- `Burnett.P01.exists_norm_projection_of_localizedVacuumSource_le`
- `Burnett.P01.projectedSourceDivergenceL2_ae`
- `Burnett.P01.projectedSourceDivergenceL2_eq_projected`
- `Burnett.P01.exists_projectedSourceDivergenceL2_bound`
- `Burnett.P01.projectedSourceQ_eq_localizedWaveSourceSchwartz`
- `Burnett.P01.exists_wholeSpace_projectedVacuumDivergenceL2_bound`
- `Burnett.P01.exists_projectedVacuumDivergenceL2_of_openChart`
- `Burnett.P01.exists_projectedVacuumDivergenceL2_of_intrinsic`
- `Burnett.P01.projectedSource_uniform_extension_bound`
- `Burnett.P01.exists_intrinsicChartProjectedField_norms_and_uniform_source`

[Shared source bindings](projected-vacuum-source-source-bindings.json)
