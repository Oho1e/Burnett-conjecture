# The two-polarization Rosen proposition

[简体中文](rosen-two-polarization.md) · [Locked manuscript](../../paper/burnett.tex#L3305)

`Burnett.RosenPlaneWave.two_polarization_rosen_closure` formalizes `prop:rosen` at manuscript lines 3305–3359. The coordinate domain is the product of an open subset of the real $u$ axis and $\mathbb R^3$, covering the open interval used for the smooth product spacetime. The screen $\gamma$ is a real symmetric positive definite $2\times2$ matrix. The proof allows an off-diagonal polarization and uses local bounds on first derivatives.

| Source lines | Lean correspondence |
| --- | --- |
| 3307–3312 | `ScreenPhysicalSequence` gives the smooth positive definite screen fields, the vacuum Ricci equations, and local convergence and the covariant first-derivative bound in an arbitrary positive auxiliary metric. `screen_local_controls_of_physical_admissible` derives pointwise screen derivative bounds for the entire sequence on each compact $u$ set. |
| 3313–3324 | `screenBilinear_computedConnection` and `screenBilinear_coordinateRicci` differentiate the bilinear metric in the fixed product coordinates. They give $L=\gamma^{-1}\gamma'/2$, $\tau=\operatorname{tr} L$, and $-\tau'-\operatorname{tr}(L^2)$ in the $uu$ Ricci component. |
| 3325–3342 | `screenShear` uses the positive inverse square root to define $S=\gamma^{-1/2}\gamma'\gamma^{-1/2}/2$. On each compact subinterval, the normalized shears $S_n$ converge weak-star to $S$ entrywise against every real $L^1$ test, and $\sum_{A,B}(S_n)_{AB}^2$ converges weak-star to $-\tau'$. The vacuum trace equation and local weak lower semicontinuity give the smooth nonnegative density $\rho=-\tau'-\sum_{A,B} S_{AB}^2$. |
| 3343–3358 | `screenHamilton_canonical_du` uses the inverse metric and the canonical half-quadratic Hamiltonian. At $du$ the base derivative of $P$ vanishes and $H_P=-\partial_v$. The witness uses the weight $\rho\sqrt{\det\gamma}$ relative to coordinate Lebesgue measure and is concentrated at $du$. |

The single witness is `phaseMeasure I (screenKineticWeight γ)`. Its carrier is closed relative to the punctured phase domain and lies in the null set. The Einstein identity pairs all tensor components with the actual Einstein tensor and the actual metric volume density. The two Bochner integrals are defined for intrinsic smooth compactly supported base tensor tests. Full phase-space transport is proved for every intrinsic smooth compactly supported scalar test. Both use this same measure. The squared cotangent length for any continuous positive definite auxiliary metric is integrable over the inverse image of each compact base set.

The result allows the zero measure when the density vanishes. The explicit nonzero multiscale example is X06. The general proof uses the product coordinates and ordinary integration in $v$.
