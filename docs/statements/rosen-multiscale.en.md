# The multiscale Rosen vacuum sequence

[简体中文](rosen-multiscale.md) · [Locked manuscript](../../paper/burnett.tex#L3360)

The Lean sequence starts at index zero and uses the positive frequency parameter $a_n=n+1$, with fast frequency $e^{a_n}$. The local ODE has the manuscript's initial values $B_n(0)=1$ and $B'_n(0)=0$. Its coefficient $(\psi_n')^2$ has a uniform $L^\infty$ bound on $I=(-1/4,1/4)$, and the pairing against every real $L^1(I)$ test converges to that of the constant $1$. The same smooth solutions satisfy $B_n\geq\cos(2u)>0$ and uniform first and second derivative bounds. On the closed interval, $B_n\to\cos u$ and $B'_n\to-\sin u$ uniformly, by a direct estimate on the oscillatory primitive.

| Manuscript lines | Actual Lean objects |
| --- | --- |
| 3360–3367 | `phase`, `rosen_phase_LInfinity_weakStar`, and `exists_smooth_rosen_sequence_c1`. |
| 3367–3371 | `exists_rosen_multiscale_vacuum_geometry` uses the same $B_n$ in the actual Ricci equations of the original and pulled metrics. Both limits have Ricci tensor $2\,du^2$. |
| 3373–3374 | `rosen_full_metric_essential_lower_bounds` gives the bounds $\cos^2(1/2)/(2a_n)$ and $2e^{-4}\cos^2(1/2)e^{a_n}-42e^4$ on the essential suprema of the full metric error and the full second-coordinate-derivative array on the four-dimensional product box. `rosen_no_common_full_metric_scale` excludes a common scale. |
| 3376–3386 | `rosenCoordinates_inverses_on_slab`, `rosenCoordinates_smooth_on_slab`, `pulledRosenField_eq_jacobian_pullback`, and `pulledRosen_contractedSource_zero`. The coordinate map is $v=B_n(u)V$. The contracted sources use the divergence of the volume-weighted inverse metric. |
| 3371, 3386 | `rosen_full_kinetic_limit` uses the positive Radon graph measure at $du$ with weight twice the actual volume density. `Transport.BaseTestClass.intrinsic_tensor_einstein_moment` gives the second-moment identity for intrinsic smooth compactly supported tensor tests on the base. `Transport.TestClass.intrinsic_compact_test_transport` gives full Hamiltonian transport for intrinsic smooth compactly supported tests on the punctured phase domain. Both identities use the same measure in each chart. |
| 3385–3386 | `RosenMultiscaleSequence.euclideanDh_eLpNorm_on_compact` uses the same $B_n$ and the actual covariant derivative of $g_n-g$ relative to the fixed Euclidean auxiliary metric in each chart. It bounds the essential supremum of the Hilbert norm of the derivative on every compact subset of the open slab, uniformly in $n$. |

The original metrics converge uniformly on the slab $u\in[-1/4,1/4]$. The pulled metrics converge uniformly on every fixed bounded $V$ region of that slab, with uniform first coordinate derivative bounds there. Both coordinate fields are smooth on their domain and have one negative and three positive Lorentz directions, with a smooth timelike direction.

`Burnett.RosenMultiscale.rosen_multiscale_full_example` assembles the sequence and both kinetic identities. The curvature and transport of this example are proved directly in fixed product coordinates. The general Rosen proposition `prop:rosen` and the main transport theorem remain separate obligations.
