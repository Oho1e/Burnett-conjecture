# Base marginal and angular disintegration

`Burnett.F08.IntrinsicBaseMarginal.baseMarginal_and_angularDisintegration` proves `cor:base-marginal` from lines 487–506 of the locked manuscript. Let $B$ be the smooth Lorentzian background, $r$ the auxiliary Riemannian metric, and $(g_n)$ the smooth vacuum sequence under the manuscript's admissibility assumptions. The input quadratic measure $\mu$ is fixed, has finite mass above compact base sets, is concentrated on the null cone, and has the original Einstein second moments. The background scalar curvature vanishes everywhere.

Write $e_r=\operatorname{tr}_r G(B)$. It is smooth and nonnegative everywhere, with

$$
\pi_*\mu=e_r\,\mathrm dV_B.
$$

`UnitNullFiber` is the dependent fiber of the same auxiliary unit cosphere. Its elements have base point $x$ and zero Hamiltonian. `UnitNullFiberMeasures` gives nonnegative fiber measures $\mu_x$ that are finite almost everywhere and whose pushforwards under the actual fiber inclusions form a measurable family. `reconstructs_apply` gives, for every Borel set $S$,

$$
\mu(S)=\int_M \mu_x(\iota_x^{-1}(S))\,\mathrm dV_B(x).
$$

On one set of full geometric volume, the mass of $\mu_x$ is $e_r(x)$ and the integrable moment identity holds for every $u,v\in T_xM$,

$$
G(B)_x(u,v)=\int \xi(u)\xi(v)\,\mathrm d\mu_x(\xi).
$$

The fiber measure is zero almost everywhere where $e_r=0$. Any two measurable fiber families reconstructing the fixed $\mu$ over background volume agree almost everywhere. The base marginal is absolutely continuous with respect to background volume, and $\mu$ vanishes above every open vacuum region.

## Mathematical and verification interfaces

The entry derives symmetry of the Einstein tensor from the original vacuum sequence and uses the existing total-space angular kernel and the simultaneous moments. Measurability of the fiber graph makes the restricted kernel a measurable family. Pulling back under the actual fiber inclusions and pushing forward again recovers the original kernel almost everywhere. The same joint graph measure yields uniqueness on the actual dependent fibers.

The native production replay checks the statements through the new `Burnett` library entry. Separate probes compare the frozen independent statement and apply the entry to the same refinement, amplitude and $\mu$ from the original quadratic construction. Author confirmation is pending and the paper status is `development`.
