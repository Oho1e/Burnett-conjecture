# Lipschitz commutator estimate in a symmetric energy pairing

[中文](lipschitz-commutator-energy.zh-CN.md)

The locked manuscript states `lem:commutator` at lines 566–575. `Burnett.Analysis.CarlesonEmbedding.originalRadianScalarLipschitzEnergy` proves the estimate for smooth real scalar coefficients $r^{ab}=r^{ba}$. The fixed first-order matrix pseudodifferential operator $B$ is properly supported and formally self-adjoint, with a full left symbol in the global smooth class $S^1_{1,0}$. For compactly supported smooth vector fields $u$ and coefficients with finite $W^{1,\infty}$ norm, the estimate is

$$
\bigl|2\operatorname{Im}\langle r^{ab}\partial_a\partial_b u, Bu\rangle\bigr|
\leq C_B\|r\|_{W^{1,\infty}}\|u\|_{H^1}^2.
$$

The constant is chosen before the coefficients and test fields. The right-hand side uses only the componentwise essential bounds on coefficient values and first derivatives and the inhomogeneous coordinate $H^1$ norm of the field. `Burnett.Analysis.CarlesonEmbedding.originalRadianHermitianLipschitzEnergy` implements the Hermitian matrix coefficient version at lines 573–574. It uses $(R^{ab})^*=R^{ba}$ and the same scalar full symbol of $B$ on every field component.

`HormanderOrderOne` expresses the general $S^1_{1,0}$ class in terms of mixed Fréchet derivatives. The full left action equals the left-symbol integral in the manuscript's Fourier convention at lines 539–544 pointwise, with forward phase $e^{-ix\cdot\xi}$, inverse phase $e^{ix\cdot\xi}$, and inverse factor $(2\pi)^{-4}$. The two results use Lebesgue pairings. The fixed-chart density step at line 591 has its own cutoff and symmetry interface.

The native replay compiled the two exact source modules and checked 11 declarations. The two registered targets depend on `propext`, `Classical.choice`, and `Quot.sound`. Independent readback checked the quantifiers, symbol class, pairing, normalization, and Hermitian condition against the manuscript from the actual types and definitions. Author confirmation is pending. [Locked inputs and verification records](lipschitz-commutator-energy-source-bindings.json)
