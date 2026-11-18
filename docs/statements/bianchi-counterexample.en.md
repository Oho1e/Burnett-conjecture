# X04 geometric nonrepresentability

[中文](bianchi-counterexample.zh-CN.md)

The declaration `Burnett.Bianchi.exists_bianchi_intrinsic_counterexample` corresponds to Proposition `prop:bianchi`, locked manuscript lines 3245–3247 and proof lines 3248–3301. For every $H>0$ the proof constructs one smooth metric on the open product $(-\tau,\tau)\times\mathbb R^3$ with $0<\tau<\pi/4$. The witness comes from the stated initial values and actual finite-dimensional system for $\gamma,A,\rho$.

The genuine curvature trace gives the actual Einstein tensor. The proof gives Lorentzian signature on every tangent fiber, actual metric trace zero, and positive semidefiniteness on every tangent vector. At each point the displayed two nonzero null covectors live in the actual cotangent fiber, and their outer squares sum to the same Einstein tensor with positive coefficient. Contracting the actual coordinate covariant derivative in the open product chart gives zero divergence for the same tensor.

The no-representation conclusion ranges over every auxiliary smooth positive metric and every locally finite nonnegative measure on its unit cotangent section. Each candidate is tested for null support, all symmetric compactly supported tensor moments, and all smooth Hamilton tests of compact base support that are homogeneous of degree one under positive covector scaling. The transition to the Euclidean section sends each covector $p$ to $p/a(p)$ and pushes forward the measure weighted by $a(p)^2$. The same transformed measure preserves null support, moments and transport. These tests use the actual Hamiltonian and geometric volume.

The contradiction uses the real angular multiplier $-2\xi_0/(\xi_0^2+\xi_{\rm sp}^{T}\gamma^{-1}\xi_{\rm sp})$ on both time sheets. Positivity and a transverse test force the numerator of the transport test to vanish where its base cutoff is nonzero. The $11$ moment gives the strict negative transport integral.

## Verification

The locked Lean check prints 485 actual types and transitive axiom sets. Independent reverse review reproduced the check. Author confirmation is pending. Three support theorems supply actual compactness and angular extension for L01. The Cauchy invariant-scale step for L01 remains open.

Frozen Lean receipt SHA256: `201270f43c31b6c659d8dc078b2f612f125aaf895a76f9412b98964c4797a7af`. Independent receipt SHA256: `aa30254c4c248a3814e7821c4661a3bd6517c93b1184b1ba60d6f1322b3c1d31`.
