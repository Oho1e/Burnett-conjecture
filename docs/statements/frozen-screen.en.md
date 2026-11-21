# Frozen screen and phase identity

[简体中文](frozen-screen.zh-CN.md)

The proofs follow manuscript lines 2053–2107. They use the four-dimensional ordered coordinate convention and the real inverse metric \(B\).

- The actual \(w\) and \(Q\) give the Euclidean screen perpendicular to \(e\) and \(Be\), where \(e\) has Euclidean length one. On the null cone, the Lorentz form is nonnegative on the Lorentz orthogonal complement of \(e\) and vanishes there precisely on the span of \(e\). Its restriction to the Euclidean screen is positive definite.
- On the null cone, \(\mathsf A=QBQ+(I-Q)\) is invertible. Under invertibility of \(\mathsf A\) and \(w\ne0\), the exact trace-adjusted formula on symmetric matrices fixes precisely the tensors \(J\) satisfying \(Je=JBe=0\) and \(\operatorname{tr}(BJ)=0\). For symmetric \(B,H\), the projected tensor is symmetric.
- One neighborhood of the unit null set works for a compact family with the stated nondegeneracy and Lorentz frame hypotheses. Throughout this neighborhood, the squared Euclidean length of \(w\) and the quadratic form on each unit screen vector have uniform positive lower bounds. Substituting \(e=\xi/|\xi|_E\) gives an even symbol invariant under positive rescaling of \(\xi\).
- For complex amplitudes with zero metric trace and Lorentz contraction, the frozen density-weighted trace reversal of the Fourier Ricci symbol is \(\tfrac12\sqrt{|\det m|}\,q_m(q)J^{\sharp\sharp}=2\sqrt{|\det m|}\,q_m(q)\mathsf C_m J\). This uses \(B=m^{-1}\) and includes slightly off-cone frequencies.

The remaining interfaces include invertibility and smooth symbol bounds throughout the chosen cone, the global angular cutoff and finite-exponent multiplier estimates, and application of the complex identity to the actual Fourier slots of the variational Hessian.

## Registered Lean declarations

- `Burnett.V06.frozenNullScreenProjection_constraints`
- `Burnett.V06.frozenScreenProjection_fixed_iff`
- `Burnett.V06.frozenScreenProjection_symmetric`
- `Burnett.V06.exists_uniform_wide_screen_bounds`
- `Burnett.V06.frozenScreenSymbol_even`
- `Burnett.V06.frozenScreenSymbol_degreeZero`
- `Burnett.V06.frozenEinsteinSymbol_screen_phase`

[Source bindings](frozen-screen-source-bindings.json)
