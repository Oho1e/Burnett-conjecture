# A01. Lipschitz coefficients in a symmetric energy pairing

[Chinese reading copy](a01-principal-energy.zh-CN.md)

The two Lebesgue declarations cover the inequality in
[the locked lemma](../../paper/burnett.tex#L566-L575). The matrix coefficient
version also appears in lines 595–599. The fixed-chart density declarations
address line 591 in the setting of the nested cutoffs in lines 524–529.

For a fixed properly supported matrix left quantization B of order one,
formal symmetry is with respect to the original Lebesgue pairing and the
fixed Euclidean inner product of the field. The compactly supported smooth
input u is represented by finitely many complex Schwartz components.
The scalar coefficients r are smooth, real, symmetric in the two derivative
indices and scalar in the field. Uniform essential bounds U on the
coefficient values and L on their first Fréchet derivatives give U + L as
the coefficient norm convention. The theorem bounds the original absolute
twice imaginary part by C(U + L) times the squared coordinate H¹ norm of u.
The field norm includes the value and the four ordinary partial derivatives.
The constant is selected for the fixed B before the coefficients and field.

The matrix-coefficient declaration uses a Hermitian transpose when both
derivative indices are swapped. The entire B symbol is the same scalar
symbol on each component. Finite field dimension is fixed when choosing C.
The written full symbol hypotheses include joint smoothness, the uniform
frequency and pure base derivative seminorms, first mixed seminorms for the
symbol and its four coordinate derivative symbols, and proper support of
the original kernel relation. The estimates use actual Fourier actions and
exact partial derivatives. The proof closes the Lipschitz L² commutator
through the proved compact-base kernel, decomposition and gluing estimates.

The density declarations assume a fixed positive smooth density on the
coordinate chart and fixed nested compact cutoffs. The original B is
formally symmetric for weighted tests supported on that chart. The positive
square-root extension and exact Fourier cutoff representation reduce the
weighted pairing to the Lebesgue one on the original tests. The H¹ norm on
the right retains the paper's coordinate convention. The constants can
depend on the density and the fixed cutoffs.

The four declarations and original source correspondence passed independent readback. The original staged library compiled with zero errors and four unused-section-variable lint messages. Connecting the manuscript's operator class and particular downstream Weyl actions to the complete left-symbol action remains an open obligation.

## Registered Lean declarations

- `Burnett.Analysis.CarlesonEmbedding.exists_actual_scalarCoefficient_principal_energy_bound`
- `Burnett.Analysis.CarlesonEmbedding.exists_actual_matrixCoefficient_principal_energy_bound`
- `Burnett.Analysis.CarlesonEmbedding.exists_actual_fixedChartDensity_scalarCoefficient_principal_energy_bound`
- `Burnett.Analysis.CarlesonEmbedding.exists_actual_fixedChartDensity_matrixCoefficient_principal_energy_bound`

[Source bindings](a01-principal-energy-source-bindings.json)
