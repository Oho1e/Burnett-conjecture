# Bounds for the analytic correction and its rough commutator

[中文](original-analytic-correction-bounds.zh-CN.md)

`Burnett.A08.exists_paperAnalyticCorrectionBounds` is the entry for
`lem:analytic-correction-bounds` at manuscript lines 1380–1394. The input
symbol uses the independent variables of lines 1248–1266 on the compact
normalized low–high domain. The ratio cutoff vanishes when
$|p|\geq\rho|\xi|$ for a fixed $\rho<1/2$. The high infrared cutoff stays in
the symbol. Any fixed low absolute-frequency cutoff is carried by $H$.
The choice of the finite derivative threshold $K$ and constant $C$ precedes
the smooth profile and its jet bound $M$.

The two operators in the conclusion realize the actual scalar Fourier
pairings. The high adjoint uses
$b^\dagger(p,\xi)=\overline{b(-p,\xi+p)}$ with low input $\overline H$.
The pairing has the radian normalization $(2\pi)^{-8}$.
Both operators satisfy

$$
\begin{aligned}
\|T_Hu\|_2 &\le CM\,\|H\|_4\,\|\partial u\|_4,\\
\|[\partial_a,T_H]u\|_2 &\le CM\,\|\partial_aH\|_4\,\|\partial u\|_4,\\
\|[d,T_H]v\|_2 &\le CM\,\|\partial d\|_\infty\,\|H\|_4\,\|v\|_4.
\end{aligned}
$$

The coordinate commutator is identified with $T_{\partial_aH}$ by testing
against Schwartz functions. The rough commutator includes every real
globally Lipschitz $d$, allowing linear growth. The proof approximates the
coefficient modulo its value at zero, passes both Fourier integrals to the
limit and represents the bounded functional in $L^2$. The adjoint uses
the second exponent triple $(4,2,4/3)$. The essential supremum of the
almost-everywhere gradient norm is a valid Lipschitz bound by smooth
convolution and Mathlib's Rademacher theorem.

`Burnett.A08.exists_paperFiniteMatrixAnalyticCorrectionBounds` assembles the three estimates for finite low, input and output component families. The forward Fourier action contracts over the low and input components. The true high adjoint contracts over the low and output components with conjugated low fields. Its value and derivative bounds use the summed component norms. The gradient bound applies to the finite rough commutator pairings.

`Burnett.A08.exists_paperRadialInhomogeneousAnalyticCorrectionBounds` permits a fixed smooth radial weight equal to the radius at sufficiently high frequencies. The value and coordinate derivative bounds use the sum of the high test's L⁴ norm and gradient norm. This includes a Japanese bracket on a fixed radial window and retains the same rough gradient estimate.

The scalar entry and both supplementary entries passed qualified native checks. The project audit and author confirmation are recorded separately. [Sources and verification](original-analytic-correction-bounds-source-bindings.json)
