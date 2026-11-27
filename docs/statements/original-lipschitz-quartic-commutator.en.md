# Quartic weak commutator with Lipschitz coefficients

[中文](original-lipschitz-quartic-commutator.zh-CN.md)

`Burnett.A08.exists_paperAnalyticLipschitzQuarticBound` implements
`eq:analytic-quartic-bound` at manuscript lines 1476–1504. Take the original
regularized correction $T_H$ from A07, its actual high adjoint, and an array
of real bounded globally Lipschitz coefficients $d^{ab}=d^{ba}$. The weak
form of $L_d=-\partial_a(d^{ab}\partial_b)$ uses the actual $L^2$ weak
coordinate derivatives of the forward and adjoint outputs. For Schwartz
coefficients this agrees with the existing divergence commutator on the
same fields and the same correction.

The three terms retain the differentiated low field, the actual correction
commutator $[d^{ab},T_H]\partial_bu$, and the differentiated low field in the
adjoint slot. The middle term is identified with the original radian
Fourier distribution after passing the two physical products and their
Fourier pairings to the limit. Its bound uses the essential supremum of the
gradient norm of each coefficient. The resulting bound is

$$
\bigl|\langle i[L_d,T_H]u,u\rangle\bigr|
\le C_\delta\left(
D\|\partial u\|_2\|\partial H\|_4\|\partial u\|_4+
G\|\partial u\|_2\|H\|_4\|\partial u\|_4\right),
$$

where $D$ bounds the coefficient values and $G$ bounds the entrywise
essential-supremum gradient norms. The proof chooses the finite symbol
derivative threshold and the constant before the independent-variable
profile and the input fields. The projected source appears in the ensuing
energy identity beginning at line 1516.

The three weak angular tails at lines 1541–1552 and 1558 use the
same spherical harmonic sum $A_L$, its actual high adjoint, and
the Hermitian part $T_L=(A_L+A_L^*)/2$.
`Burnett.A08.OriginalAngularCutoff.originalWeakDivergenceCommutatorPair_angularTail`
identifies the difference between the finite angular and original
Hermitian weak pairings with those three tails.
`Burnett.A08.OriginalAngularCutoff.exists_boundedLipschitzWeakDivergenceAngularTails`
bounds each term by its original norm product times $(1+L)^{-2}$.
Summing both high-slot estimates preserves the essential supremum of
the gradient norm for each bounded real Lipschitz coefficient.

The six ordinary modules for the quartic bound and angular tails
passed their isolated native replays. The tail replay also imports
the quartic construction. The ordinary project build, independent
candidate review, and author confirmation remain pending.
[Angular-tail sources and verification](original-lipschitz-quartic-angular-tail-source-bindings.json)
[Source and verification record](original-lipschitz-quartic-commutator-source-bindings.json)
