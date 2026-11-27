# Quantitative freezing of a complete cubic energy

[中文](original-cubic-freezing.zh-CN.md)

`Burnett.A03.exists_symmetric_action_freezing_of_local_classical_amplitude` implements `lem:freezing` at lines 736–764 of the locked manuscript. A fixed finite coordinate system represents the real field space. The real symmetric trilinear action has principal diagonal polynomial with terms $C_{IJK}^{ab}z^I\partial_a z^J\partial_b z^K$, where $C_{IJK}^{ab}=C_{IKJ}^{ba}$. The remaining terms have at most one field derivative. The frozen action keeps only the principal coefficients at the center $x_0$. Polarization recovers the actual three-slot evaluations from these two diagonal polynomials with their fixed action normalization.

On the fixed chart window the outer cutoff is one near every supported input. A compact classical two-point amplitude with its smooth kernel represents the localized action through the weak oscillatory limit. The reduction gives the actual homogeneous left principal action and a finite order-zero remainder in value and first derivative on $L^3$. Local equality of the tests identifies all three placements in the cubic action. The frozen multiplier uses the same real odd principal symbol at the center and the fixed even infrared cutoff.

For real smooth fields supported in $B(x_0,R\ell)$ and $0<\ell\leq\ell_0\leq1$, the result proves

$$
\bigl|\mathcal T(z,z,Qz)-\mathcal T_0(z,z,Q_0z)\bigr|
\leq A\ell\|\partial z\|_3^3+B_\ell\|z\|_3\|\partial z\|_3^2.
$$

The choice of $A$ precedes the scale, and the choice of $B_\ell$ at fixed scale precedes the center and field. Both constants are independent of the patch count and frequency splitting of the field. One integration by parts moves the test derivative in the lower-order terms onto the remaining fields and fixed coefficients. The bound uses only first derivatives of the field.

The named modules and the axiom readback passed. Independent review compared the exact statement with the locked manuscript. Author confirmation and the full project audit are pending. [Sources and verification](local-classical-cubic-freezing-source-bindings.json)
