# Fixed gauge-complement projection and its order-zero symbol

[简体中文](fixed-gauge-projection.zh-CN.md)

This delivery implements the projection algebra and symbol estimates used in lines 1603–1604 and 1621–1638 of the locked manuscript.

- At nonzero frequency $\xi$, the Euclidean coordinate pairing gives $P_\xi=I-\xi\xi^{\mathsf T}/|\xi|^2$ and $\Pi_E(\xi)H=P_\xi H P_\xi$. Lean proves idempotence, annihilation of pure-gauge tensors, and transversality of the range. For symmetric $H$, it proves the explicit gauge difference in the manuscript and its orthogonality to the projected range.
- The unregularized real symbol satisfies the componentwise finite-exponent Mikhlin bound. Its fixed radial regularization is smooth and even, vanishes for $|\xi|\le 1$, and agrees with the unregularized symbol for $|\xi|\ge 2$. For each component and each nonnegative integer order $n$, a frequency-independent constant $C$ bounds $(\max(1,|\xi|))^n\|D^n\Pi(\xi)_{abcd}\|$. The regularized components have temperate growth.

The full `prop:general-projection` also requires the action on symmetric gradients of compactly supported distributions, projected-field norm and divergence-source bounds, and preservation of the angular measure. Author confirmation is pending.

- `Burnett.P01.euclideanGaugeProjection_idempotent`
- `Burnett.P01.euclideanGaugeProjection_kills_gauge`
- `Burnett.P01.euclideanGaugeProjection_range_kills_covector`
- `Burnett.P01.euclideanGaugeProjection_sub_eq`
- `Burnett.P01.euclideanGaugeProjection_orthogonal`
- `Burnett.P01.gaugeProjectionSymbol_mikhlin`
- `Burnett.P01.regularizedGaugeProjectionSymbol_even`
- `Burnett.P01.regularizedGaugeProjectionSymbol_zero`
- `Burnett.P01.regularizedGaugeProjectionSymbol_high`
- `Burnett.P01.regularizedGaugeProjectionSymbol_contDiff`
- `Burnett.P01.regularizedGaugeProjectionSymbol_hasTemperateGrowth`
- `Burnett.P01.regularizedGaugeProjectionSymbol_orderZero_weighted`

[Shared source bindings](fixed-gauge-projection-source-bindings.json)
