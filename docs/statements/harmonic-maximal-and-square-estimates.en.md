# Maximal and annular square estimates in four dimensions

[简体中文](harmonic-maximal-and-square-estimates.zh-CN.md)

Lines 626–685 use finite-exponent multiplier estimates in the proof of cubic-energy continuity. The lemmas below supply the scalar maximal and L² square estimates for this argument.

- `centeredMax_weak_type` — The four-dimensional centered maximal operator on all positive closed-ball radii satisfies the weak (1,1) distribution bound with constant 256.

- `centeredMax_complex_Lp` — For every measurable complex input and every real p > 1, the Lᵖ seminorm of the maximal function of its absolute value is bounded by the input seminorm times (256 · 2ᵖ · p/(p−1))^(1/p).

- `annular_square_L2` — For a bounded symbol supported where 1/2 < |ξ| < 2, the sum of squared L² norms of the dilated multipliers over any finite set of dyadic scales is at most twice the squared symbol bound times the squared input norm. The initial scale is any positive real number.

- `shifted_annular_square_L2` — For the smooth annular window multiplied by a Fourier modulation, the squared L² bound has constant 2 for every modulation vector, initial scale and finite collection of scales.

The four-dimensional weak and strong maximal bounds and the annular L² square estimates are proved. Continue the commutator construction and establish its finite-exponent bilinear bound across scales before deriving cubic-energy continuity and coefficient differences. [Source bindings](harmonic-maximal-and-square-estimates-source-bindings.json)
