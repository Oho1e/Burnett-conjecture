# Compact Fourier multipliers between spatial cutoffs

[简体中文](compact-frequency-localization.zh-CN.md)

Let $M_a,M_b$ be multiplication by real smooth compactly supported functions on four-dimensional Euclidean space, and let $p$ be a bounded continuous complex symbol. The operator $M_a p(D) M_b$ acts on complex $L^2$ under the pinned Fourier convention.

- `compact_spatial_cutoffs_truncated_multiplier` proves compactness with $p$ restricted to any closed frequency ball. The proof writes the operator as a Bochner integral of rank-one plane-wave operators and uses the operator-norm closed subspace of compact operators.
- `compact_spatial_cutoffs_decaying_multiplier` proves compactness for the full symbol when $p(ξ)$ tends uniformly to zero as $|ξ|$ tends to infinity. The finite-frequency truncations converge in operator norm.

These results support the localized remainder at lines 403–404, one fixed base Fourier frequency at a time. The general variable symbol requires a norm-integrable family and identification with the original quantization. Author confirmation of this supporting correspondence remains pending. [Source bindings](compact-frequency-localization-source-bindings.json)
