# Changing the auxiliary metric in the vacuum sequence hypotheses

[简体中文](auxiliary-metric-admissibility.zh-CN.md)

Lines 91–106 of the manuscript control a smooth sequence on a four-manifold using the Levi-Civita connection of an auxiliary Riemannian metric. The comparisons below vary both the tensor norm and the connection.

- `physicalNorm2_compact_compare` — On a fixed compact set the s-norm of every covariant two-tensor is bounded by one constant times its r-norm. The constant is uniform in the point and tensor.

- `locallyUniformlyConverges_changeAuxiliary` — Local uniform convergence of the metric sequence to the same background passes from r to s.

- `normScalar_compact_compare` — On each compact set a constant independent of the smooth two-tensor H bounds the s-norm of its s-covariant derivative by the sum of the r-norms of its r-covariant derivative and H, times that constant.

- `compactDhBound_changeAuxiliary` — The local uniform convergence and the original compact L∞ bounds on the r-covariant derivatives of the metric errors yield a bound for every index n for their s-covariant derivatives, using the same background geometric volume. The proof treats the finite initial segment separately.

- `admissible_iff_changeAuxiliary` — With smooth approximating metrics and smooth background fixed, the conjunction of intrinsic Ricci vacuum for each member, local uniform convergence, and the compact first derivative bounds holds for r if and only if it holds for s. The Lorentzian signature and time orientation are properties of the given metrics and background.

An independent reviewer checked the nine public declarations against the manuscript hypotheses and recompiled both Lean sources.

These estimates allow a construction on the same subsequence to use different auxiliary metrics. The transformation law of the microlocal measure and the transport equation require further arguments. [Source bindings](auxiliary-metric-admissibility-source-bindings.json)
