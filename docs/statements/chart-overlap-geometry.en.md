# F05 geometry on preferred chart overlaps

[简体中文](chart-overlap-geometry.zh-CN.md)

Lines 392–428 of the manuscript use geometric volume for local defect pairings and compare descriptions of one tensor in different charts. The eight supporting results below concern a given metric field, two preferred charts, and the Jacobian of their transition.

- `geometricMeasure_chartSource_inner_eq_halfDensity` — For a smooth metric field, integrate the scalar complex inner product over the chart source for geometric volume. If that inner product is almost everywhere strongly measurable there, the Bochner integral equals the Lebesgue integral over the target after pulling back both factors and multiplying both by the chart half-density. To infer finite integrals, the application must supply integrability.

- `coordinateMeasure_restrict_L2_inner_eq_halfDensity` — On a measurable subset of the chart target, assume the two representatives are in geometric L² and the two half-density-weighted representatives are in Lebesgue L². The corresponding Hilbert-space inner products agree.

- `coordinateMeasure_memLp_two_iff_halfDensity` — For a smooth nondegenerate metric and any complex representative on a measurable part of the chart target, square integrability for geometric volume is equivalent to square integrability for Lebesgue volume after multiplication by the half-density. Thus geometric L² data supply both weighted input conditions of the preceding inner-product identity.

- `chartHalfDensity_transition` — For two preferred charts with transition Φ, the source half-density at x equals √|det DΦ(x)| times the target half-density at Φ(x). The absolute determinant includes orientation-reversing transitions.

- `overlapKernel_geometry_bounds` — On a compact convex subset of a smooth chart overlap and for a smooth nondegenerate metric field, DΦ and the square-root Jacobian weight are Lipschitz, the weight is bounded and DΦ has a uniform positive lower bound on vector lengths. The bounds give a positive radius on which the variation of DΦ is at most half that lower bound.

- `overlapFar_uniform_arguments` — On a compact subset of the overlap, a fixed positive lower bound for |x−y| gives a uniform positive lower bound for both |Φ(x)−Φ(y)| and |DΦ(x)(x−y)|.

- `exists_transportOverlapCutoff` — A real smooth compactly supported cutoff whose closed support is inside the source overlap has a real smooth compactly supported target cutoff. Pullback by Φ gives the original cutoff throughout the overlap, and its target support lies in the image of the original closed support.

- `exists_countable_chartTransition_windows` — Given a source and target neighborhood at each point, choose positive radii at every point and a countable set of centers. The source half-radius balls at these centers cover the overlap. All closed balls lie in the prescribed neighborhoods and chart domains, and Φ maps each closed source ball into the target open ball.

The paper's coordinate covariance also requires controlling the lower-order conjugation error in the quadratic limit and identifying all ordered covariance components on the same subsequence.

Two reviewers divided the proof sources by authorship and independently recompiled the parts they had not written. They checked the actual types and transitive axioms of all 31 public declarations across the four modules. Eight supporting results enter the regular project check. [Lean sources and manuscript locations](chart-overlap-geometry-source-bindings.json)
