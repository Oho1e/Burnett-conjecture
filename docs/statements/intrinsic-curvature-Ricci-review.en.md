# Independent review of intrinsic curvature and the Ricci trace

[简体中文](intrinsic-curvature-Ricci-review.md)

Independent reviewers read the actual Lean types in stages, covering the curvature operator, connection coefficients and coordinate contraction, cancellation of vector-field jets, global smooth sections, fiber tensors, and the Ricci trace. They compiled the full set of 64 frozen declarations and checked their types and transitive axioms. The six project modules retain the same proof bodies, definitions, and declaration names. [Source bindings and review evidence](intrinsic-curvature-Ricci-source-bindings.json)

The review checked the Lie bracket order, the order of the fiber arguments, and the sign of coordinate Ricci. Fiber curvature agrees between any two preferred charts at the same point. Ricci is the actual linear trace on the tangent fiber. For every sequence index and point in the chart target, the vacuum bridge uses the Ricci tensor of that same metric. Its coordinate conclusion is restricted to the chart target.

All six project modules passed a Lake build. A separate query used the project imports to check the 64 intrinsic declarations and a subsequent local-analysis consumer, with only the three permitted axioms. This batch registers eight intrinsic supporting targets. The consumer requires the separate strong local H⁻¹ modules and will be delivered separately. Lorentzian signature and time orientation, global tensor testing, and the F05 defect measure remain open. Author confirmation remains to be recorded.
