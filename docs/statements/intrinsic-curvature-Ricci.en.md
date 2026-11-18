# Intrinsic curvature, the Ricci trace, and chartwise vacuum

[简体中文](intrinsic-curvature-Ricci.md)

This batch supplies eight supporting results for the geometric data at lines 99–104 and coordinate curvature calculations at lines 352–388 of the manuscript. The six modules contain 14 definitions and 50 theorems.

The curvature operator uses the existing global Levi-Civita derivative and the manifold Lie bracket from mathlib. Its formula on smooth vector fields cancels the contributions from the first and second jets of the fields. At each fixed point, curvature therefore depends only on the three tangent vectors at that point. Under the manuscript's Hausdorff hypothesis, every tangent vector is the value of a global smooth section. The construction gives a continuous trilinear fiber curvature, proves agreement between any two preferred charts containing the point, and recovers the original curvature operator on global smooth fields.

For fixed tangent vectors U and V, Ricci is the actual linear trace on the tangent fiber of X ↦ R(X,V)U. Conjugation by the tangent frame and the differential of the chart identifies this trace in the coordinate basis with the manuscript's positive contraction Σₐ Rᵃ_{b a d}, the `coordinateRicci` used by the local analysis. The theorem `sequence_coordinateVacuum_of_intrinsic` consequently gives coordinate vacuum for the same smooth symmetric nondegenerate metric sequence on the target of each preferred chart whenever its intrinsic Ricci vanishes.

The bridge is available to the local weak Ricci limit and strong local H⁻¹ conclusions. The complete model of Lorentzian signature and time orientation, global test gluing, the common defect measure, and author confirmation remain separate obligations.

[Independent review](intrinsic-curvature-Ricci-review.en.md) · [Source bindings](intrinsic-curvature-Ricci-source-bindings.json)
