# Flat admissible sequences have flat smooth limits

[中文](flat-rigidity.zh-CN.md) · [Statement T17](main.en.md#t17)

The locked source is Proposition D.2 (`prop:flat-rigidity`, lines 3390–3392) with proof at lines 3393–3421. The admissible-sequence assumptions are at lines 91–104.

The main Lean declaration is `Burnett.FlatRigidity.isFlat_of_original_flat_sequence`. It uses local uniform convergence measured by the auxiliary Riemannian metric $r$ and the all-compact uniform $L^\infty$ bound for $\nabla^r(g_n-g_0)$. The project uses $dV_{g_0}$ for the essential supremum. The premise and conclusion use the same intrinsic curvature predicate `Burnett.Geometry.FlatRigidity.IsFlat`, defined by the full `CurvatureFiberTensor.tensor` vanishing at every point. Smooth symmetric nondegeneracy suffices and includes the paper's Lorentzian setting. Full flatness also implies the vacuum hypothesis. [Intrinsic derivative statement](intrinsic-dh-geometry.en.md)

The proof chooses a common coordinate ball from the original derivative bound and constructs radial integral solutions with identity at the center. Their displacement derivative and the flat curvature equation give the parallel equations in every coordinate direction. On a smaller closed ball, one strictly increasing subsequence gives uniform limits of the frames and their inverses. The same subsequence of Christoffel coefficients converges weakly against local $L^1$ tests. The weak parallel equation and distributional commutation give zero coordinate curvature. The intrinsic bridge transfers this conclusion at every point of the manifold.

The frozen integrated proof passed 18 actual type and transitive-axiom checks under trust policy A. The receipt SHA256 is `18b0a4a806d27af29b6ff237c3eb7e54bfe0274cceb114e7c3c332377623de5c`. The independent run reproduced the native log byte for byte and checked the original assumptions, the frame construction, and the intrinsic conclusion. Its receipt SHA256 is `b3331ff99e6ee273291f016325cf0bfa5f7da0fbc40c3d45e7ad09a698540286`. These receipts refer to the integrated proof snapshot. The project check covers the modular files registered in the scope. Author confirmation is pending.
