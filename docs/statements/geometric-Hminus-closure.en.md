# Strong local H⁻¹ convergence of linearized Ricci from the geometric hypotheses

[简体中文](geometric-Hminus-closure.md)

This batch covers lines 358–388 of the locked manuscript, with its main conclusion at lines 384–388. Seven supporting targets use the same geometric data to show that the actual linearized Ricci operator, localized by any fixed smooth cutoff compactly supported in the target of a preferred chart, converges strongly to zero in the H⁻¹ operator norm for each fixed pair of tensor indices.

Fix the auxiliary Riemannian metric r, a smooth symmetric nondegenerate background g₀, and a smooth symmetric nondegenerate sequence gₙ. The assumptions retain locally uniform convergence measured by r and a uniform L∞ bound on Dʳ(gₙ−g₀) on each compact set for the same geometric measure of g₀. The linearized operator itself uses the background derivative Dᵍ⁰. The theorem explicitly assumes that the actual coordinate Ricci of each gₙ vanishes in the chart. Deriving this premise from the intrinsic vacuum hypothesis remains a separate proof obligation.

Write Cₙ for the actual connection difference, Eₙ for the remainder after its linear approximation, and Aₙ = −Ric(g₀) − Q(Cₙ). On the chart, the exact identity is ℒhₙ = Aₙ − DivΓ₀ Eₙ. The proof realizes χAₙ and χDivΓ₀ Eₙ as continuous linear functionals converging strongly to zero for the same χ. The divergence estimate retains Dχ, and the density-weighted version retains the full derivative D(χρ₀). The uniform bound for Cₙ on each fixed chart compact set includes every n, including the finite set of early indices. The construction uses the original uniform first-derivative control.

The final Lean theorem `Burnett.Analysis.GeometricHminusPrincipalClosure.linearizedRicci_has_strong_realization_of_original` constructs the continuous dual sequence Fₙ. For each n and each genuine smooth compactly supported test φ it proves that φχℒhₙ is integrable and that evaluation of Fₙ on φ equals this integral. Both Fₙ and its operator norm converge strongly to zero. Outside the chart the proof uses the vanishing of χ.

This chartwise, componentwise result serves subsequent global tensor testing in F04 and localization in F05. Gluing across charts, the intrinsic Lorentz vacuum wrapper, and the common defect measure remain open. Author confirmation of the new mathematical correspondence remains to be recorded.

[Independent review](geometric-Hminus-closure-review.en.md) · [Source bindings](geometric-Hminus-closure-source-bindings.json)
