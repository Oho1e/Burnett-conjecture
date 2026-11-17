# The analytic core of local H⁻¹

This batch addresses source lines 384–388, adds six modules with 75 declarations, and registers 14 semantic endpoints. It supplies two concrete analytic consumers: directional derivatives of strongly vanishing L² remainders, and bounded L² sources with a common smooth compact cutoff. See the [bindings](analysis-hminus-source-bindings.json) and [review](analysis-hminus-review.en.md) for exact sources, types, and independent-review identities. Author confirmation of the new explanation has not been recorded; the parent results and whole-paper certification are not completed by this batch.

## Actual test space and norm

The underlying space is real four-dimensional EuclideanSpace. D is the submodule of all actual real-valued smooth compactly supported tests. Jφ consists of φ and its four actual Fréchet directional derivatives in a genuine five-slot L² Hilbert space. The H¹ model is the closure of J(D); testMap has genuinely dense range, and continuous functionals are uniquely determined by their values on all actual tests. The H⁻¹ model is its actual continuous real dual, with the operator norm.

For every actual L² source u and direction v, a directional distributional functional is constructed with test value −∫u D_vφ and operator norm ≤‖v‖‖u‖. When u is represented by an actual smooth function f, local integration by parts identifies it with ∫φ D_vf and proves this test integral integrable. D_vf need not belong to L², and f itself need not be compactly supported. For a strongly vanishing L² sequence, these functionals and their norms genuinely tend to zero strongly.

## Fourier and duality bridges with the same cutoff

The real smooth sequence fₙ has a single actual χ∈D, equal to one wherever any fₙ is nonzero; its actual L² norms have a uniform finite bound, and ∫fₙφ tends to zero for every fixed φ∈D. The parameters, χ, and tests are fixed before n.

This χ and the L² pairing yield actual L¹ integrability and a uniform Fourier bound. Fixed real tests are first complexified through their actual real and imaginary parts, then χ is multiplied by the negative-2π phase to prove pointwise convergence of the actual Fourier transforms at every frequency. Actual Schwartz conversion, finite measure of a fixed frequency ball, and a common dominating function give dominated convergence of the squared energy.

The sole weight is W(ξ)=1+4π²‖ξ‖². The actual Fourier formula for Schwartz derivatives and Parseval prove

    ‖Jφ‖² = ∫ W(ξ) |Fφ(ξ)|².

An actual weighted L² construction, Cauchy–Schwarz, and the Plancherel pairing first bound all actual tests. Density of testMap and a closed inequality then extend the bound to the whole H¹ model, giving the actual sourceFunctional the operator-norm bound sqrt(∫|Ff|²/W). This bridge is proved internally rather than assumed by the caller.

For high frequencies, the actual proof bounds the full negative-order integral of a nonnegative integrable energy F by its integral over a frequency ball plus C/R, with R fixed before n. Parseval supplies the uniform full-frequency energy bound. Letting the energy on each fixed ball tend to zero then proves that ∫|Ffₙ|²/W and its square root tend to zero.

The final CompactRellich consumer internally constructs the actual Fₙ for the same sequence and returns the integral identity for every n and every actual test, strong convergence of Fₙ to zero, and convergence of ‖Fₙ‖ to zero. The eLpNorm exponent is 2 and the bound is an L² norm bound; membership in MemLp is proved internally for each term. The functional witness is chosen before all tests, rather than selected anew for each test.

## Production modules and remaining scope

StrongL2Hminus, LocalHminusFourier, H1FourierEnergy, HminusWeightedDual, WeightedFourierTail, and CompactRellich contain 18, 13, 11, 21, 8, and 4 items respectively. Three files have module names different from their declaration namespaces; registration uses the correct qualified names. frequencyWeight is defined only once, in H1FourierEnergy.

These are general analytic support results. Actual localization of the original vacuum sequence, the finitely many early indices, the exact principal-operator decomposition, and assembly with the same background and witnesses must be registered in the corresponding geometric deliverable. Full Lorentz/vacuum-data instantiation, global tensor interfaces, F04/F05, and transport do not close automatically. No uniform D²gₙ or global smooth frame assumption has been added. The article and trust policy A remain locked.
