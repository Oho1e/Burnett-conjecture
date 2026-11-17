# Local inverse metrics, connection errors, and positive-functional bounds

2026-11-16; continued from the user-merged PR7 commit `d5c3d06e55c39776716f1fc2e4baddebd032ab00`, whose main CI passed. The article, dependency locks, mathematical standard 1.2, and trust policy A are unchanged. This deliverable provides necessary F04/F05 support, not a complete quadratic-limit theorem or whole-paper proof.

## Actual inverses and uniform control

`InversePerturbation` uses the component sup norm on actual `Tensor2 = Fin 4 → Fin 4 → ℝ`, explicitly defines matrix composition by finite sums, and derives from left/right inverse identities
\[
g_1^{-1}-g_0^{-1}=g_1^{-1}(g_0-g_1)g_0^{-1}.
\]
The product-norm constant is 4 and the inverse-difference estimate constant is 16. Absorbing under `16‖g₁−g₀‖‖g₀⁻¹‖≤1/2` gives the new inverse bound `‖g₁⁻¹‖≤2‖g₀⁻¹‖`, hence inverse difference at most `32‖g₀⁻¹‖²‖g₁−g₀‖`. The new inverse bound is not an input. Actual symmetric nondegenerate bilinear forms and `FiberMetric.contravariant` in a given basis supply the inverse laws.

`InverseField` explicitly uses the matrix inverse instance, not Tensor2 entrywise reciprocals. Nondegeneracy only on K, continuity of background components on K, and compactness of K yield actual inverse continuity and a uniform B>0. Uniform convergence of actual matrix fields gives eventual smallness, uniform new-inverse bounds, and uniform inverse-field convergence with the same B. `InverseSequence` connects this to contravariant fields of actual bilinear metrics, retaining the same parameters and sequence. No nondegeneracy outside K is required.

## Background regularity and the actual error

`BackgroundConnection` assumes only C¹ background components on an open U, K⊂U, and symmetry/nondegeneracy on K. It proves continuity of the actual first Fréchet coordinate jet and of the connection computed from the explicit matrix inverse and Christoffel formula, and equality with actual `metricConnection` on K. Compactness supplies a uniform G>0 bound for Γ(g₀); continuity or boundedness of the desired Γ is not assumed.

`ConnectionError` is the difference of two actual connections minus the background linear principal part:
\[
E=(\Gamma(g_1)-\Gamma(g_0))-L_{g_0}(\nabla^{g_0}(g_1-g_0)).
\]
It proves that E is exactly the Christoffel construction obtained by inserting the inverse difference into the same actual covariant perturbation jet. The actual component sup norm satisfies `‖Christoffel(A,J)‖≤6‖A‖‖J‖`, giving for small perturbations
\[
\|E\|\le192\|g_0^{-1}\|^2\|g_1-g_0\|\|J\|.
\]
`PerturbationJet` proves `‖J‖≤‖rawJet‖+8‖Γ₀‖‖h‖` from the two actual covariant-derivative contractions. Uniform convergence gives eventual `‖h‖≤1`, so the actual raw first-derivative bound constructs the same H.

The final declaration `Burnett.Geometry.ConnectionErrorSequence.metricConnectionError_uniform_of_coordinate_bounds` actually assembles these interfaces: a local C¹ background, compact K, only local symmetry/nondegeneracy, actual differentiability of the sequence on K, an eventual uniform coordinate rawJet bound, and uniform convergence of the original metric components imply **uniform convergence of actual E to zero on K**. Its type does not additionally assume B/G/J bounds, inverse smallness, or convergence of E. The reverse bound `rawJet≤covariantJet+8Γh` is also proved for a future auxiliary-connection bridge.

## L∞ and two general F05 tools

`UniformLInfinity` proves for arbitrary measures actual Lp∞ norm bounds from genuine a.e. bounds, and convergence to zero in actual Lp∞ for restricted measures from uniform convergence on a fixed measurable K. Finite total measure is not required; `MemLp ∞` for each function remains explicit. It does not manufacture a bound using `ENNReal.toReal ∞=0`, nor prove measurability of original E or its physical r norm.

For a real-linear L on an actual C_c subspace with explicit positivity, `PositiveFunctional` uses an actual nonnegative order-unit cutoff e to transfer the genuine C₀ norm for fixed-support tests into `|L f|≤‖f‖∞L(e)`. The full-C_c positive-functional version and actual Urysohn cutoffs on LCH/T2 compact sets give nonnegative finite local constants. This tool assumes neither finite total mass nor proved original PDO positivity, C_c extension, RMK, or measure existence.

## Interfaces with the source still to close

Source lines 91–105 give a `‖D h_n‖L∞(K;r)` bound with `D=∇ʳ` and local C⁰ convergence on the manifold. **This batch's final entry point uses coordinate norms and a raw coordinate first-derivative bound; neither has been renamed as an original assumption.** The auxiliary-r connection, actual compact-set comparison of physical-r and coordinate norms, passage from a.e. derivative bounds to the required pointwise local conditions, manifold charts, and the dV correspondence remain future proofs. The uniform error and general Lp∞ bridge therefore do not establish the complete physical-E conclusion under the original admissibility assumptions.

The route from original vacuum to weak Ricci moments, distributional integration by parts, H⁻¹ compactness, actual F05 PDO bounds/vanishing-error positivity/common measure, and global naturality remain open. No uniform higher-order gn derivatives or whole-domain nondegeneracy is added. New author confirmation is pending; the whole paper remains development/verified=false.
