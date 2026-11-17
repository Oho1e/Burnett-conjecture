# Actual second chart derivatives, global metric connections, and volume regularity

This batch implements necessary geometric dependencies at source lines 91–108, 333–345, and 358–369. The article and trust policy A are unchanged; all additions are support results and do not close F04, F05, or the main theorem. Author confirmation of the new mathematical explanation has not been recorded.

## From actual chart differentiation to connection naturality

ActualChartSecondJet uses the overlap map φ of actual preferred chartAt charts, proves its smoothness, and defines H as basis components of the actual second Fréchet derivative. Symmetry of the two lower H indices follows from the actual second-derivative theorem; C∞ in the actual type is not the analytic order Cω.

MetricJetNaturality differentiates the coordinate law for the same actual tangent-fiber bilinear field B. Equality is used only as a function germ on the open overlap, with no geometric interpretation of total-function values outside the chart. The three new-jet terms are H_bᵀGA, Aᵀ(Σp A_pb J_p)A, and AᵀGH_b. ConnectionTermNaturality cancels the intermediate inverse matrix using actual matrix inversion and nondegeneracy, obtaining

\[
 D\phi\,[\Gamma_{\rm new}(v,w)]
 =\Gamma_{\rm old}(D\phi\,v,D\phi\,w)+D^2\phi[v,w].
\]

A has old-coordinate rows and new-coordinate columns. The Matrix inverse is a matrix inverse, not entrywise reciprocation of a function array. The H terms are fully retained; callers need not provide a jet or connection transformation law.

ChartVectorField.Field is the actual Πm T_mM, and IsSmooth is ContMDiff of the genuine tangent-bundle total-space section. Coordinates are defined from the actual trivialization, with reconstruction, transformation, and a two-way smoothness characterization proved. Differentiating the actual vector-field transformation law supplies a D²φ term that combines with the connection transformation above; ChartConnectionNaturality proves equality of chart derivatives in the same fiber. There is no global smooth frame or identification of different coordinates merely through equality of the underlying TangentSpace types.

## A global smooth affine metric connection

GlobalCovariantDerivative defines the actual vector ∇_V W(m) using the preferred chart centered at m. Proved chart naturality identifies it with the computation in any preferred chart containing m. This construction is not an unproved conclusion field in a structure.

SmoothMetricConnection proves local smoothness of inverse matrices through actual determinants, adjugates, and det⁻¹; actual first derivatives on the open set give smoothness of the jet and hence of the computed Christoffel field. Nondegeneracy is required only on the relevant open set. GlobalCovariantDerivative then eliminates the intermediate smooth-Γ input and proves that smooth V and W produce a genuinely smooth section.

GlobalConnectionLaws separately proves addition and function-linearity in the first slot, addition and constant-linearity in the second, and the function Leibniz rule. The actual types retain the relevant pointwise differentiability conditions, and scalar differentiation uses genuine mfderiv. Addition and multiplication of coordinate functions are used in derivatives only through chart-local equality and open-set function germs.

ChartDifferential links actual mfderiv f on a tangent vector with the chart Fréchet directional derivative. ChartLieBracket obtains the coordinate formula of the actual manifold Lie bracket from mathlib's mpullback_mlieBracket theorem; it does not replace it with a separately defined commutator.

GlobalLeviCivita proves smoothness of B(U,W) through actual Hom-bundle bilinear evaluation, then combines the scalar differential bridge and actual coordinate compatibility to prove

\[
 V(B(U,W))=B(\nabla_V U,W)+B(U,\nabla_V W),\qquad
 \nabla_VW-\nabla_WV=[V,W].
\]

The first identity needs smooth U/W but not a smooth direction V; smoothness of V/W in the second is used for actual bracket coordinate transport. B is globally smooth, symmetric, and nondegenerate, and may have indefinite signature. The original auxiliary Riemannian r is instantiated through its actual smoothness, symmetry, and positive definiteness, yielding its global smooth connection, metric compatibility, and zero torsion.

An actual global connection with these properties is constructed here. No separate uniqueness theorem over all abstract global connection operators is claimed; existing coefficient uniqueness is reused only within its precise scope. Full Lorentz signature, a time-orientation model, and the original intrinsic cov2 Dh and physical three-tensor norm have not yet been connected.

## Regularity of volume on the base manifold

ManifoldVolumeRegularity reuses the actual geometricMeasure of the same B and its preferred-chart formula. Smoothness of B bounds sqrt(abs(det G)) on chart compact sets, giving finite coordinate-compact mass; actual compact neighborhoods within charts then prove global local finiteness and finite mass on compact subsets of M. This uses the original Hausdorff, second-countable, and Borel structures, without assuming finite total mass.

For nondegenerate B, every nonempty open set has strictly positive mass. Local finiteness itself does not require nondegeneracy or symmetry. Neither local finiteness nor positivity is supplied as a caller field. A formula for arbitrary maximal-atlas members and Radon regularity are not claimed. This is the base-manifold dV_g; the F05 phase-space defect measure μ has not yet been constructed.

Next come identification of the original intrinsic cov2 derivative with the existing auxiliaryPerturbationJet, the physical three-tensor norm, and coordinate first-derivative bounds from the original assumptions, followed by integration by parts, weak Ricci identification, and H⁻¹ compactness. No uniform D²g_n assumption is added. The sign of the exact Ricci quadratic correction as minus the old B is retained.

See the [independent readback](actual-chart-connection-review.en.md) and [byte bindings](actual-chart-connection-source-bindings.json) for sources, declarations, and review bindings. Target counts are not completion percentages; whole-paper verified=false. Independent successor work continues automatically once a PR is ready, under [GOAL](../formalization/GOAL.en.md); the final main merge remains a human action.
