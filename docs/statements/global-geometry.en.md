# Global geometric volume, physical convergence, and actual coordinate covariant derivatives

This batch fills necessary dependencies at source lines 91–108, 333–345, and 358–369. All are support results and do not close F04, F05, or thm:quadratic. The source identity is unchanged, and author confirmation of the new explanation has not been recorded.

## Geometric volume on the base manifold

MeasureGluing actually defines, on general measurable spaces,

\[
 \mu=\sum_n \nu_n|_{\operatorname{disjointed}(U)_n}.
\]

A countable measurable cover and compatibility on pairwise local intersections give the restriction formula on each cover member; any other measurable local domain compatible with the whole cover has the same formula. Existence and uniqueness are proved without finite total mass or sigma-finiteness. Compatibility remains an explicit input of the general lemma.

ManifoldVolume then eliminates these intermediate inputs in the Borel structure of the actual manifold: actual chart.source/target homeomorphisms become measurableEquiv, and the inverse chart is extended outside the target by c to give a measurable total function. The actual coordinate density is restricted to the target before transport. The proved same-B Jacobian theorem yields local measure compatibility for the same actual fiber-bilinear field B. A countable chart cover is extracted from the original SecondCountable assumption and genuinely glued. The empty manifold is handled separately, with no new Nonempty assumption.

The resulting geometricMeasure B satisfies the following formula for every preferred chart chartAt c, c:M:

\[
 (\mathrm{chart}_c)_*(\mathrm{geometricMeasure}(B)|_{\mathrm{source}_c})
 =\bigl(\sqrt{|\det G_c|}\,dx\bigr)|_{\mathrm{target}_c}.
\]

Callers do not supply the cover, local compatibility, a global measure, or the final chart formula. The formula uniquely determines the measure, independently of the countable subcover chosen. Here “all charts” strictly means the existing preferred chartAt(c:M) family; there is no separate extension theorem for arbitrary maximal-atlas members. Local finiteness, Radon regularity, and nonzero mass are not claimed, and general B need not be nondegenerate. Those properties must later be proved from actual smooth nondegenerate fields when needed.

This is the base-manifold geometric volume dV_g. The defect measure mu on phase space S_r^*M and its transport remain later F05 tasks.

## Genuine global fields and physical C0loc

ManifoldBilinear.Field is a continuous bilinear map on each actual tangent fiber; IsSmooth is ContMDiff of the field as a nested Hom-bundle total-space section. Evaluation in an actual smooth tangent frame and composition with the inverse chart give C∞/C1 coordinate components. Fiber symmetry and left nondegeneracy are also transported through the genuine frame bijection, without coordinate-regularity or nondegeneracy conclusion fields. Auxiliary r.inner is an actual instance of this smooth type.

ManifoldTensorNorm defines physicalNorm2 r B m using the preferred frame centered at m. Invertibility of the actual chart derivative matrix follows from frame injectivity; the same-B matrix law and full inverse-r contraction show that this length equals physical norm2 in any fixed preferred chart containing m. It also equals the actual Hilbert norm for the inverseR⊗inverseR Gram form, without using a curried-Hom operator norm or requiring a global smooth frame.

ManifoldMetricSequence.LocallyUniformlyConverges explicitly means uniform convergence of the actual scalar physicalNorm2 r (B_n-B_0) to zero on every compact subset of M. A compact K in a fixed chart.target is sent through the actual inverse chart to a compact subset of M; the same r and a uniform norm-comparison constant C>0 on K yield uniform convergence of every coordinate component. chart_conditions_of_global combines global smooth/symmetric/nondegenerate fields and this convergence with the required C1, nondegeneracy, neighborhood symmetry, and component convergence, without a caller-supplied coordinate hconv premise.

This batch proves only the direction from this explicit physical-norm C0loc formulation to coordinate conditions. It does not claim equivalence with another, as yet undefined, bundle compact-open topology. Full Lorentz signature, time orientation, and instantiation of the complete original intrinsic Dh assumptions remain unfinished.

## Actual coordinate covariant derivatives

CoordinateCovariantDerivative defines from actual vector fields

\[
 \nabla^\Gamma_VW(x)=DW(x)[V(x)]+\Gamma(x)(V(x),W(x)).
\]

The proof establishes function-linearity in the first slot, a Leibniz rule in the second, and zero torsion expressed with mathlib's actual LieBracket; differentiability assumptions remain explicit at the points actually differentiated. The induced cov2 operation is defined from an actual scalar pairing minus two connection terms. Its basis components agree with the existing covariantJet and the auxiliaryPerturbationJet for the same r/g1-g0.

AffineConnection further constructs a genuine trilinear cov2Differential, proves the three differentiation terms and two cancellations for variable U/W pairings, and obtains tensoriality of the induced derivative, actual metric compatibility and zero torsion of the computed metric connection, and the same-perturbation auxiliary-jet identity. These are actual local coordinate affine operators; the source's global D=Levi-Civita(r) and global closure into smooth sections have not yet been constructed.

LeviCivitaUniqueness uses the actual inverse of a nondegenerate fiber form to prove that zero-torsion, metric-compatible coefficients for the same g/dg equal the actual computedConnection. Uniqueness does not replace existence or compatibility between charts.

## Algebraic transformation retaining nonlinear second-order terms

ConnectionCoordinateChange gives A old-coordinate rows and new-coordinate columns, while H has one old upper index and two new lower indices. With old connection matrices Gamma_p and old metric first jets J_p, it constructs explicitly

\[
 K_b=\sum_p A_{pb}\Gamma_p,\quad
 \widetilde\Gamma_b=A^{-1}(K_bA+H_b),
\]
\[
 \widetilde J_b=H_b^TGA+A^T(\sum_p A_{pb}J_p)A+A^TGH_b.
\]

The actual proof preserves metric compatibility when A is invertible and zero torsion when the lower H slots are symmetric; the uniqueness result then gives the Christoffel identity with a genuine inverse matrix. H terms are not omitted. This is explicit affine second-jet algebra. Identifying A/H/the new jet with actual chart Jacobians/Hessians/Fréchet derivatives remains OPEN, so the algebraic theorem cannot be called global naturality.

## Remaining work

Next are the actual second-order chart chain rule, global LC and identification of its induced cov2 derivative with the current computed jet, followed by the original intrinsic Dh physical bound and actual geometric volume. Volume local finiteness and a broader chart family are added as consumers need them. The existing a.e.-to-pointwise argument on a larger compact neighborhood must be retained. No uniform D²g_n bound or global smooth frame is added.

Then come fixed-test integration by parts, weak Ricci identification, H⁻¹ compactness, and actual F05 PDO/positivity/common-defect-measure constructions. The exact quadratic-correction sign, minus the old B, is retained. See the [review](global-geometry-review.en.md) and [frozen bindings](global-geometry-source-bindings.json) for all 123 declarations and 31 registrations. Whole-paper verified=false.
