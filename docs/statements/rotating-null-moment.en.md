# X03: conservation, positive null moments, and transport

This batch formalizes the unnumbered counterexample at source lines 3215–3239, which the user explicitly included among the final targets. It uses an alternative proof permitted by the adopted standard, retaining every original tensor property and the nonexistence of a transported representation. Author confirmation of the new mathematical explanation has not been recorded; current whole-project and remote evidence are obtained separately. No whole-paper verification is claimed.

## The original tensor and precise conclusion

Fix c>0, put v(t)=(cos t,sin t,0), k±=(-1,±v), and T=c(k+⊗k++k−⊗k−). The actual Lean aggregate theorem rotating_null_moment_counterexample proves together: smoothness of T in four dimensions, symmetry, ordinary quadratic-form positive semidefiniteness, zero Minkowski trace, actual zero four-dimensional Lorentz divergence, two nonzero null rays, the exact displayed decomposition, and nonexistence on any open time neighborhood I of zero of a locally finite nonnegative measure simultaneously satisfying null support, the T moment identity, and Hamiltonian transport.

The registered tensor_components additionally verifies T00=2c, T0i=0 for spatial i, and Tij=2c vi vj. T is the tensor specified in the source; the moment identity uses T on the left, rather than replacing it by G(m). No vacuum approximation is constructed, and this does not close the actual Einstein-tensor counterexample in X04.

## Actual cosphere measure and test classes

The base is actual Euclidean R4, and frequencies have the coordinate representation Fin4→R. The physical Euclidean unit condition is explicitly Q(ξ)=Σa ξa²=1; the Lean sup-norm unit sphere of this Pi type cannot replace it. UnitPhase I={(x,ξ):x0∈I,Q(ξ)=1} retains both time directions. μ is an actual nonnegative Borel Measure on this space, with local finiteness required only there. This is weaker than the original Radon assumption, and adds neither finite total mass nor local finiteness of its ambient pushforward at the boundary of I.

The proof establishes compactness of the Q=1 angular shell and of the full angular-fiber preimage above fixed compact K⊂{x:x0∈I}; this gives actual integrability under the original μ of the continuous weights with compact base support used in the argument. The pushforward ambientMeasure is used only to consume the proved integral-error bound; it has no additional local-finiteness premise.

HasTensorMoments uses all smooth symmetric compactly supported coordinate tensors S with base support inside I, with the full sums T_ab S^ab and S^ab ξa ξb. Actual 00 and 12/21 tests with f/2 yield the precise component moments; integrability on both sides is proved. These global coordinate tests restrict to legitimate original tests on I. The contradiction needs only this subclass; it does not conversely claim that zero extensions of all original-domain tests have been formalized as equivalent.

CanonicalHamilton is defined from actual Fréchet partial derivatives of the original P=1/2 m^{ab}ξaξb and the full difference of the two Poisson sums. Its frequency derivative is computed as raised ξ, and its base derivative as zero. IsTransportTest requires actual joint smoothness on the punctured space, positive one-homogeneity, and compact BASE support. The Hamiltonian derivative is taken before restriction to the unit cosphere; compact frequency support is not required. Genuine integrability of the Hamiltonian integrals used is derived by the model, rather than supplied as an unproved structure field.

## The formalized alternative proof

Use the odd one-homogeneous extension, smooth at all nonzero frequencies,

\[
 F(\xi)=-2\xi_0\xi_1\xi_2/Q(\xi).
\]

On both sheets of the nonzero null cone, (-ξ0)F=ξ1ξ2 and |ξj F|≤ξ0². The actual Hamiltonian derivative therefore gives

\[
 |H_P(\phi F)-\xi_1\xi_2\partial_t\phi|
 \le\xi_0^2\sum_{j=1}^3|\partial_j\phi|.
\]

In any neighborhood I of zero, an actual nonnegative nonzero χ∈C∞c is constructed with support where cos(2t)>0, so ∫χcos(2t)>0. An actual spatial bump η and a larger plateau θ give the same C>0 such that, for every positive scale R, the sum of absolute spatial derivatives of φ_R=χ(t)η(x/R) is bounded by β_R=χ(t)(C/R)θ(x/R). Spatial projection is a genuine CLM, and compact support is transported through a continuous inverse coordinate map. A separate actual proof supplies a measure-preserving splitting Euclidean R4→R×Euclidean R3. Genuine integrability and Fubini yield the R³ integral scaling, and actual one-dimensional integration by parts gives the time term with the correct minus sign.

The final NoTransport proof uses the same original μ and its same ambient pushforward, eliminating all additional integral inputs through the full moment identity: the 12 moment gives the leading term −A R³, and the 00 moment bounds the spatial error by B R², where

\[
 A=2c(\int\eta)(\int\chi\cos2t)>0,\qquad
 B=2cC(\int\theta)(\int\chi)>0.
\]

A zero transport integral would imply A R≤B. Choosing R=B/A+1>0 gives a contradiction. Smoothness, compact support, and support within I of the time-derivative test, as well as μ-integrability of the leading term, error, and Hamiltonian integrals, are all derived from the original data. No remaining hDerivative, error-bound, moment, or transport-conclusion field replaces the original proof.

The source's future-sheet folding, support determination, and two branch weights form a different proof route. This batch does not claim formal verification of those intermediate steps, or verification of the source's exact transport-integral formula through the large-R proof. The final counterexample and every T property are proved in this explicit model and have undergone independent readback.

## Delivery scope

The 10 sources have 194 public declarations, including four inherited instances. The 29 support targets and the original parent form 30 new machine-audit registrations; the parent already existed in the inventory, so only its implementation/review status is updated. The new candidate totals 354 targets, 424 inventory entries, and 115 Lean sources. The old 324 targets, 395 inventory entries except the parent's status, 104 mathematical leaf sources, article, dependency locks, standard 1.2, and three-axiom policy are retained.

The [independent readback](rotating-null-moment-review.en.md) and [byte bindings](rotating-null-moment-source-bindings.json) record actual versions separately. Author confirmation, complete project checks, and actual combined CI still require separate evidence; whole-paper verified=false. Unclosed portions of the other 16 formal results, X04/X06, F04/F05, and the main defect-measure/transport argument are not completed by this batch.
