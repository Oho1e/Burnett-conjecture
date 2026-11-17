import Burnett.Geometry.IntrinsicCurvature

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.CurvatureComponents

open Filter Set
open scoped BigOperators Topology Manifold ContDiff
open Burnett.RicciSymbol
open ConnectionDifference CurvatureDifference CoordinateCovariantDerivative
open ManifoldMetric ManifoldMetricTransition ChartVectorField

/-- R^a_{bcd} for R(X,Y)Z = D_X D_Y Z - D_Y D_X Z - D_[X,Y] Z. -/
def components (Γ : Connection) (dΓ : ConnectionJet) (a b c d : Index) : ℝ :=
  dΓ c a d b - dΓ d a c b +
    ∑ e, (Γ a c e * Γ e d b - Γ a d e * Γ e c b)

theorem actualJet_lower_symmetric_of_germ (Γ : CoordinateSpace → Connection) (y : CoordinateSpace)
    (hSym : ∀ᶠ z in 𝓝 y, ∀ a b d, Γ z a b d = Γ z a d b) (q a b d : Index) :
    coordinateConnectionJet Γ y q a b d = coordinateConnectionJet Γ y q a d b := by
  have h : (fun z => Γ z a b d) =ᶠ[𝓝 y] (fun z => Γ z a d b) :=
    hSym.mono (fun z hz => hz a b d)
  exact congrArg (fun L : CoordinateSpace →L[ℝ] ℝ => L (EuclideanSpace.single q 1)) h.fderiv_eq

theorem trace_components_eq_ricci (Γ : Connection) (dΓ : ConnectionJet)
    (hSym : ∀ a b d, Γ a b d = Γ a d b)
    (hdSym : ∀ q a b d, dΓ q a b d = dΓ q a d b) (b d : Index) :
    (∑ a : Index, components Γ dΓ a b a d) = ricci Γ dΓ b d := by
  unfold components ricci
  apply Finset.sum_congr rfl
  intro a _
  rw [hdSym a a d b, hdSym d a a b]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [hSym e d b, hSym e a b]

theorem coordinateRicci_eq_trace_components (Γ : CoordinateSpace → Connection) (y : CoordinateSpace)
    (hSym : ∀ᶠ z in 𝓝 y, ∀ a b d, Γ z a b d = Γ z a d b) (b d : Index) :
    coordinateRicci Γ y b d = ∑ a : Index, components (Γ y) (coordinateConnectionJet Γ y) a b a d :=
  (trace_components_eq_ricci (Γ y) (coordinateConnectionJet Γ y) hSym.self_of_nhds
    (actualJet_lower_symmetric_of_germ Γ y hSym) b d).symm

theorem coordinateCurvature_basis (Γ : CoordinateSpace → Connection) (y : CoordinateSpace)
    (hΓ : DifferentiableConnectionAt Γ y) (a b c d : Index) :
    IntrinsicCurvature.coordinateCurvature Γ
      (fun _ => EuclideanSpace.single c 1) (fun _ => EuclideanSpace.single d 1)
      (fun _ => EuclideanSpace.single b 1) y a =
      components (Γ y) (coordinateConnectionJet Γ y) a b c d := by
  have hc (i j : Index) : DifferentiableAt ℝ (fun z =>
      connectionTerm (Γ z) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) y := by
    apply (differentiableAt_piLp 2).mpr
    intro r
    simpa only [connectionTerm_basis] using hΓ r i j
  have hD (i j r q : Index) :
      (fderiv ℝ (fun z => connectionTerm (Γ z) (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1)) y (EuclideanSpace.single q 1)) r =
        coordinateConnectionJet Γ y q r i j := by
    rw [← AffineConnection.fderiv_component (hc i j) r]
    simp only [connectionTerm_basis, coordinateConnectionJet]
  have hbr : _root_.VectorField.lieBracket ℝ (fun _ : CoordinateSpace => EuclideanSpace.single c 1)
      (fun _ => EuclideanSpace.single d 1) = fun _ => 0 := by
    funext z
    simp [_root_.VectorField.lieBracket]
  have hDz (i j : Index) : derivative Γ (fun _ => EuclideanSpace.single i 1)
      (fun _ => EuclideanSpace.single j 1) =
      fun z => connectionTerm (Γ z) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    funext z
    simp [derivative]
  have hz : derivative Γ (fun _ => 0) (fun _ => EuclideanSpace.single b 1) y = 0 := by
    ext r
    simp [derivative, connectionTerm]
  have hOuter (p i j r : Index) : connectionTerm (Γ y) (EuclideanSpace.single p 1)
      (connectionTerm (Γ y) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) r =
      ∑ e : Index, Γ y r p e * Γ y e i j := by
    simp [connectionTerm_apply, EuclideanSpace.single_apply]
  simp only [IntrinsicCurvature.coordinateCurvature, hDz, hbr, hz, sub_zero]
  simp only [derivative, PiLp.sub_apply, PiLp.add_apply]
  rw [hD d b a c, hD c b a d, hOuter c d b a, hOuter d c b a]
  simp only [components, Finset.sum_sub_distrib]
  ring

theorem coordinateRicci_eq_curvature_basis_trace (Γ : CoordinateSpace → Connection) (y : CoordinateSpace)
    (hΓ : DifferentiableConnectionAt Γ y)
    (hSym : ∀ᶠ z in 𝓝 y, ∀ a b d, Γ z a b d = Γ z a d b) (b d : Index) :
    coordinateRicci Γ y b d = ∑ a : Index,
      IntrinsicCurvature.coordinateCurvature Γ
        (fun _ => EuclideanSpace.single a 1) (fun _ => EuclideanSpace.single d 1)
        (fun _ => EuclideanSpace.single b 1) y a := by
  rw [coordinateRicci_eq_trace_components Γ y hSym b d]
  apply Finset.sum_congr rfl
  intro a _
  exact (coordinateCurvature_basis Γ y hΓ a b a d).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem computedConnection_Ricci_basis_trace
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (hSym : ManifoldBilinear.IsSymmetric B) (hND : ManifoldBilinear.IsNondegenerate B)
    (c : M) (y : CoordinateSpace) (hy : y ∈ (chartAt CoordinateSpace c).target) (b d : Index) :
    coordinateRicci (BackgroundConnection.computedConnection (coordinateBilinear B c)) y b d =
      ∑ a : Index, IntrinsicCurvature.coordinateCurvature
        (BackgroundConnection.computedConnection (coordinateBilinear B c))
        (fun _ => EuclideanSpace.single a 1) (fun _ => EuclideanSpace.single d 1)
        (fun _ => EuclideanSpace.single b 1) y a := by
  have hΓ := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection B hB hND c
  apply coordinateRicci_eq_curvature_basis_trace
  · intro a b d
    exact ((contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ a) b) d).contDiffAt
      ((chartAt CoordinateSpace c).open_target.mem_nhds hy)).differentiableAt (by simp)
  · apply Eventually.of_forall
    intro z a b d
    exact christoffel_torsion_free _ _ (coordinateJet_symmetric _ z
      (Eventually.of_forall (fun w => FiberMetric.covariant_symmetric _
        (ManifoldBilinear.coordinateBilinear_symmetric B hSym c w) coordinateBasis))) a b d

end Burnett.Geometry.CurvatureComponents
