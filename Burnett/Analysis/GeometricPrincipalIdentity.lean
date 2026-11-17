import Burnett.Analysis.VacuumWeakRicci

set_option autoImplicit false

noncomputable section

namespace Burnett.Analysis.GeometricPrincipalIdentity

open Filter Set
open scoped ContDiff Manifold Topology BigOperators
open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference BackgroundConnection ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open CurvatureDifference LocalWeakRicci LocalWeakRicciIdentification

/-- Exactly the paper's covariant operator ℒH=Div_Γ0 L(D^g0 H), with its real derivative jet. -/
def linearizedRicci (g0 g1 : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (y : CoordinateSpace) (b d : Index) : ℝ :=
  covariantDivergenceDifference (computedConnection g0 y) (linearConnection g0 g1 y)
    (coordinateConnectionJet (linearConnection g0 g1) y) b d

def boundedRicciSource (g0 g1 : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (y : CoordinateSpace) (b d : Index) : ℝ :=
  -coordinateRicci (computedConnection g0) y b d - quadraticDifference (connectionDifference g0 g1 y) b d

theorem coordinateConnectionJet_add (A B : CoordinateSpace → Connection) (y : CoordinateSpace)
    (hA : DifferentiableConnectionAt A y) (hB : DifferentiableConnectionAt B y) :
    coordinateConnectionJet (fun x => A x + B x) y =
      coordinateConnectionJet A y + coordinateConnectionJet B y := by
  funext q a b d
  simp only [coordinateConnectionJet, Pi.add_apply]
  rw [fderiv_fun_add (hA a b d) (hB a b d), ContinuousLinearMap.add_apply]

theorem covariantDerivative_add (Γ C D : Connection) (dC dD : ConnectionJet) (q a b d : Index) :
    covariantDerivative Γ (C+D) (dC+dD) q a b d =
      covariantDerivative Γ C dC q a b d + covariantDerivative Γ D dD q a b d := by
  have hs : (∑ e : Index, (Γ a q e * (C+D) e b d - Γ e q b * (C+D) a e d - Γ e q d * (C+D) a b e)) =
      (∑ e : Index, (Γ a q e * C e b d - Γ e q b * C a e d - Γ e q d * C a b e)) +
        ∑ e : Index, (Γ a q e * D e b d - Γ e q b * D a e d - Γ e q d * D a b e) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    simp only [Pi.add_apply]
    ring
  unfold covariantDerivative
  rw [hs]
  simp only [Pi.add_apply]
  ring

theorem covariantDivergenceDifference_add (Γ C D : Connection) (dC dD : ConnectionJet) (b d : Index) :
    covariantDivergenceDifference Γ (C+D) (dC+dD) b d =
      covariantDivergenceDifference Γ C dC b d + covariantDivergenceDifference Γ D dD b d := by
  unfold covariantDivergenceDifference
  simp_rw [covariantDerivative_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem divergence_connectionDifference_eq_linearizedRicci_add_error
    (g0 g1 : Field (M := M)) (h0 : IsSmooth g0) (h1 : IsSmooth g1)
    (hn0 : IsNondegenerate g0) (hn1 : IsNondegenerate g1) (c : M)
    (y : CoordinateSpace) (hy : y ∈ (chartAt CoordinateSpace c).target) (b d : Index) :
    covariantDivergenceDifference (computedConnection (coordinateBilinear g0 c) y)
      (connectionDifference (coordinateBilinear g0 c) (coordinateBilinear g1 c) y)
      (coordinateConnectionJet (connectionDifference (coordinateBilinear g0 c) (coordinateBilinear g1 c)) y) b d =
      linearizedRicci (coordinateBilinear g0 c) (coordinateBilinear g1 c) y b d +
        covariantDivergenceDifference (computedConnection (coordinateBilinear g0 c) y)
          (ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear g1 c) y)
          (coordinateConnectionJet (ConnectionErrorLInfinity.computedError
            (coordinateBilinear g0 c) (coordinateBilinear g1 c)) y) b d := by
  let L := linearConnection (coordinateBilinear g0 c) (coordinateBilinear g1 c)
  let E := ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear g1 c)
  have hL : DifferentiableConnectionAt L y := fun a b d =>
    ((linearConnection_component_smoothOn g0 g1 h0 h1 hn0 hn1 c a b d).contDiffAt
      ((chartAt CoordinateSpace c).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hE : DifferentiableConnectionAt E y := fun a b d =>
    ((computedError_component_smoothOn g0 g1 h0 h1 hn0 hn1 c a b d).contDiffAt
      ((chartAt CoordinateSpace c).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hC : connectionDifference (coordinateBilinear g0 c) (coordinateBilinear g1 c) =
      fun x => L x + E x := by
    funext x
    exact connection_difference_eq_linear_plus_error (coordinateBilinear g0 c) (coordinateBilinear g1 c) x
  rw [hC, coordinateConnectionJet_add L E y hL hE]
  exact covariantDivergenceDifference_add _ (L y) (E y) _ _ b d

theorem linearizedRicci_eq_source_sub_error_of_coordinateVacuum
    (g0 g1 : Field (M := M)) (h0 : IsSmooth g0) (h1 : IsSmooth g1)
    (hs0 : IsSymmetric g0) (hs1 : IsSymmetric g1)
    (hn0 : IsNondegenerate g0) (hn1 : IsNondegenerate g1) (c : M)
    (y : CoordinateSpace) (hy : y ∈ (chartAt CoordinateSpace c).target)
    (hVac : ∀ b d, coordinateRicci (computedConnection (coordinateBilinear g1 c)) y b d = 0)
    (b d : Index) :
    linearizedRicci (coordinateBilinear g0 c) (coordinateBilinear g1 c) y b d =
      boundedRicciSource (coordinateBilinear g0 c) (coordinateBilinear g1 c) y b d -
        covariantDivergenceDifference (computedConnection (coordinateBilinear g0 c) y)
          (ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear g1 c) y)
          (coordinateConnectionJet (ConnectionErrorLInfinity.computedError
            (coordinateBilinear g0 c) (coordinateBilinear g1 c)) y) b d := by
  have hΓ0 := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g0 h0 hn0 c
  have hΓ1 := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g1 h1 hn1 c
  have hd0 : DifferentiableConnectionAt (computedConnection (coordinateBilinear g0 c)) y := fun a b d =>
    ((contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ0 a) b) d).contDiffAt
      ((chartAt CoordinateSpace c).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hd1 : DifferentiableConnectionAt (computedConnection (coordinateBilinear g1 c)) y := fun a b d =>
    ((contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ1 a) b) d).contDiffAt
      ((chartAt CoordinateSpace c).open_target.mem_nhds hy)).differentiableAt (by simp)
  have h := coordinateRicci_vacuum_identity (computedConnection (coordinateBilinear g0 c))
    (computedConnection (coordinateBilinear g1 c)) y
    (computedConnection_torsion_free_of_symmetric g0 hs0 c y)
    (computedConnection_torsion_free_of_symmetric g1 hs1 c y) hd0 hd1 hVac b d
  have hs := divergence_connectionDifference_eq_linearizedRicci_add_error g0 g1 h0 h1 hn0 hn1 c y hy b d
  change 0 = coordinateRicci (computedConnection (coordinateBilinear g0 c)) y b d +
    covariantDivergenceDifference (computedConnection (coordinateBilinear g0 c) y)
      (connectionDifference (coordinateBilinear g0 c) (coordinateBilinear g1 c) y)
      (coordinateConnectionJet (connectionDifference (coordinateBilinear g0 c) (coordinateBilinear g1 c)) y) b d +
    quadraticDifference (connectionDifference (coordinateBilinear g0 c) (coordinateBilinear g1 c) y) b d at h
  rw [hs] at h
  unfold boundedRicciSource
  linarith

theorem linearizedRicci_sequence_eq_source_sub_error_on_target
    (g0 : Field (M := M)) (g : ℕ → Field (M := M))
    (h0 : IsSmooth g0) (hg : ∀ n, IsSmooth (g n))
    (hs0 : IsSymmetric g0) (hs : ∀ n, IsSymmetric (g n))
    (hn0 : IsNondegenerate g0) (hn : ∀ n, IsNondegenerate (g n)) (c : M)
    (hVac : ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ b d,
      coordinateRicci (computedConnection (coordinateBilinear (g n) c)) y b d = 0) :
    ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ b d,
      linearizedRicci (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d =
        boundedRicciSource (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y b d -
          covariantDivergenceDifference (computedConnection (coordinateBilinear g0 c) y)
            (ConnectionErrorLInfinity.computedError (coordinateBilinear g0 c) (coordinateBilinear (g n) c) y)
            (coordinateConnectionJet (ConnectionErrorLInfinity.computedError
              (coordinateBilinear g0 c) (coordinateBilinear (g n) c)) y) b d :=
  fun n y hy b d => linearizedRicci_eq_source_sub_error_of_coordinateVacuum
    g0 (g n) h0 (hg n) hs0 (hs n) hn0 (hn n) c y hy (hVac n y hy) b d

end Burnett.Analysis.GeometricPrincipalIdentity
