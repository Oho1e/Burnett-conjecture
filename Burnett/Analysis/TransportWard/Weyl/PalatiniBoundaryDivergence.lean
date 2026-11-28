import Burnett.Analysis.TransportWard.Weyl.PalatiniBoundaryContraction
import Burnett.Analysis.TransportWard.Weyl.PalatiniMetricVariation

/-! The ordinary divergence of the actual Palatini weighted boundary vector. -/

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 5000

noncomputable section

namespace Burnett.V03.Palatini

open Filter Set Burnett.RicciSymbol Burnett.V02.EinsteinHilbert
open Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.SmoothMetricConnection (contDiffOn_matrixInverse contDiffOn_coordinateJet)
open scoped BigOperators ContDiff Topology

open private coordinatePartial_sum coordinatePartial_mul coordinatePartial_sub from Burnett.Analysis.TransportWard.Weyl.EHCoordinateDensity

local notation "E" => CoordinateSpace

/-- The vector density whose ordinary divergence is the metric-density
contraction of the first Ricci variation. -/
def palatiniBoundaryVector (g : E → Mat) (C : E → Connection) (x : E) (a : Index) : ℝ :=
  contractedConnection (inverseMetricDensity g x) (C x) a -
    ∑ b, inverseMetricDensity g x b a * connectionTrace (C x) b

theorem contDiffOn_coordinateConnectionVariation (g h : E → Mat) {U : Set E}
    (hU : IsOpen U) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U)
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (a b c : Index) :
    ContDiffOn ℝ ∞ (fun y => coordinateConnectionVariation g h y a b c) U := by
  have hB := contDiffOn_matrixInverse g U hg hn
  have hBg (i j : Index) :
      ContDiffOn ℝ ∞ (fun y => inverseVariation (g y) (h y) i j) U := by
    simp only [inverseVariation_apply]
    exact (ContDiffOn.sum fun b _ => ContDiffOn.sum fun c _ =>
      (((hB i b).mul (hh b c)).mul (hB c j))).neg
  have hG := contDiffOn_coordinateJet g U hU hg
  have hH := contDiffOn_coordinateJet h U hU hh
  simp only [coordinateConnectionVariation, connectionVariation, Pi.add_apply, christoffel, koszul]
  exact (ContDiffOn.sum fun d _ => (hBg a d).mul
    ((((hG b c d).add (hG c b d)).sub (hG d b c)).div_const 2)).add
    (ContDiffOn.sum fun d _ => (hB a d).mul
      ((((hH b c d).add (hH c b d)).sub (hH d b c)).div_const 2))

theorem contDiffOn_palatiniBoundaryVector (g : E → Mat) (C : E → Connection) {U : Set E}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0)
    (hC : ∀ a b c, ContDiffOn ℝ ∞ (fun y => C y a b c) U) (a : Index) :
    ContDiffOn ℝ ∞ (fun y => palatiniBoundaryVector g C y a) U := by
  have hW := contDiffOn_inverseMetricDensity g hg hn
  unfold palatiniBoundaryVector contractedConnection connectionTrace
  exact (ContDiffOn.sum fun b _ => ContDiffOn.sum fun c _ => (hW b c).mul (hC a b c)).sub
    (ContDiffOn.sum fun b _ => (hW b a).mul (ContDiffOn.sum fun e _ => hC e b e))

/-- Metric compatibility converts the contracted covariant Palatini
variation to the *ordinary* divergence of the genuine vector density. -/
theorem coordinateDivergence_palatiniBoundaryVector (g : E → Mat) (C : E → Connection)
    {U : Set E} (hU : IsOpen U) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (hs : ∀ y ∈ U, IsSymmetricTensor (g y))
    (x : E) (hx : x ∈ U) (hC : DifferentiableConnectionAt C x) :
    coordinateDivergence (palatiniBoundaryVector g C) x =
      metricTrace (inverseMetricDensity g x)
        (covariantDivergenceDifference (coordinateConnectionFromMetric g x)
          (C x) (coordinateConnectionJet C x)) := by
  let W := inverseMetricDensity g
  let Γ := coordinateConnectionFromMetric g x
  let J := coordinateConnectionJet C x
  let D := inverseDensityDerivative (W x) Γ
  have hxN := hU.mem_nhds hx
  have hW (b c : Index) : DifferentiableAt ℝ (fun y => W y b c) x :=
    ((contDiffOn_inverseMetricDensity g hg hn b c).contDiffAt hxN).differentiableAt (by simp)
  have hdW (a b c : Index) : coordinatePartial (fun y => W y b c) x a = D a b c :=
    coordinatePartial_inverseMetricDensity g hU hg hn hs x hx a b c
  have hT (b : Index) : DifferentiableAt ℝ (fun y => connectionTrace (C y) b) x :=
    DifferentiableAt.fun_sum fun e _ => hC e b e
  have hdT (a b : Index) :
      coordinatePartial (fun y => connectionTrace (C y) b) x a = ∑ e, J a e b e :=
    coordinatePartial_sum (fun e y => C y e b e) x a (fun e => hC e b e)
  have hΓJ := coordinateJet_symmetric g x (by
    filter_upwards [hxN] with y hy
    exact hs y hy)
  have hΓ : ∀ a b c, Γ a b c = Γ a c b :=
    christoffel_torsion_free (inverseMatrix (g x)) (coordinateJet g x) hΓJ
  have hWSym : IsSymmetricTensor (W x) :=
    fun b c => congrArg (fun r => metricDensity (g x) * r) (inverseMatrix_symmetric (g x) (hs x hx) b c)
  have hFirst (a : Index) :
      coordinatePartial (fun y => contractedConnection (W y) (C y) a) x a =
        ∑ b, ∑ c, (D a b c * C x a b c + W x b c * J a a b c) := by
    unfold contractedConnection
    rw [coordinatePartial_sum (fun b y => ∑ c, W y b c * C y a b c) x a
      (fun b => DifferentiableAt.fun_sum fun c _ => (hW b c).mul (hC a b c))]
    apply Finset.sum_congr rfl
    intro b _
    rw [coordinatePartial_sum (fun c y => W y b c * C y a b c) x a
      (fun c => (hW b c).mul (hC a b c))]
    apply Finset.sum_congr rfl
    intro c _
    rw [coordinatePartial_mul _ _ x a (hW b c) (hC a b c), hdW]; rfl
  have hSecond (a : Index) :
      coordinatePartial (fun y => ∑ b, W y b a * connectionTrace (C y) b) x a =
        ∑ b, (D a b a * connectionTrace (C x) b + W x b a * (∑ e, J a e b e)) := by
    rw [coordinatePartial_sum (fun b y => W y b a * connectionTrace (C y) b) x a
      (fun b => (hW b a).mul (hT b))]
    apply Finset.sum_congr rfl
    intro b _
    rw [coordinatePartial_mul _ _ x a (hW b a) (hT b), hdW, hdT]
  have hBoundary (a : Index) :
      coordinatePartial (fun y => palatiniBoundaryVector g C y a) x a =
        (∑ b, ∑ c, (D a b c * C x a b c + W x b c * J a a b c)) -
          ∑ b, (D a b a * connectionTrace (C x) b + W x b a * (∑ e, J a e b e)) := by
    change coordinatePartial (fun y => contractedConnection (W y) (C y) a -
      ∑ b, W y b a * connectionTrace (C y) b) x a = _
    have hA : DifferentiableAt ℝ (fun y => contractedConnection (W y) (C y) a) x := by
      unfold contractedConnection
      exact DifferentiableAt.fun_sum fun b _ => DifferentiableAt.fun_sum fun c _ =>
        (hW b c).mul (hC a b c)
    have hB : DifferentiableAt ℝ (fun y => ∑ b, W y b a * connectionTrace (C y) b) x :=
      DifferentiableAt.fun_sum fun b _ => (hW b a).mul (hT b)
    rw [coordinatePartial_sub _ _ x a hA hB, hFirst, hSecond]
  rw [weighted_covariantDivergenceDifference_eq (W x) Γ (C x) J hWSym hΓ]
  simp only [coordinateDivergence, hBoundary, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ricciDerivativeContraction, D]
  ring

end Burnett.V03.Palatini
