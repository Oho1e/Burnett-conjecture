import Burnett.Analysis.TransportWard.Weyl.EHBoundaryContraction

/-! Einstein–Hilbert and ΓΓ densities differ by the actual coordinate divergence. -/

set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option maxRecDepth 5200

noncomputable section

namespace Burnett.V02.EinsteinHilbert

open Filter Set Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.BackgroundConnection (computedConnection)
open Burnett.Geometry.SmoothMetricConnection (contDiffOn_matrixInverse)
open scoped BigOperators ContDiff Topology

local notation "E" => CoordinateSpace

def inverseMetricDensity (g : E → Mat) (x : E) : Mat :=
  fun b c => metricDensity (g x) * inverseMatrix (g x) b c

/-- The exact coordinate boundary vector of the scalar-curvature density. -/
def christoffelBoundaryVector (g : E → Mat) (x : E) (a : Index) : ℝ :=
  let W := inverseMetricDensity g x
  let Γ := coordinateConnectionFromMetric g x
  contractedConnection W Γ a - ∑ b, W b a * connectionTrace Γ b

def coordinateDivergence (F : E → Index → ℝ) (x : E) : ℝ :=
  ∑ a, coordinatePartial (fun y => F y a) x a

def coordinateScalarCurvature (g : E → Mat) (x : E) : ℝ :=
  metricTrace (inverseMatrix (g x)) (coordinateRicci (coordinateConnectionFromMetric g) x)

theorem contDiffOn_inverseMetricDensity (g : E → Mat) {U : Set E}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (b c : Index) :
    ContDiffOn ℝ ∞ (fun x => inverseMetricDensity g x b c) U :=
  (contDiffOn_spatialMetricDensity g hg hn).mul (contDiffOn_matrixInverse g U hg hn b c)

theorem contDiffOn_christoffelBoundaryVector (g : E → Mat) {U : Set E} (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (a : Index) :
    ContDiffOn ℝ ∞ (fun x => christoffelBoundaryVector g x a) U := by
  have hW := contDiffOn_inverseMetricDensity g hg hn
  have hΓ := contDiffOn_coordinateConnectionFromMetric g hU hg hn
  unfold christoffelBoundaryVector contractedConnection connectionTrace
  exact (ContDiffOn.sum fun b _ => ContDiffOn.sum fun c _ => (hW b c).mul (hΓ a b c)).sub
    (ContDiffOn.sum fun b _ => (hW b a).mul (ContDiffOn.sum fun e _ => hΓ e b e))

private theorem coordinatePartial_sum {ι : Type*} [Fintype ι] (f : ι → E → ℝ) (x : E) (a : Index)
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    coordinatePartial (fun y => ∑ i, f i y) x a = ∑ i, coordinatePartial (f i) x a := by
  have h := (HasFDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) => (hf i).hasFDerivAt).fderiv
  simp only [coordinatePartial, h, ContinuousLinearMap.sum_apply]

private theorem coordinatePartial_mul (f h : E → ℝ) (x : E) (a : Index)
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) :
    coordinatePartial (fun y => f y * h y) x a =
      coordinatePartial f x a * h x + f x * coordinatePartial h x a := by
  rw [coordinatePartial, (hf.hasFDerivAt.fun_mul hh.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, coordinatePartial]
  ring

private theorem coordinatePartial_sub (f h : E → ℝ) (x : E) (a : Index)
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) :
    coordinatePartial (fun y => f y - h y) x a =
      coordinatePartial f x a - coordinatePartial h x a := by
  simp only [coordinatePartial, (hf.hasFDerivAt.fun_sub hh.hasFDerivAt).fderiv,
    ContinuousLinearMap.sub_apply]

theorem coordinatePartial_inverseMetricDensity (g : E → Mat) {U : Set E} (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (hs : ∀ y ∈ U, IsSymmetricTensor (g y))
    (x : E) (hx : x ∈ U) (a b c : Index) :
    coordinatePartial (fun y => inverseMetricDensity g y b c) x a =
      inverseDensityDerivative (inverseMetricDensity g x) (coordinateConnectionFromMetric g x) a b c := by
  have hxN := hU.mem_nhds hx
  have hd : DifferentiableComponentsAt g x :=
    fun i j => ((hg i j).contDiffAt hxN).differentiableAt (by simp)
  have hJ := coordinateJet_symmetric g x (by
    filter_upwards [hxN] with y hy
    exact hs y hy)
  have hw := ((contDiffOn_spatialMetricDensity g hg hn).contDiffAt hxN).differentiableAt (by simp)
  have hB := ((contDiffOn_matrixInverse g U hg hn b c).contDiffAt hxN).differentiableAt (by simp)
  let B := inverseMatrix (g x)
  let Γ := coordinateConnectionFromMetric g x
  let w := metricDensity (g x)
  have hp := coordinatePartial_mul (fun y => metricDensity (g y))
    (fun y => inverseMatrix (g y) b c) x a hw hB
  change coordinatePartial (fun y => inverseMetricDensity g y b c) x a =
    coordinatePartial (fun y => metricDensity (g y)) x a * B b c +
      w * coordinatePartial (fun y => inverseMatrix (g y) b c) x a at hp
  rw [coordinatePartial_metricDensity g x hd (hs x hx) hJ (hn x hx),
    coordinatePartial_inverseMatrix g x hd (hs x hx) hJ (hn x hx)] at hp
  change _ = w * connectionTrace Γ a * B b c +
    w * (-(∑ e, (B b e * Γ c a e + Γ b a e * B e c))) at hp
  rw [hp, inverseDensityDerivative]
  change _ = connectionTrace Γ a * (w * B b c) -
    ∑ e, ((w * B b e) * Γ c a e + Γ b a e * (w * B e c))
  have hsum : w * (∑ e, (B b e * Γ c a e + Γ b a e * B e c)) =
      ∑ e, ((w * B b e) * Γ c a e + Γ b a e * (w * B e c)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [mul_neg, hsum]
  ring

/-- Divergence of the actual boundary vector. The Ricci derivative terms
appear once, and the ΓΓ contraction appears twice. -/
theorem coordinateDivergence_christoffelBoundaryVector (g : E → Mat) {U : Set E} (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (hs : ∀ y ∈ U, IsSymmetricTensor (g y))
    (x : E) (hx : x ∈ U) :
    let W := inverseMetricDensity g x
    let Γ := coordinateConnectionFromMetric g
    let J := coordinateConnectionJet Γ x
    coordinateDivergence (christoffelBoundaryVector g) x =
      ricciDerivativeContraction W J + 2 * metricTrace W (quadraticDifference (Γ x)) := by
  intro W Γ J
  let Q := inverseMetricDensity g
  have hxN := hU.mem_nhds hx
  have hQ (b c : Index) : DifferentiableAt ℝ (fun y => Q y b c) x :=
    ((contDiffOn_inverseMetricDensity g hg hn b c).contDiffAt hxN).differentiableAt (by simp)
  have hΓ (a b c : Index) : DifferentiableAt ℝ (fun y => Γ y a b c) x :=
    ((contDiffOn_coordinateConnectionFromMetric g hU hg hn a b c).contDiffAt hxN).differentiableAt (by simp)
  have hT (b : Index) : DifferentiableAt ℝ (fun y => connectionTrace (Γ y) b) x :=
    DifferentiableAt.fun_sum fun e _ => hΓ e b e
  have hdQ (a b c : Index) : coordinatePartial (fun y => Q y b c) x a =
      inverseDensityDerivative W (Γ x) a b c :=
    coordinatePartial_inverseMetricDensity g hU hg hn hs x hx a b c
  have hdT (a b : Index) :
      coordinatePartial (fun y => connectionTrace (Γ y) b) x a = ∑ e, J a e b e := by
    unfold connectionTrace
    exact coordinatePartial_sum (fun e y => Γ y e b e) x a (fun e => hΓ e b e)
  have hFirst (a : Index) :
      coordinatePartial (fun y => contractedConnection (Q y) (Γ y) a) x a =
        ∑ b, ∑ c, (inverseDensityDerivative W (Γ x) a b c * Γ x a b c + W b c * J a a b c) := by
    unfold contractedConnection
    rw [coordinatePartial_sum (fun b y => ∑ c, Q y b c * Γ y a b c) x a
      (fun b => DifferentiableAt.fun_sum fun c _ => (hQ b c).mul (hΓ a b c))]
    apply Finset.sum_congr rfl
    intro b _
    rw [coordinatePartial_sum (fun c y => Q y b c * Γ y a b c) x a
      (fun c => (hQ b c).mul (hΓ a b c))]
    apply Finset.sum_congr rfl
    intro c _
    rw [coordinatePartial_mul _ _ x a (hQ b c) (hΓ a b c), hdQ]; rfl
  have hSecond (a : Index) :
      coordinatePartial (fun y => ∑ b, Q y b a * connectionTrace (Γ y) b) x a =
        ∑ b, (inverseDensityDerivative W (Γ x) a b a * connectionTrace (Γ x) b +
          W b a * (∑ e, J a e b e)) := by
    rw [coordinatePartial_sum (fun b y => Q y b a * connectionTrace (Γ y) b) x a
      (fun b => (hQ b a).mul (hT b))]
    apply Finset.sum_congr rfl
    intro b _
    rw [coordinatePartial_mul _ _ x a (hQ b a) (hT b), hdQ, hdT]
  have hBoundary (a : Index) :
      coordinatePartial (fun y => christoffelBoundaryVector g y a) x a =
        (∑ b, ∑ c, (inverseDensityDerivative W (Γ x) a b c * Γ x a b c + W b c * J a a b c)) -
          ∑ b, (inverseDensityDerivative W (Γ x) a b a * connectionTrace (Γ x) b +
            W b a * (∑ e, J a e b e)) := by
    change coordinatePartial (fun y => contractedConnection (Q y) (Γ y) a -
      ∑ b, Q y b a * connectionTrace (Γ y) b) x a = _
    have hA : DifferentiableAt ℝ (fun y => contractedConnection (Q y) (Γ y) a) x := by
      unfold contractedConnection
      exact DifferentiableAt.fun_sum fun b _ =>
        DifferentiableAt.fun_sum fun c _ => (hQ b c).mul (hΓ a b c)
    have hB : DifferentiableAt ℝ (fun y => ∑ b, Q y b a * connectionTrace (Γ y) b) x :=
      DifferentiableAt.fun_sum fun b _ => (hQ b a).mul (hT b)
    rw [coordinatePartial_sub _ _ x a hA hB, hFirst, hSecond]
  have hWsym : IsSymmetricTensor W := by
    intro b c
    exact congrArg (fun r => metricDensity (g x) * r) (inverseMatrix_symmetric (g x) (hs x hx) b c)
  have hJ := coordinateJet_symmetric g x (by
    filter_upwards [hxN] with y hy
    exact hs y hy)
  have ht := christoffel_torsion_free (inverseMatrix (g x)) (coordinateJet g x) hJ
  have hC := inverseDensityDerivative_boundary_contraction W (Γ x) hWsym ht
  simp only [coordinateDivergence, hBoundary, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ricciDerivativeContraction]
  linarith only [hC]

private theorem metricTrace_inverseMetricDensity (g : E → Mat) (x : E) (A : Tensor2) :
    metricTrace (inverseMetricDensity g x) A =
      metricDensity (g x) * metricTrace (inverseMatrix (g x)) A := by
  simp only [metricTrace, inverseMetricDensity, Finset.mul_sum, mul_assoc]

/-- Pointwise sign of the Einstein–Hilbert action in the paper:
the negative scalar-curvature density is the actual ΓΓ density minus
the divergence of the actual coordinate boundary vector. -/
theorem negative_scalarCurvatureDensity_eq_metricActionDensity_sub_divergence
    (g : E → Mat) {U : Set E} (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (hs : ∀ y ∈ U, IsSymmetricTensor (g y))
    (x : E) (hx : x ∈ U) :
    -(metricDensity (g x) * coordinateScalarCurvature g x) =
      metricActionDensity (g x) (coordinateJet g x) -
        coordinateDivergence (christoffelBoundaryVector g) x := by
  let W := inverseMetricDensity g x
  let Γ := coordinateConnectionFromMetric g
  let J := coordinateConnectionJet Γ x
  have hD := coordinateDivergence_christoffelBoundaryVector g hU hg hn hs x hx
  have hR := metricTrace_ricci_eq_derivative_add_quadratic W (Γ x) J
  change -(metricDensity (g x) * metricTrace (inverseMatrix (g x)) (ricci (Γ x) J)) =
    metricDensity (g x) * metricTrace (inverseMatrix (g x)) (quadraticDifference (Γ x)) -
      coordinateDivergence (christoffelBoundaryVector g) x
  rw [← metricTrace_inverseMetricDensity g x, ← metricTrace_inverseMetricDensity g x]
  linarith only [hD, hR]

/-- The pointwise identity in the exact computedConnection representation
used for chart metrics and their scalar curvature. -/
theorem negative_computedScalarDensity_eq_metricActionDensity_sub_divergence
    (g : E → LinearMap.BilinForm ℝ E) {U : Set E} (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => metricComponents g y i j) U)
    (hn : ∀ y ∈ U, Matrix.det (metricComponents g y) ≠ 0)
    (hs : ∀ y ∈ U, IsSymmetricTensor (metricComponents g y)) (x : E) (hx : x ∈ U) :
    -(metricDensity (metricComponents g x) *
        metricTrace (inverseMatrix (metricComponents g x)) (coordinateRicci (computedConnection g) x)) =
      metricActionDensity (metricComponents g x) (coordinateJet (metricComponents g) x) -
        coordinateDivergence (christoffelBoundaryVector (metricComponents g)) x :=
  negative_scalarCurvatureDensity_eq_metricActionDensity_sub_divergence
    (metricComponents g) hU hg hn hs x hx

end Burnett.V02.EinsteinHilbert
