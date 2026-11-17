import Burnett.Geometry.BackgroundConnection
import Burnett.Geometry.ManifoldBilinear
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth actual inverse components and metric connection

Finite determinant and adjugate formulas give componentwise smoothness of
true matrix inversion on a locally nondegenerate set. Actual coordinate
Frechet differentiation then supplies smooth computed Christoffel fields.
No smooth inverse, connection regularity, or extension outside the open
coordinate domain is supplied as a hypothesis. Symmetry is not needed for
this regularity statement; later Levi-Civita properties use it separately.
-/

noncomputable section
namespace Burnett.Geometry.SmoothMetricConnection
open scoped BigOperators ContDiff
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.InverseField Burnett.Geometry.BackgroundConnection

theorem contDiffOn_det (A : CoordinateSpace → Matrix Index Index ℝ)
    (U : Set CoordinateSpace)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) :
    ContDiffOn ℝ ∞ (fun x => (A x).det) U := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum (fun σ _ => contDiffOn_const.mul
    (contDiffOn_prod (fun i _ => hA (σ i) i)))

theorem contDiffOn_adjugate (A : CoordinateSpace → Matrix Index Index ℝ)
    (U : Set CoordinateSpace)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) (i j : Index) :
    ContDiffOn ℝ ∞ (fun x => (A x).adjugate i j) U := by
  simp only [Matrix.adjugate_apply]
  apply contDiffOn_det (fun x => (A x).updateRow j (Pi.single i (1 : ℝ))) U
  intro a b
  by_cases ha : a = j
  · subst a
    simpa using (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : CoordinateSpace => (Pi.single i (1 : ℝ) : Index → ℝ) b) U)
  · simpa [Matrix.updateRow_apply, ha] using hA a b

theorem contDiffOn_matrixInverse (A : CoordinateSpace → Matrix Index Index ℝ)
    (U : Set CoordinateSpace)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U)
    (hn : ∀ x ∈ U, (A x).det ≠ 0) (i j : Index) :
    ContDiffOn ℝ ∞ (fun x => matrixInverse (A x) i j) U := by
  have hi := ((contDiffOn_det A U hA).inv hn).mul (contDiffOn_adjugate A U hA i j)
  simpa only [matrixInverse, Matrix.inv_def, Ring.inverse_eq_inv',
    Matrix.smul_apply, smul_eq_mul] using hi

theorem contDiffOn_coordinateJet (A : CoordinateSpace → Tensor2)
    (U : Set CoordinateSpace) (hU : IsOpen U)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) (d i j : Index) :
    ContDiffOn ℝ ∞ (fun x => coordinateJet A x d i j) U := by
  have hd := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp (hA i j)).2
  exact hd.clm_apply contDiffOn_const

theorem contDiffOn_computedConnection
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (U : Set CoordinateSpace) (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => metricComponents g x i j) U)
    (hn : ∀ x ∈ U, (g x).Nondegenerate) (a b c : Index) :
    ContDiffOn ℝ ∞ (fun x => computedConnection g x a b c) U := by
  have hdet (x : CoordinateSpace) (hx : x ∈ U) : Matrix.det (metricComponents g x) ≠ 0 := by
    have hd := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero coordinateBasis).mp (hn x hx)
    have hm : BilinForm.toMatrix coordinateBasis (g x) = metricComponents g x := by
      ext i j
      simp only [BilinForm.toMatrix_apply, metricComponents, FiberMetric.covariant]
    simpa only [hm] using hd
  have hi := contDiffOn_matrixInverse (fun x => (metricComponents g x : Matrix Index Index ℝ)) U hg hdet
  have hj := contDiffOn_coordinateJet (metricComponents g) U hU hg
  unfold computedConnection christoffel koszul
  exact ContDiffOn.sum (fun d _ => (hi a d).mul
    ((((hj b c d).add (hj c b d)).sub (hj d b c)).div_const 2))

theorem contDiffOn_computedConnection_field
    (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (U : Set CoordinateSpace) (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => metricComponents g x i j) U)
    (hn : ∀ x ∈ U, (g x).Nondegenerate) :
    ContDiffOn ℝ ∞ (computedConnection g) U := by
  apply contDiffOn_pi.mpr
  intro a
  apply contDiffOn_pi.mpr
  intro b
  apply contDiffOn_pi.mpr
  intro c
  exact contDiffOn_computedConnection g U hU hg hn a b c

open scoped Manifold
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition

theorem contDiffOn_coordinateBilinear_connection
    {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
    [IsManifold Model ∞ M]
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (hn : ManifoldBilinear.IsNondegenerate B) (c : M) :
    ContDiffOn ℝ ∞ (computedConnection (coordinateBilinear B c))
      (chartAt CoordinateSpace c).target := by
  exact contDiffOn_computedConnection_field _ _ (chartAt CoordinateSpace c).open_target
    (ManifoldBilinear.contDiffOn_metricComponents B hB c)
    (fun x hx => ManifoldBilinear.coordinateBilinear_nondegenerate B hn c hx)

end Burnett.Geometry.SmoothMetricConnection
