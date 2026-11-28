import Burnett.Analysis.TransportWard.Weyl.EulerActionVariation

/-! Ordinary integration-by-parts identity for the same coordinate Euler expression. -/

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4700

noncomputable section

namespace Burnett.V03.Palatini

open Set Burnett.RicciSymbol Burnett.V02.EinsteinHilbert
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Geometry.ConnectionDifference
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology

open private coordinatePartial_sum coordinatePartial_mul from Burnett.Analysis.TransportWard.Weyl.EHCoordinateDensity
open private contDiffOn_coordinateMetricFirstJet from Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet

local notation "E" => CoordinateSpace

private def eulerFluxTerm {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g : E → ι → ℝ) (a : Index) (i : ι) (t : ActionSlot ι) (y : E) : ℝ :=
  metricActionCoefficient S (a, i) t (assembleMetricComponents S (g y)) * coordinateMetricFirstJet g y t

/-- Boundary flux of the first ΓΓ variation with the actual scalar field test. -/
def eulerVariationBoundaryVector {ι : Type*} [Fintype ι] (S : ι → Mat) (g h : E → ι → ℝ)
    (y : E) (a : Index) : ℝ :=
  ∑ i, h y i * ∑ t, eulerFluxTerm S g a i t y

private theorem coordinatePartial_component_eq_firstJet {ι : Type*} [Fintype ι] (h : E → ι → ℝ)
    (x : E) (hh : DifferentiableAt ℝ h x) (a : Index) (i : ι) :
    coordinatePartial (fun y => h y i) x a = coordinateMetricFirstJet h x (a, i) := by
  have hb : coordinateBasis a = EuclideanSpace.single a 1 := EuclideanSpace.basisFun_apply _ _ a
  have hd := hasFDerivAt_pi'.mp hh.hasFDerivAt i
  rw [coordinatePartial, coordinateMetricFirstJet, hd.fderiv, hb]
  rfl

private theorem contDiffOn_eulerFluxTerm {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g : E → ι → ℝ) {U : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hn : ∀ y ∈ U, Matrix.det (assembleMetricComponents S (g y)) ≠ 0)
    (a : Index) (i : ι) (t : ActionSlot ι) :
    ContDiffOn ℝ ∞ (eulerFluxTerm S g a i t) U := by
  have hG := (assembleMetricComponents S).contDiff.comp_contDiffOn hg
  have hC := (contDiffOn_metricActionCoefficient S (a, i) t).comp hG hn
  exact hC.mul (contDiffOn_coordinateMetricFirstJet hU g hg t)

theorem contDiffOn_eulerVariationBoundaryVector {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g h : E → ι → ℝ) {U : Set E} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (hn : ∀ y ∈ U, Matrix.det (assembleMetricComponents S (g y)) ≠ 0) (a : Index) :
    ContDiffOn ℝ ∞ (fun y => eulerVariationBoundaryVector S g h y a) U := by
  unfold eulerVariationBoundaryVector
  exact ContDiffOn.sum fun i _ => ((contDiff_apply ℝ ℝ i).comp_contDiffOn hh).mul
    (ContDiffOn.sum fun t _ => contDiffOn_eulerFluxTerm S g hU hg hn a i t)

private theorem coordinateDivergence_eulerVariationBoundaryVector {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g h : E → ι → ℝ) {U : Set E} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (hn : ∀ y ∈ U, Matrix.det (assembleMetricComponents S (g y)) ≠ 0)
    (x : E) (hx : x ∈ U) :
    let p := coordinateMetricFirstJet g x
    let dp := coordinateMetricFirstJet h x
    let G := assembleMetricComponents S (g x)
    coordinateDivergence (eulerVariationBoundaryVector S g h) x =
      (∑ s, ∑ t, metricActionCoefficient S s t G * dp s * p t) +
        ∑ i, h x i * ∑ a, ∑ t, coordinatePartial (eulerFluxTerm S g a i t) x a := by
  intro p dp G
  have hhD := (hh.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hhd (i : ι) : DifferentiableAt ℝ (fun y => h y i) x :=
    differentiableAt_pi.mp hhD i
  have hF (a : Index) (i : ι) (t : ActionSlot ι) :
      DifferentiableAt ℝ (eulerFluxTerm S g a i t) x :=
    ((contDiffOn_eulerFluxTerm S g hU hg hn a i t).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hSum (a : Index) (i : ι) :
      DifferentiableAt ℝ (fun y => ∑ t, eulerFluxTerm S g a i t y) x :=
    DifferentiableAt.fun_sum fun t _ => hF a i t
  have hDerivative (a : Index) :
      coordinatePartial (fun y => eulerVariationBoundaryVector S g h y a) x a =
        ∑ i, (dp (a, i) * (∑ t, eulerFluxTerm S g a i t x) +
          h x i * (∑ t, coordinatePartial (eulerFluxTerm S g a i t) x a)) := by
    unfold eulerVariationBoundaryVector
    rw [coordinatePartial_sum (fun i y => h y i * ∑ t, eulerFluxTerm S g a i t y) x a
      (fun i => (hhd i).mul (hSum a i))]
    apply Finset.sum_congr rfl
    intro i _
    rw [coordinatePartial_mul _ _ x a (hhd i) (hSum a i),
      coordinatePartial_component_eq_firstJet h x hhD a i, coordinatePartial_sum _ x a (hF a i)]
  have hGradient :
      (∑ a, ∑ i, dp (a, i) * ∑ t, eulerFluxTerm S g a i t x) =
        ∑ s, ∑ t, metricActionCoefficient S s t G * dp s * p t := by
    simp only [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro j _
    change dp (a, i) * (metricActionCoefficient S (a, i) (t, j) G * p (t, j)) = _
    ring
  have hOther :
      (∑ a, ∑ i, h x i * (∑ t, coordinatePartial (eulerFluxTerm S g a i t) x a)) =
        ∑ i, h x i * ∑ a, ∑ t, coordinatePartial (eulerFluxTerm S g a i t) x a := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  simp only [coordinateDivergence, hDerivative, Finset.sum_add_distrib, hGradient, hOther]

private theorem coordinateWeakActionVariation_field_part {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g h : E → ι → ℝ) (x : E) :
    let G := assembleMetricComponents S (g x)
    let H := assembleMetricComponents S (h x)
    let p := coordinateMetricFirstJet g x
    (1 / 2 : ℝ) * (∑ s, ∑ t, fderiv ℝ (metricActionCoefficient S s t) G H * p s * p t) =
      ∑ i, h x i * ∑ s, ∑ t,
        ((1 / 2 : ℝ) * fderiv ℝ (metricActionCoefficient S s t) G (S i)) * p s * p t := by
  intro G H p
  have hLinear (s t : ActionSlot ι) : fderiv ℝ (metricActionCoefficient S s t) G H =
      ∑ i, h x i * fderiv ℝ (metricActionCoefficient S s t) G (S i) := by
    change fderiv ℝ (metricActionCoefficient S s t) G (assembleMetricComponents S (h x)) = _
    simp only [assembleMetricComponents_apply, map_sum, map_smul, smul_eq_mul]
  calc
    _ = ∑ s, ∑ t, ∑ i,
        h x i * (((1 / 2 : ℝ) * fderiv ℝ (metricActionCoefficient S s t) G (S i)) * p s * p t) := by
      simp only [hLinear, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ s, ∑ i, ∑ t,
        h x i * (((1 / 2 : ℝ) * fderiv ℝ (metricActionCoefficient S s t) G (S i)) * p s * p t) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ s, ∑ t,
        h x i * (((1 / 2 : ℝ) * fderiv ℝ (metricActionCoefficient S s t) G (S i)) * p s * p t) :=
      Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

/-- The actual weak ΓΓ first variation is exactly the V03 coordinate Euler
expression paired with the test, plus the spatial divergence of its flux. -/
theorem coordinateWeakActionVariation_eq_coordinateDensityEuler_add_divergence {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g h : E → ι → ℝ) {U : Set E} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (hn : ∀ y ∈ U, Matrix.det (assembleMetricComponents S (g y)) ≠ 0) (x : E) (hx : x ∈ U) :
    coordinateWeakActionVariation S g h x =
      (∑ i, h x i * coordinateDensityEuler S g x i) +
        coordinateDivergence (eulerVariationBoundaryVector S g h) x := by
  have hbasis (a : Index) : coordinateBasis a = EuclideanSpace.single a 1 :=
    EuclideanSpace.basisFun_apply _ _ a
  have hEuler (i : ι) :
      coordinateDensityEuler S g x i =
        (∑ s, ∑ t, ((1 / 2 : ℝ) * fderiv ℝ (metricActionCoefficient S s t)
          (assembleMetricComponents S (g x)) (S i)) *
            coordinateMetricFirstJet g x s * coordinateMetricFirstJet g x t) -
          ∑ a, ∑ t, coordinatePartial (eulerFluxTerm S g a i t) x a := by
    unfold eulerFluxTerm
    simp only [coordinateDensityEuler, coordinatePartial, hbasis]
  dsimp only [coordinateWeakActionVariation]
  have hField := coordinateWeakActionVariation_field_part S g h x
  have hDiv := coordinateDivergence_eulerVariationBoundaryVector S g h hU hg hh hn x hx
  dsimp only at hField hDiv
  rw [hField, hDiv]
  simp only [hEuler, mul_sub, Finset.sum_sub_distrib]
  ring

end Burnett.V03.Palatini
