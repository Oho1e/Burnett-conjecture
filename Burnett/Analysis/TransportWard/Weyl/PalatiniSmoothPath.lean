import Burnett.Analysis.TransportWard.Weyl.PalatiniMetricVariation
import Burnett.Analysis.FrozenTransport.V03MetricActionCoefficient
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Joint regularity of the true affine metric path and its computed connection. -/

set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter Set Burnett.RicciSymbol Burnett.V02.EinsteinHilbert
open Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.SmoothMetricConnection (contDiffOn_coordinateJet)
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology

open private contDiffOn_inverseMetricEntry contDiffOn_metricDensity from Burnett.Analysis.FrozenTransport.V03MetricActionCoefficient

local notation "E" => CoordinateSpace

abbrev MetricParameterSpace := ℝ × E
local notation "P" => MetricParameterSpace

/-- The actual open set where the spatial point is in the chart and the
parameter metric is nondegenerate. -/
def nonsingularVariationDomain (g h : E → Mat) (U : Set E) : Set P :=
  Prod.snd ⁻¹' U ∩ uncurry (metricAffineVariation g h) ⁻¹' nonsingularMetricDomain

theorem contDiffOn_metricAffineVariation_joint (g h : E → Mat) {U : Set E}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U) :
    ContDiffOn ℝ ∞ (uncurry (metricAffineVariation g h)) (Prod.snd ⁻¹' U) := by
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  change ContDiffOn ℝ ∞ (fun z : P => g z.2 i j + z.1 * h z.2 i j) (Prod.snd ⁻¹' U)
  exact ((hg i j).comp contDiff_snd.contDiffOn (fun _ hz => hz)).add
    (contDiff_fst.contDiffOn.mul ((hh i j).comp contDiff_snd.contDiffOn (fun _ hz => hz)))

theorem isOpen_nonsingularVariationDomain (g h : E → Mat) {U : Set E} (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U) :
    IsOpen (nonsingularVariationDomain g h U) :=
  (contDiffOn_metricAffineVariation_joint g h hg hh).continuousOn.isOpen_inter_preimage
    (hU.preimage continuous_snd) isOpen_nonsingularMetricDomain

theorem zero_mem_nonsingularVariationDomain (g h : E → Mat) {U : Set E} (x : E)
    (hx : x ∈ U) (hn : Matrix.det (g x) ≠ 0) :
    (0, x) ∈ nonsingularVariationDomain g h U := by
  refine ⟨hx, ?_⟩
  change Matrix.det (metricAffineVariation g h 0 x) ≠ 0
  rw [metricAffineVariation_zero]
  exact hn

private theorem contDiffOn_coordinateJet_metricAffineVariation_joint (g h : E → Mat) {U : Set E}
    (hU : IsOpen U) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U) (a b c : Index) :
    ContDiffOn ℝ ∞ (fun z : P => coordinateJet (metricAffineVariation g h z.1) z.2 a b c)
      (nonsingularVariationDomain g h U) := by
  have hJg := (contDiffOn_coordinateJet g U hU hg a b c).comp
    (contDiff_snd.contDiffOn : ContDiffOn ℝ ∞ Prod.snd (nonsingularVariationDomain g h U))
    (fun _ hz => hz.1)
  have hJh := (contDiffOn_coordinateJet h U hU hh a b c).comp
    (contDiff_snd.contDiffOn : ContDiffOn ℝ ∞ Prod.snd (nonsingularVariationDomain g h U))
    (fun _ hz => hz.1)
  refine (hJg.add (contDiff_fst.contDiffOn.mul hJh)).congr ?_
  intro z hz
  have hzU : z.2 ∈ U := hz.1
  have hgn : DifferentiableComponentsAt g z.2 :=
    fun i j => ((hg i j).contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
  have hhn : DifferentiableComponentsAt h z.2 :=
    fun i j => ((hh i j).contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
  exact congrArg (fun J : Jet => J a b c) (coordinateJet_metricAffineVariation g h z.2 hgn hhn z.1)

theorem contDiffOn_coordinateConnection_metricAffineVariation_joint (g h : E → Mat) {U : Set E}
    (hU : IsOpen U) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U) (a b c : Index) :
    ContDiffOn ℝ ∞ (fun z : P => coordinateConnectionFromMetric (metricAffineVariation g h z.1) z.2 a b c)
      (nonsingularVariationDomain g h U) := by
  have hMetric := (contDiffOn_metricAffineVariation_joint g h hg hh).mono
    (inter_subset_left : nonsingularVariationDomain g h U ⊆ _)
  have hB (d : Index) := (contDiffOn_inverseMetricEntry a d).comp hMetric (fun _ hz => hz.2)
  have hJ := contDiffOn_coordinateJet_metricAffineVariation_joint g h hU hg hh
  unfold coordinateConnectionFromMetric christoffel koszul
  exact ContDiffOn.sum fun d _ => (hB d).mul
    ((((hJ b c d).add (hJ c b d)).sub (hJ d b c)).div_const 2)

theorem contDiffOn_inverseMetricDensity_metricAffineVariation_joint (g h : E → Mat) {U : Set E}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U) (b c : Index) :
    ContDiffOn ℝ ∞ (fun z : P => inverseMetricDensity (metricAffineVariation g h z.1) z.2 b c)
      (nonsingularVariationDomain g h U) := by
  have hMetric := (contDiffOn_metricAffineVariation_joint g h hg hh).mono
    (inter_subset_left : nonsingularVariationDomain g h U ⊆ _)
  exact (contDiffOn_metricDensity.comp hMetric (fun _ hz => hz.2)).mul
    ((contDiffOn_inverseMetricEntry b c).comp hMetric (fun _ hz => hz.2))

/-- A time slice differentiates in the first coordinate of the parameter-space product. -/
theorem hasDerivAt_parameterSlice (F : P → ℝ) (t : ℝ) (x : E)
    (hf : DifferentiableAt ℝ F (t, x)) :
    HasDerivAt (fun u => F (u, x)) (fderiv ℝ F (t, x) (1, 0)) t :=
  (hf.hasFDerivAt.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x)).hasDerivAt

/-- A spatial coordinate partial differentiates in the second coordinate
of the very same parameter-space product. -/
theorem coordinatePartial_spaceSlice_eq_fderiv (F : P → ℝ) (t : ℝ) (x : E) (a : Index)
    (hf : DifferentiableAt ℝ F (t, x)) :
    coordinatePartial (fun y => F (t, y)) x a =
      fderiv ℝ F (t, x) (0, EuclideanSpace.single a 1) :=
  DFunLike.congr_fun (hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)).fderiv
    (EuclideanSpace.single a 1)

/-- Spatial differentiation and the true parameter derivative commute on a
jointly smooth neighborhood of the initial point. -/
theorem hasDerivAt_coordinatePartial_parameterSlice (F : P → ℝ) {U : Set P}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ F U) (x : E) (hx : (0, x) ∈ U) (a : Index) :
    HasDerivAt (fun t => coordinatePartial (fun y => F (t, y)) x a)
      (coordinatePartial (fun y => deriv (fun t => F (t, y)) 0) x a) 0 := by
  let v : P := (1, 0)
  let w : P := (0, EuclideanSpace.single a 1)
  let z : P := (0, x)
  have hF := hf.contDiffAt (hU.mem_nhds hx)
  have hDOn : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hf.fderiv_of_isOpen hU (by simp)
  have hD : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hDOn.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hEval (r : P) : HasFDerivAt (fun y => fderiv ℝ F y r)
      ((ContinuousLinearMap.apply ℝ ℝ r).comp (fderiv ℝ (fderiv ℝ F) z)) z :=
    (ContinuousLinearMap.apply ℝ ℝ r).hasFDerivAt.comp z hD.hasFDerivAt
  have hSpaceFirst : HasDerivAt (fun t => fderiv ℝ F (t, x) w)
      (fderiv ℝ (fderiv ℝ F) z v w) 0 := by
    have hd := hasDerivAt_parameterSlice (fun y => fderiv ℝ F y w) 0 x (hEval w).differentiableAt
    rw [(hEval w).fderiv] at hd
    exact hd
  have hTimeFirst : coordinatePartial (fun y => fderiv ℝ F (0, y) v) x a =
      fderiv ℝ (fderiv ℝ F) z w v := by
    rw [coordinatePartial_spaceSlice_eq_fderiv _ 0 x a (hEval v).differentiableAt, (hEval v).fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, w]
  have hSpaceEq : (fun t => coordinatePartial (fun y => F (t, y)) x a) =ᶠ[𝓝 (0 : ℝ)]
      fun t => fderiv ℝ F (t, x) w := by
    have ht : (fun t : ℝ => (t, x)) ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
      (hU.preimage (continuous_id.prodMk continuous_const)).mem_nhds hx
    filter_upwards [ht] with t ht
    exact coordinatePartial_spaceSlice_eq_fderiv F t x a
      ((hf.contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp))
  have hTimeEq : (fun y => deriv (fun t => F (t, y)) 0) =ᶠ[𝓝 x]
      fun y => fderiv ℝ F (0, y) v := by
    have hy : (fun y : E => ((0 : ℝ), y)) ⁻¹' U ∈ 𝓝 x :=
      (hU.preimage (continuous_const.prodMk continuous_id)).mem_nhds hx
    filter_upwards [hy] with y hy
    exact (hasDerivAt_parameterSlice F 0 y
      ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))).deriv
  have hPartial : coordinatePartial (fun y => deriv (fun t => F (t, y)) 0) x a =
      coordinatePartial (fun y => fderiv ℝ F (0, y) v) x a := by
    unfold coordinatePartial
    rw [hTimeEq.fderiv_eq]
  have hSym := hF.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  refine (hSpaceFirst.congr_of_eventuallyEq hSpaceEq).congr_deriv ?_
  rw [hPartial, hTimeFirst]
  exact hSym v w

end Burnett.V03.Palatini
