import Burnett.Analysis.TransportWard.Weyl.AffineActionHessian
import Burnett.Analysis.TransportWard.Weyl.LinearizedEulerSymmetry
import Burnett.Analysis.TransportWard.Weyl.EulerActionIntegral
import Burnett.Analysis.TransportWard.Weyl.EulerAffineRegularity
import Mathlib.Analysis.Calculus.Deriv.Shift

set_option autoImplicit false
set_option maxHeartbeats 6300000
set_option maxRecDepth 4300

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Set Function Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Analysis.TransportWardSymbol
open Burnett.V02.EinsteinHilbert (coordinateDivergence)
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology

open private actionDensityOnState actionState actionStateDomain actionState_affine
  contDiffOn_actionDensityOnState isOpen_actionStateDomain from Burnett.Analysis.TransportWard.Weyl.AffineActionHessian
open private fieldVariationDomain isOpen_fieldVariationDomain det_fieldVariation_ne_zero
  contDiffOn_parameterizedEulerBoundary from Burnett.Analysis.TransportWard.Weyl.LinearizedEulerSymmetry
open private integrableOn_and_integral_coordinateDivergence_eq_zero from Burnett.Analysis.TransportWard.Weyl.EulerActionIntegral

local notation "E₀" => CoordinateSpace
local notation "P" => MetricParameterSpace

private theorem affine_field_translate {ι : Type*} (g h : E₀ → ι → ℝ) (s t : ℝ) :
    (fun y => (g y + s • h y) + t • h y) = fun y => g y + (s + t) • h y := by
  funext y
  rw [add_smul, add_assoc]

def quadraticEulerBoundaryVector {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g h k : E₀ → ι → ℝ) (x : E₀) (a : Index) : ℝ :=
  deriv (fun t : ℝ => linearizedEulerBoundaryVector S (fun y => g y + t • h y) h k x a) 0

/-- The third variation of the actual density along the same two equal
metric variations and the independent test. -/
def coordinateActionThirdVariationDensity {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g h k : E₀ → ι → ℝ) (x : E₀) : ℝ :=
  deriv (fun t : ℝ => coordinateActionHessianDensity S (fun y => g y + t • h y) h k x) 0

private theorem contDiffOn_shiftedEulerBoundary {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g h k : E₀ → ι → ℝ) {U : Set E₀}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U) (hk : ContDiffOn ℝ ∞ k U)
    (a : Index) : ContDiffOn ℝ ∞ (fun z : P =>
      linearizedEulerBoundaryVector S (fun y => g y + z.1 • h y) h k z.2 a)
      (fieldVariationDomain S g h U) := by
  let Ω := fieldVariationDomain S g h U
  let F (z : P) := eulerVariationBoundaryVector S (fun y => g y + z.1 • h y) k z.2 a
  have hΩ := isOpen_fieldVariationDomain S g h hU hg hh
  have hF := contDiffOn_parameterizedEulerBoundary S g h k hU hg hh hk a
  have hc : ContDiffOn ℝ ∞ (fun z => fderiv ℝ F z ((1 : ℝ),(0 : E₀))) Ω :=
    (hF.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  apply hc.congr
  intro z hz
  have hD := hasDerivAt_parameterSlice F z.1 z.2
    ((hF.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp))
  unfold linearizedEulerBoundaryVector
  have hPath : (fun t => eulerVariationBoundaryVector S (fun y => (g y + z.1 • h y) + t • h y)
        k z.2 a) = (fun t => F (z.1 + t,z.2)) := by
    funext t
    rw [affine_field_translate g h z.1 t]
  rw [hPath, deriv_comp_const_add (fun t => F (t,z.2)) z.1 0, add_zero]
  exact hD.deriv

private theorem contDiffOn_quadraticEulerBoundaryVector {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g h k : E₀ → ι → ℝ) {U : Set E₀}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U) (hk : ContDiffOn ℝ ∞ k U)
    (hn : ∀ x ∈ U, (assembleMetricComponents S (g x)).det ≠ 0) (a : Index) :
    ContDiffOn ℝ ∞ (fun x => quadraticEulerBoundaryVector S g h k x a) U := by
  let Ω := fieldVariationDomain S g h U
  let F (z : P) := linearizedEulerBoundaryVector S (fun y => g y + z.1 • h y) h k z.2 a
  have hΩ := isOpen_fieldVariationDomain S g h hU hg hh
  have hF := contDiffOn_shiftedEulerBoundary S g h k hU hg hh hk a
  have h0 (x : E₀) (hx : x ∈ U) : (0,x) ∈ Ω := zero_mem_nonsingularVariationDomain _ _ x hx (hn x hx)
  have hc : ContDiffOn ℝ ∞ (fun z => fderiv ℝ F z ((1 : ℝ),(0 : E₀))) Ω :=
    (hF.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  apply (hc.comp (contDiff_const.prodMk contDiff_id).contDiffOn h0).congr
  intro x hx
  exact (hasDerivAt_parameterSlice F 0 x
    ((hF.contDiffAt (hΩ.mem_nhds (h0 x hx))).differentiableAt (by simp))).deriv

private theorem hasDerivAt_coordinateActionHessianDensity_shift {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g h k : E₀ → ι → ℝ) (x : E₀)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x)
    (hn : (assembleMetricComponents S (g x)).det ≠ 0) :
    HasDerivAt (fun t : ℝ => coordinateActionHessianDensity S (fun y => g y + t • h y) h k x)
      (coordinateActionThirdVariationDensity S g h k x) 0 := by
  let D := actionStateDomain (ι := ι)
  let z := actionState S g x
  let v := actionState S h x
  let w := actionState S k x
  let F (q : Mat × (ActionSlot ι → ℝ)) := secondFDeriv (actionDensityOnState S) q v w
  have hFirst : ContDiffOn ℝ ∞ (fderiv ℝ (actionDensityOnState S)) D :=
    (contDiffOn_actionDensityOnState S).fderiv_of_isOpen isOpen_actionStateDomain (by simp)
  have hSecond : ContDiffOn ℝ ∞ (secondFDeriv (actionDensityOnState S)) D :=
    hFirst.fderiv_of_isOpen isOpen_actionStateDomain (by simp)
  have hF : ContDiffOn ℝ ∞ F D :=
    (hSecond.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hG : ContDiff ℝ ∞ (fieldSegment z v) := contDiff_const.add (contDiff_id.smul contDiff_const)
  have h0 : fieldSegment z v 0 ∈ D := by
    simpa only [fieldSegment, zero_smul, add_zero] using (show z ∈ D from hn)
  have hp : ContDiffAt ℝ ∞ (F ∘ fieldSegment z v) 0 :=
    ((hF.contDiffAt (isOpen_actionStateDomain.mem_nhds h0)).comp 0 hG.contDiffAt)
  have hEq : (fun t : ℝ => coordinateActionHessianDensity S (fun y => g y + t • h y) h k x) =
      F ∘ fieldSegment z v := by
    funext t
    dsimp only [coordinateActionHessianDensity, F, comp_apply]
    rw [actionState_affine S g h x hg hh t]
  unfold coordinateActionThirdVariationDensity
  rw [hEq]
  exact (hp.differentiableAt (by simp)).hasDerivAt

private theorem hasDerivAt_shiftedLinearizedEulerPair {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g h k : E₀ → ι → ℝ) {U : Set E₀}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U) (hk : ContDiffOn ℝ ∞ k U)
    (x : E₀) (hx : x ∈ U) (hn : (assembleMetricComponents S (g x)).det ≠ 0) :
    HasDerivAt (fun t : ℝ => ∑ i, k x i * deriv
      (fun u => coordinateDensityEuler S (fun y => g y + u • h y) x i) t)
      (coordinateActionThirdVariationDensity S g h k x -
        coordinateDivergence (quadraticEulerBoundaryVector S g h k) x) 0 := by
  let Ω := fieldVariationDomain S g h U
  have hΩ := isOpen_fieldVariationDomain S g h hU hg hh
  have h0 : (0,x) ∈ Ω := zero_mem_nonsingularVariationDomain _ _ x hx hn
  have hH := hasDerivAt_coordinateActionHessianDensity_shift S g h k x
    ((hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    ((hh.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) hn
  have hDiv : HasDerivAt (fun t : ℝ => coordinateDivergence
      (linearizedEulerBoundaryVector S (fun y => g y + t • h y) h k) x)
      (coordinateDivergence (quadraticEulerBoundaryVector S g h k) x) 0 := by
    unfold coordinateDivergence quadraticEulerBoundaryVector
    exact HasDerivAt.fun_sum fun a _ => hasDerivAt_coordinatePartial_parameterSlice _ hΩ
      (contDiffOn_shiftedEulerBoundary S g h k hU hg hh hk a) x h0 a
  apply (hH.sub hDiv).congr_of_eventuallyEq
  have hNear : (fun t : ℝ => (t,x)) ⁻¹' Ω ∈ 𝓝 (0 : ℝ) :=
    (hΩ.preimage (continuous_id.prodMk continuous_const)).mem_nhds h0
  filter_upwards [hNear] with t ht
  let Uₜ := (fun y : E₀ => (t,y)) ⁻¹' Ω
  have hUₜ : IsOpen Uₜ := hΩ.preimage (continuous_const.prodMk continuous_id)
  have hSub : Uₜ ⊆ U := fun _ hy => hy.1
  have hND (y : E₀) (hy : y ∈ Uₜ) := det_fieldVariation_ne_zero S g h hy
  have hPair := linearizedCoordinateDensityEuler_pairing_eq_hessian_sub_divergence
    S (fun y => g y + t • h y) h k hUₜ ((hg.add (hh.const_smul t)).mono hSub)
    (hh.mono hSub) (hk.mono hSub) x ht (hND x ht)
  have he (i : ι) : linearizedCoordinateDensityEuler S (fun y => g y + t • h y) h x i =
      deriv (fun u => coordinateDensityEuler S (fun y => g y + u • h y) x i) t := by
    unfold linearizedCoordinateDensityEuler
    have hu : (fun u => coordinateDensityEuler S (fun y => (g y + t • h y) + u • h y) x i) =
        (fun u => coordinateDensityEuler S (fun y => g y + (t + u) • h y) x i) := by
      funext u
      rw [affine_field_translate g h t u]
    rw [hu, deriv_comp_const_add (fun u => coordinateDensityEuler S (fun y => g y + u • h y) x i) t 0,
      add_zero]
  simpa only [he] using hPair

theorem quadraticCoordinateDensityEuler_pairing_eq_thirdVariation_sub_divergence
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g h k : E₀ → ι → ℝ) {U : Set E₀}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U) (hk : ContDiffOn ℝ ∞ k U)
    (x : E₀) (hx : x ∈ U) (hn : (assembleMetricComponents S (g x)).det ≠ 0) :
    (∑ i, k x i * deriv (deriv (fun u : ℝ => coordinateDensityEuler S (fun y => g y + u • h y) x i)) 0) =
      coordinateActionThirdVariationDensity S g h k x -
        coordinateDivergence (quadraticEulerBoundaryVector S g h k) x := by
  classical
  have hd (i : ι) : DifferentiableAt ℝ (deriv (fun u : ℝ =>
      coordinateDensityEuler S (fun y => g y + u • h y) x i)) 0 := by
    let e (_ : E₀) (j : ι) : ℝ := if j = i then 1 else 0
    simpa only [e, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq'] using
      (hasDerivAt_shiftedLinearizedEulerPair S g h e hU hg hh contDiffOn_const x hx hn).differentiableAt
  have hD := HasDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) => (hd i).hasDerivAt.const_mul (k x i)
  exact hD.unique (hasDerivAt_shiftedLinearizedEulerPair S g h k hU hg hh hk x hx hn)

/-- Compact support removes the true second boundary variation exactly. -/
theorem integral_quadraticCoordinateDensityEuler_pair_eq_thirdVariation
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g h k : E₀ → ι → ℝ) {U K : Set E₀}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U) (hk : ContDiffOn ℝ ∞ k U)
    (hn : ∀ x ∈ U, (assembleMetricComponents S (g x)).det ≠ 0)
    (hZero : ∀ x ∈ U \ K, k x = 0) :
    (∫ x in K, ∑ i, k x i * deriv (deriv (fun u : ℝ => coordinateDensityEuler S (fun y => g y + u • h y) x i)) 0) =
      ∫ x in K, coordinateActionThirdVariationDensity S g h k x := by
  have hBzero (x : E₀) (hx : x ∈ U \ K) (a : Index) : quadraticEulerBoundaryVector S g h k x a = 0 := by
    unfold quadraticEulerBoundaryVector linearizedEulerBoundaryVector
    simp only [eulerVariationBoundaryVector, hZero x hx, Pi.zero_apply, zero_mul, Finset.sum_const_zero, deriv_const]
  obtain ⟨hDivI, hDiv⟩ := integrableOn_and_integral_coordinateDivergence_eq_zero hU hK hKU
    (quadraticEulerBoundaryVector S g h k) (contDiffOn_quadraticEulerBoundaryVector S g h k hU hg hh hk hn) hBzero
  have hP : ContinuousOn (fun x => ∑ i, k x i * (deriv (deriv (fun u : ℝ =>
      coordinateDensityEuler S (fun y => g y + u • h y) x i)) 0)) U := by
    have hQ := (coordinateDensityEuler_affine_variations_contDiffOn S hU g h hg hh hn).2
    exact continuousOn_finset_sum _ fun i _ =>
      ((continuous_apply i).comp_continuousOn hk.continuousOn).mul
        ((continuous_apply i).comp_continuousOn hQ.continuousOn)
  have hPI := (hP.mono hKU).integrableOn_compact (μ := (volume : Measure E₀)) hK
  calc
    _ = (∫ x in K, ∑ i, k x i * deriv (deriv (fun u : ℝ => coordinateDensityEuler S (fun y => g y + u • h y) x i)) 0) +
        ∫ x in K, coordinateDivergence (quadraticEulerBoundaryVector S g h k) x := by rw [hDiv, add_zero]
    _ = _ := by
      rw [← integral_add hPI hDivI]
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      dsimp only
      rw [quadraticCoordinateDensityEuler_pairing_eq_thirdVariation_sub_divergence S g h k hU hg hh hk
        x (hKU hx) (hn x (hKU hx)), sub_add_cancel]

end Burnett.V03.Palatini
