import Burnett.Analysis.TransportWard.Weyl.EHCoordinateDensity
import Burnett.Analysis.IBP.CompactIBP

/-! The exact action difference under a compactly supported coordinate variation. -/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option maxRecDepth 5300

noncomputable section

namespace Burnett.V02.EinsteinHilbert

open Filter MeasureTheory Set Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.SmoothMetricConnection (contDiffOn_matrixInverse)
open scoped BigOperators ContDiff Topology

local notation "E" => CoordinateSpace

private theorem coordinateJet_eq_of_eventuallyEq {g k : E → Mat} {x : E}
    (h : k =ᶠ[𝓝 x] g) :
    coordinateJet k x = coordinateJet g x := by
  funext a b c
  have hc : (fun y => k y b c) =ᶠ[𝓝 x] (fun y => g y b c) := by
    filter_upwards [h] with y hy
    exact congrFun (congrFun hy b) c
  exact DFunLike.congr_fun hc.fderiv_eq (EuclideanSpace.single a 1)

private theorem boundaryVector_eq_of_eventuallyEq {g k : E → Mat} {x : E}
    (h : k =ᶠ[𝓝 x] g) (a : Index) : christoffelBoundaryVector k x a = christoffelBoundaryVector g x a := by
  have hm := h.self_of_nhds
  have hj := coordinateJet_eq_of_eventuallyEq h
  have hW : inverseMetricDensity k x = inverseMetricDensity g x := by
    funext b c
    simp only [inverseMetricDensity, hm]
  simp only [christoffelBoundaryVector, coordinateConnectionFromMetric, hW, hm, hj]

private theorem contDiffOn_coordinateActionDensity (g : E → Mat) {U : Set E} (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) :
    ContDiffOn ℝ ∞ (fun y => metricActionDensity (g y) (coordinateJet g y)) U := by
  have hΓ := contDiffOn_coordinateConnectionFromMetric g hU hg hn
  have hB := contDiffOn_matrixInverse g U hg hn
  have hw := contDiffOn_spatialMetricDensity g hg hn
  change ContDiffOn ℝ ∞ (fun y => metricDensity (g y) * ∑ b, ∑ c,
    inverseMatrix (g y) b c * quadraticDifference (coordinateConnectionFromMetric g y) b c) U
  unfold quadraticDifference
  exact hw.mul (ContDiffOn.sum fun b _ => ContDiffOn.sum fun c _ =>
    (hB b c).mul (ContDiffOn.sum fun a _ => ContDiffOn.sum fun e _ =>
      ((hΓ a a e).mul (hΓ e b c)).sub ((hΓ a c e).mul (hΓ e b a))))

private theorem indicator_smooth_and_compact {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U)
    (hz : ∀ x ∈ U \ K, f x = 0) :
    (∀ x ∉ K, U.indicator f x = 0) ∧
      ContDiff ℝ ∞ (U.indicator f) ∧ HasCompactSupport (U.indicator f) := by
  have hzero (x : E) (hx : x ∉ K) : U.indicator f x = 0 := by
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU, hz x ⟨hxU, hx⟩]
    · exact indicator_of_notMem hxU _
  refine ⟨hzero, contDiff_iff_contDiffAt.mpr fun x => ?_, HasCompactSupport.intro hK hzero⟩
  by_cases hx : x ∈ U
  · exact (hf.contDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq
      (by filter_upwards [hU.mem_nhds hx] with y hy; exact indicator_of_mem hy _)
  · have hxK : x ∈ Kᶜ := fun hxK => hx (hKU hxK)
    have hEq : U.indicator f =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      exact hzero y hy
    exact contDiffAt_const.congr_of_eventuallyEq hEq

private theorem integral_coordinatePartial_eq_zero (f : E → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (a : Index) :
    (∫ x, coordinatePartial f x a) = 0 := by
  let v : E := EuclideanSpace.single a 1
  have hiD : Integrable (fun u => fderiv ℝ f u v) :=
    (Burnett.X02.CompactIBP.continuous_directional hf v).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v)
  have hi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure E)) (f := fun _ : E => (1 : ℝ)) (g := f) (v := v)
    (by simp) (by simpa using hiD) (by simpa using hi)
    (differentiable_const (1 : ℝ)) (hf.differentiable (by simp))
  simpa only [one_mul, fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_mul, integral_zero, neg_zero] using hh

/-- Equality of the relative Einstein–Hilbert action and the actual ΓΓ action
for two metrics that differ on a compact subset of their coordinate domain. -/
theorem integral_relative_negative_scalarDensity_eq_gammaGamma
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (g k : E → Mat)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hk : ∀ i j, ContDiffOn ℝ ∞ (fun y => k y i j) U)
    (hgn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (hkn : ∀ y ∈ U, Matrix.det (k y) ≠ 0)
    (hgs : ∀ y ∈ U, IsSymmetricTensor (g y)) (hks : ∀ y ∈ U, IsSymmetricTensor (k y))
    (hSupport : EqOn k g (U \ K)) :
    (∫ x in U, -(metricDensity (k x) * coordinateScalarCurvature k x) -
      -(metricDensity (g x) * coordinateScalarCurvature g x)) =
    ∫ x in U, metricActionDensity (k x) (coordinateJet k x) -
      metricActionDensity (g x) (coordinateJet g x) := by
  let L (y : E) := metricActionDensity (k y) (coordinateJet k y) -
    metricActionDensity (g y) (coordinateJet g y)
  let R (y : E) := -(metricDensity (k y) * coordinateScalarCurvature k y) -
    -(metricDensity (g y) * coordinateScalarCurvature g y)
  let F (a : Index) (y : E) := christoffelBoundaryVector k y a - christoffelBoundaryVector g y a
  let V (a : Index) := U.indicator (F a)
  let D (y : E) := ∑ a, coordinatePartial (V a) y a
  have hGerm (x : E) (hx : x ∈ U \ K) : k =ᶠ[𝓝 x] g := by
    filter_upwards [(hU.sdiff hK.isClosed).mem_nhds hx] with y hy
    exact hSupport hy
  have hL : ContDiffOn ℝ ∞ L U :=
    (contDiffOn_coordinateActionDensity k hU hk hkn).sub (contDiffOn_coordinateActionDensity g hU hg hgn)
  have hLzero (x : E) (hx : x ∈ U \ K) : L x = 0 := by
    have heq := hGerm x hx
    simp only [L, heq.self_of_nhds, coordinateJet_eq_of_eventuallyEq heq, sub_self]
  obtain ⟨_, hLs, hLc⟩ := indicator_smooth_and_compact hU hK hKU L hL hLzero
  have hF (a : Index) : ContDiffOn ℝ ∞ (F a) U :=
    (contDiffOn_christoffelBoundaryVector k hU hk hkn a).sub
      (contDiffOn_christoffelBoundaryVector g hU hg hgn a)
  have hV (a : Index) : (∀ x ∉ K, V a x = 0) ∧ ContDiff ℝ ∞ (V a) ∧ HasCompactSupport (V a) := by
    refine indicator_smooth_and_compact hU hK hKU (F a) (hF a) ?_
    intro x hx
    exact sub_eq_zero.mpr (boundaryVector_eq_of_eventuallyEq (hGerm x hx) a)
  have hDi (a : Index) : Integrable (fun y => coordinatePartial (V a) y a) := by
    let v : E := EuclideanSpace.single a 1
    exact (Burnett.X02.CompactIBP.continuous_directional (hV a).2.1 v).integrable_of_hasCompactSupport
      ((hV a).2.2.fderiv_apply ℝ v)
  have hDInt : Integrable D := integrable_finset_sum Finset.univ fun a _ => hDi a
  have hDZero : (∫ y, D y) = 0 := by
    rw [show D = (fun y => ∑ a, coordinatePartial (V a) y a) from rfl,
      integral_finset_sum Finset.univ (fun a _ => hDi a)]
    simp only [fun a => integral_coordinatePartial_eq_zero (V a) (hV a).2.1 (hV a).2.2 a,
      Finset.sum_const_zero]
  have hDin (x : E) (hx : x ∈ U) :
      D x = coordinateDivergence (christoffelBoundaryVector k) x -
        coordinateDivergence (christoffelBoundaryVector g) x := by
    simp only [D, coordinateDivergence, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    have hEq : V a =ᶠ[𝓝 x] F a := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact indicator_of_mem hy _
    have hf₁ := ((contDiffOn_christoffelBoundaryVector k hU hk hkn a).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by simp)
    have hf₀ := ((contDiffOn_christoffelBoundaryVector g hU hg hgn a).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by simp)
    simp only [coordinatePartial, hEq.fderiv_eq, F,
      (hf₁.hasFDerivAt.fun_sub hf₀.hasFDerivAt).fderiv, ContinuousLinearMap.sub_apply]
  have hDout (x : E) (hx : x ∉ U) : D x = 0 := by
    have hxK : x ∈ Kᶜ := fun hxK => hx (hKU hxK)
    have hzero (a : Index) : V a =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      exact (hV a).1 y hy
    unfold D
    apply Finset.sum_eq_zero
    intro a _
    rw [coordinatePartial, (hzero a).fderiv_eq]
    simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply]
  have hIdentity : U.indicator R = fun y => U.indicator L y - D y := by
    funext x
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx, R, L, hDin x hx,
        negative_scalarCurvatureDensity_eq_metricActionDensity_sub_divergence k hU hk hkn hks x hx,
        negative_scalarCurvatureDensity_eq_metricActionDensity_sub_divergence g hU hg hgn hgs x hx]
      ring
    · simp only [indicator_of_notMem hx, hDout x hx, sub_zero]
  have hI : (∫ x, U.indicator R x) = ∫ x, U.indicator L x := by
    rw [hIdentity, integral_sub (hLs.continuous.integrable_of_hasCompactSupport hLc) hDInt, hDZero, sub_zero]
  simpa only [integral_indicator hU.measurableSet, R, L] using hI

end Burnett.V02.EinsteinHilbert
