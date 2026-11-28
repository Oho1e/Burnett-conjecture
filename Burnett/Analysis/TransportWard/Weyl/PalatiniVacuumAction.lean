import Burnett.Analysis.TransportWard.Weyl.PalatiniDensity
import Burnett.Analysis.TransportWard.Weyl.PalatiniCompactBoundary
import Burnett.Analysis.TransportWard.Weyl.PalatiniParametricIntegral

/-! Stationarity of the actual relative actions on a coordinate vacuum. -/

set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option maxRecDepth 5300

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Metric Set Burnett.RicciSymbol Burnett.V02.EinsteinHilbert
open Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped ContDiff Topology

open private coordinateJet_eq_of_eventuallyEq from Burnett.Analysis.TransportWard.Weyl.EHCompactVariation

local notation "E" => CoordinateSpace
local notation "P" => MetricParameterSpace

/-- The relative Einstein–Hilbert action along the actual compact variation. -/
def relativeEinsteinHilbertAction (g h : E → Mat) (U : Set E) (t : ℝ) : ℝ :=
  ∫ y in U, einsteinHilbertDensity (metricAffineVariation g h t) y - einsteinHilbertDensity g y

/-- The relative first-order action on the very same metric path. -/
def relativeGammaGammaAction (g h : E → Mat) (U : Set E) (t : ℝ) : ℝ :=
  ∫ y in U, metricActionDensity (metricAffineVariation g h t y)
        (coordinateJet (metricAffineVariation g h t) y) -
      metricActionDensity (g y) (coordinateJet g y)

private theorem coordinateRicci_eq_of_germ {Γ Δ : E → Connection} {x : E}
    (h : Γ =ᶠ[𝓝 x] Δ) : coordinateRicci Γ x = coordinateRicci Δ x := by
  have hJ : coordinateConnectionJet Γ x = coordinateConnectionJet Δ x := by
    funext d a b c
    have hc : (fun y => Γ y a b c) =ᶠ[𝓝 x] (fun y => Δ y a b c) := by
      filter_upwards [h] with y hy
      exact congrFun (congrFun (congrFun hy a) b) c
    exact DFunLike.congr_fun hc.fderiv_eq (EuclideanSpace.single d 1)
  change ricci (Γ x) (coordinateConnectionJet Γ x) = ricci (Δ x) (coordinateConnectionJet Δ x)
  rw [h.self_of_nhds, hJ]

private theorem einsteinHilbertDensity_eq_off_compact_variation (g h : E → Mat)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hSupport : ∀ y ∈ U \ K, h y = 0)
    (t : ℝ) (x : E) (hx : x ∈ U \ K) :
    einsteinHilbertDensity (metricAffineVariation g h t) x = einsteinHilbertDensity g x := by
  let k := metricAffineVariation g h t
  have hUK := hU.sdiff hK.isClosed
  have hgerm (y : E) (hy : y ∈ U \ K) : k =ᶠ[𝓝 y] g := by
    filter_upwards [hUK.mem_nhds hy] with z hz
    simp only [k, metricAffineVariation, hSupport z hz, smul_zero, add_zero]
  have hC : coordinateConnectionFromMetric k =ᶠ[𝓝 x] coordinateConnectionFromMetric g := by
    filter_upwards [hUK.mem_nhds hx] with y hy
    have heq := hgerm y hy
    simp only [coordinateConnectionFromMetric, heq.self_of_nhds, coordinateJet_eq_of_eventuallyEq heq]
  change einsteinHilbertDensity k x = _
  simp only [einsteinHilbertDensity, coordinateScalarCurvature, (hgerm x hx).self_of_nhds,
    coordinateRicci_eq_of_germ hC]

private theorem setIntegral_eq_on_compact_support (L : E → ℝ) {U K : Set E}
    (hU : MeasurableSet U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hZero : ∀ y ∈ U \ K, L y = 0) :
    (∫ y in U, L y) = ∫ y in K, L y := by
  have hz (y : E) (hy : y ∉ K) : U.indicator L y = 0 := by
    by_cases hyU : y ∈ U
    · rw [indicator_of_mem hyU, hZero y ⟨hyU, hy⟩]
    · exact indicator_of_notMem hyU _
  calc
    (∫ y in U, L y) = ∫ y, U.indicator L y := (integral_indicator hU).symm
    _ = ∫ y in K, U.indicator L y := (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm
    _ = ∫ y in K, L y := setIntegral_congr_fun hK fun y hy => indicator_of_mem (hKU hy) _

/-- The genuine compact affine variation at an actual Ricci-flat metric is
stationary for the signed curvature action and for its first-order ΓΓ form. -/
theorem hasDerivAt_relative_actions_of_coordinateVacuum (g h : E → Mat) {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U)
    (hgs : ∀ y ∈ U, IsSymmetricTensor (g y)) (hhs : ∀ y ∈ U, IsSymmetricTensor (h y))
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (hSupport : ∀ y ∈ U \ K, h y = 0)
    (hVac : ∀ y ∈ U, ∀ b c, coordinateRicci (coordinateConnectionFromMetric g) y b c = 0) :
    HasDerivAt (relativeEinsteinHilbertAction g h U) 0 0 ∧
      HasDerivAt (relativeGammaGammaAction g h U) 0 0 := by
  let Ω := nonsingularVariationDomain g h U
  let F (z : P) := einsteinHilbertDensity (metricAffineVariation g h z.1) z.2
  let C := coordinateConnectionVariation g h
  have hΩ : IsOpen Ω := isOpen_nonsingularVariationDomain g h hU hg hh
  have hf : ContDiffOn ℝ ∞ F Ω := contDiffOn_einsteinHilbertDensity_metricAffineVariation_joint g h hU hg hh
  have hx0 : ({0} : Set ℝ) ×ˢ K ⊆ Ω := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have ht' : t = 0 := by simpa only [mem_singleton_iff] using ht
    subst t
    exact zero_mem_nonsingularVariationDomain g h y (hKU hy) (hn y (hKU hy))
  obtain ⟨I, V, hI, _, h0I, hKV, hIV⟩ := generalized_tube_lemma isCompact_singleton hK hΩ hx0
  have h0 : (0 : ℝ) ∈ I := h0I (mem_singleton 0)
  obtain ⟨ε, hε, hεI⟩ := nhds_basis_closedBall.mem_iff.mp (hI.mem_nhds h0)
  have hSub : closedBall (0 : ℝ) ε ×ˢ K ⊆ Ω := (Set.prod_mono hεI hKV).trans hIV
  have hDerivativeEq : EqOn (fun y => fderiv ℝ F (0, y) (1, 0))
      (fun y => -coordinateDivergence (palatiniBoundaryVector g C) y) K := by
    intro y hy
    have hyΩ := hx0 (show ((0 : ℝ), y) ∈ ({0} : Set ℝ) ×ˢ K from ⟨mem_singleton 0, hy⟩)
    have hd := hasDerivAt_parameterSlice F 0 y
      ((hf.contDiffAt (hΩ.mem_nhds hyΩ)).differentiableAt (by simp))
    exact hd.unique (hasDerivAt_einsteinHilbertDensity_of_coordinateVacuum
      g h hU hg hh hgs hhs hn y (hKU hy) (hVac y (hKU hy)))
  have hBoundaryIntegral :
      (∫ y in K, fderiv ℝ F (0, y) (1, 0)) = 0 := by
    rw [setIntegral_congr_fun hK.measurableSet hDerivativeEq, integral_neg,
      integral_coordinateDivergence_palatini_compact_variation g h hU hK hKU hg hh hn hSupport, neg_zero]
  have hDeriv := hasDerivAt_integral_compact_parameter F hΩ hf hK hε hSub
  rw [hBoundaryIntegral] at hDeriv
  have hNear : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ ball (0 : ℝ) ε := ball_mem_nhds 0 hε
  have hGI : IntegrableOn (einsteinHilbertDensity g) K := by
    have h0C := continuousOn_parameterSlice_compact F hf.continuousOn 0
      (fun y hy => hx0 (show ((0 : ℝ), y) ∈ ({0} : Set ℝ) ×ˢ K from ⟨mem_singleton 0, hy⟩))
    simpa only [F, metricAffineVariation_zero] using h0C.integrableOn_compact hK
  have hRelativeEq : relativeEinsteinHilbertAction g h U =ᶠ[𝓝 (0 : ℝ)]
      (fun t => (∫ y in K, F (t, y)) - ∫ y in K, einsteinHilbertDensity g y) := by
    filter_upwards [hNear] with t ht
    have hKI : IntegrableOn (fun y => F (t, y)) K (volume : Measure E) :=
      (continuousOn_parameterSlice_compact F hf.continuousOn t
      (fun _ hy => hSub ⟨ball_subset_closedBall ht, hy⟩)).integrableOn_compact hK
    have hZero (y : E) (hy : y ∈ U \ K) : F (t, y) - einsteinHilbertDensity g y = 0 :=
      sub_eq_zero.mpr (einsteinHilbertDensity_eq_off_compact_variation g h hU hK hSupport t y hy)
    change (∫ y in U, F (t, y) - einsteinHilbertDensity g y) = _
    rw [setIntegral_eq_on_compact_support _ hU.measurableSet hK.measurableSet hKU hZero, integral_sub hKI hGI]
  have hRelative : HasDerivAt (relativeEinsteinHilbertAction g h U) 0 0 :=
    (hDeriv.sub_const _).congr_of_eventuallyEq hRelativeEq
  have hGammaGammaEq : relativeGammaGammaAction g h U =ᶠ[𝓝 (0 : ℝ)]
      relativeEinsteinHilbertAction g h U := by
    filter_upwards [hNear] with t ht
    let k := metricAffineVariation g h t
    have hk (i j : Index) : ContDiffOn ℝ ∞ (fun y => k y i j) U :=
      (hg i j).add ((contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => t) U).mul (hh i j))
    have hks (y : E) (hy : y ∈ U) : IsSymmetricTensor (k y) := by
      intro i j
      change g y i j + t * h y i j = g y j i + t * h y j i
      rw [hgs y hy i j, hhs y hy i j]
    have hEq : EqOn k g (U \ K) := by
      intro y hy
      simp only [k, metricAffineVariation, hSupport y hy, smul_zero, add_zero]
    have hkn (y : E) (hy : y ∈ U) : Matrix.det (k y) ≠ 0 := by
      by_cases hyK : y ∈ K
      · exact (hSub (show (t, y) ∈ closedBall (0 : ℝ) ε ×ˢ K from
          ⟨ball_subset_closedBall ht, hyK⟩)).2
      · rw [hEq ⟨hy, hyK⟩]
        exact hn y hy
    exact (integral_relative_negative_scalarDensity_eq_gammaGamma hU hK hKU g k hg hk
      hn hkn hgs hks hEq).symm
  exact ⟨hRelative, hRelative.congr_of_eventuallyEq hGammaGammaEq⟩

end Burnett.V03.Palatini
