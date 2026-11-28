import Burnett.Analysis.TransportWard.Weyl.EulerActionDivergence
import Burnett.Analysis.TransportWard.Weyl.PalatiniVacuumAction

/-! The actual first ΓΓ variation against a compact test in the V03 coordinates. -/

set_option autoImplicit false
set_option maxHeartbeats 6600000
set_option maxRecDepth 5200

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Metric Set Burnett.RicciSymbol Burnett.V02.EinsteinHilbert
open Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology

open private setIntegral_eq_on_compact_support from Burnett.Analysis.TransportWard.Weyl.PalatiniVacuumAction
open private coordinateJet_eq_of_eventuallyEq indicator_smooth_and_compact integral_coordinatePartial_eq_zero
  from Burnett.Analysis.TransportWard.Weyl.EHCompactVariation

local notation "E" => CoordinateSpace
local notation "P" => MetricParameterSpace

private theorem integrableOn_and_integral_coordinateDivergence_eq_zero {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (F : E → Index → ℝ)
    (hF : ∀ a, ContDiffOn ℝ ∞ (fun y => F y a) U)
    (hZero : ∀ y ∈ U \ K, ∀ a, F y a = 0) :
    IntegrableOn (coordinateDivergence F) K ∧ (∫ y in K, coordinateDivergence F y) = 0 := by
  let V (a : Index) := U.indicator (fun y => F y a)
  let D (y : E) := ∑ a, coordinatePartial (V a) y a
  have hV (a : Index) : (∀ y ∉ K, V a y = 0) ∧ ContDiff ℝ ∞ (V a) ∧ HasCompactSupport (V a) :=
    indicator_smooth_and_compact hU hK hKU _ (hF a) (fun y hy => hZero y hy a)
  have hDi (a : Index) : Integrable (fun y => coordinatePartial (V a) y a) := by
    let v : E := EuclideanSpace.single a 1
    exact (Burnett.X02.CompactIBP.continuous_directional (hV a).2.1 v).integrable_of_hasCompactSupport
      ((hV a).2.2.fderiv_apply ℝ v)
  have hDInt : Integrable D := integrable_finset_sum Finset.univ fun a _ => hDi a
  have hD0 : (∫ y, D y) = 0 := by
    rw [show D = (fun y => ∑ a, coordinatePartial (V a) y a) from rfl,
      integral_finset_sum Finset.univ (fun a _ => hDi a)]
    simp only [fun a => integral_coordinatePartial_eq_zero (V a) (hV a).2.1 (hV a).2.2 a,
      Finset.sum_const_zero]
  have hEq : EqOn D (coordinateDivergence F) K := by
    intro x hx
    unfold coordinateDivergence D
    apply Finset.sum_congr rfl
    intro a _
    have heq : V a =ᶠ[𝓝 x] (fun y => F y a) := by
      filter_upwards [hU.mem_nhds (hKU hx)] with y hy
      exact indicator_of_mem hy _
    exact DFunLike.congr_fun heq.fderiv_eq (EuclideanSpace.single a 1)
  have hDout (x : E) (hx : x ∉ K) : D x = 0 := by
    have hzero (a : Index) : V a =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
      exact (hV a).1 y hy
    unfold D
    apply Finset.sum_eq_zero
    intro a _
    rw [coordinatePartial, (hzero a).fderiv_eq]
    simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply]
  have hAE : D =ᵐ[(volume : Measure E).restrict K] coordinateDivergence F := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure E)) hK.measurableSet] with y hy
    exact hEq hy
  refine ⟨hDInt.integrableOn.congr hAE, ?_⟩
  rw [← setIntegral_congr_fun hK.measurableSet hEq,
    setIntegral_eq_integral_of_forall_compl_eq_zero hDout, hD0]

private theorem hasDerivAt_relative_integral_compact_parameter (F : P → ℝ) (G : E → ℝ)
    {Ω : Set P} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ F Ω) {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {ε : ℝ} (hε : 0 < ε) (hSub : closedBall (0 : ℝ) ε ×ˢ K ⊆ Ω)
    (h0 : ∀ y ∈ K, F (0, y) = G y)
    (hSupport : ∀ t ∈ ball (0 : ℝ) ε, ∀ y ∈ U \ K, F (t, y) = G y) :
    HasDerivAt (fun t => ∫ y in U, F (t, y) - G y)
      (∫ y in K, fderiv ℝ F (0, y) (1, 0)) 0 := by
  have hF0 : IntegrableOn (fun y => F (0, y)) K (volume : Measure E) :=
    (continuousOn_parameterSlice_compact F hf.continuousOn 0
      (fun _ hy => hSub ⟨mem_closedBall_self hε.le, hy⟩)).integrableOn_compact hK
  have hG : IntegrableOn G K := by
    refine hF0.congr ?_
    filter_upwards [ae_restrict_mem (μ := (volume : Measure E)) hK.measurableSet] with y hy
    exact h0 y hy
  have hNear : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ ball (0 : ℝ) ε := ball_mem_nhds 0 hε
  have heq : (fun t => ∫ y in U, F (t, y) - G y) =ᶠ[𝓝 (0 : ℝ)]
      fun t => (∫ y in K, F (t, y)) - ∫ y in K, G y := by
    filter_upwards [hNear] with t ht
    have hFI : IntegrableOn (fun y => F (t, y)) K (volume : Measure E) :=
      (continuousOn_parameterSlice_compact F hf.continuousOn t
        (fun _ hy => hSub ⟨ball_subset_closedBall ht, hy⟩)).integrableOn_compact hK
    rw [setIntegral_eq_on_compact_support _ hU.measurableSet hK.measurableSet hKU
      (fun y hy => sub_eq_zero.mpr (hSupport t ht y hy)), integral_sub hFI hG]
  exact ((hasDerivAt_integral_compact_parameter F hΩ hf hK hε hSub).sub_const _).congr_of_eventuallyEq heq

private theorem contDiffOn_metricActionDensity_metricAffineVariation_joint (g h : E → Mat)
    {U : Set E} (hU : IsOpen U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U) :
    ContDiffOn ℝ ∞ (fun z : P =>
      metricActionDensity (metricAffineVariation g h z.1 z.2)
        (coordinateJet (metricAffineVariation g h z.1) z.2)) (nonsingularVariationDomain g h U) := by
  let k (z : P) := metricAffineVariation g h z.1
  let C (z : P) := coordinateConnectionFromMetric (k z) z.2
  have hΓ := contDiffOn_coordinateConnection_metricAffineVariation_joint g h hU hg hh
  have hW := contDiffOn_inverseMetricDensity_metricAffineVariation_joint g h hg hh
  have hQ (b c : Index) : ContDiffOn ℝ ∞ (fun z : P => quadraticDifference (C z) b c)
      (nonsingularVariationDomain g h U) := by
    unfold quadraticDifference
    exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun e _ =>
      ((hΓ a a e).mul (hΓ e b c)).sub ((hΓ a c e).mul (hΓ e b a))
  have hSum : ContDiffOn ℝ ∞ (fun z : P => ∑ b, ∑ c,
      inverseMetricDensity (k z) z.2 b c * quadraticDifference (C z) b c)
      (nonsingularVariationDomain g h U) :=
    ContDiffOn.sum fun b _ => ContDiffOn.sum fun c _ => (hW b c).mul (hQ b c)
  refine hSum.congr ?_
  intro z _
  change metricActionDensity (k z z.2) (coordinateJet (k z) z.2) =
    ∑ b, ∑ c, inverseMetricDensity (k z) z.2 b c * quadraticDifference (C z) b c
  simp only [metricActionDensity, quadraticAction, C, coordinateConnectionFromMetric,
    inverseMetricDensity, Finset.mul_sum, mul_assoc]

/-- The exact first variation of the relative ΓΓ action is the spatial
integral of the existing coordinate Euler expression tested by the
same compact lower-metric variation. -/
theorem hasDerivAt_relativeGammaGammaAction_eq_integral_coordinateDensityEuler
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g h : E → ι → ℝ) {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (hn : ∀ y ∈ U, Matrix.det (assembleMetricComponents S (g y)) ≠ 0)
    (hSupport : ∀ y ∈ U \ K, h y = 0) :
    HasDerivAt (relativeGammaGammaAction (assembledCoordinateMetric S g) (assembledCoordinateMetric S h) U)
      (∫ y in K, ∑ i, h y i * coordinateDensityEuler S g y i) 0 := by
  let G := assembledCoordinateMetric S g
  let H := assembledCoordinateMetric S h
  let Ω := nonsingularVariationDomain G H U
  let F (z : P) := metricActionDensity (metricAffineVariation G H z.1 z.2)
    (coordinateJet (metricAffineVariation G H z.1) z.2)
  let L (y : E) := metricActionDensity (G y) (coordinateJet G y)
  let A (y : E) := ∑ i, h y i * coordinateDensityEuler S g y i
  let V := eulerVariationBoundaryVector S g h
  have hG0 : ContDiffOn ℝ ∞ G U := (assembleMetricComponents S).contDiff.comp_contDiffOn hg
  have hH0 : ContDiffOn ℝ ∞ H U := (assembleMetricComponents S).contDiff.comp_contDiffOn hh
  have hG (i j : Index) : ContDiffOn ℝ ∞ (fun y => G y i j) U :=
    contDiffOn_pi.mp (contDiffOn_pi.mp hG0 i) j
  have hH (i j : Index) : ContDiffOn ℝ ∞ (fun y => H y i j) U :=
    contDiffOn_pi.mp (contDiffOn_pi.mp hH0 i) j
  have hΩ : IsOpen Ω := isOpen_nonsingularVariationDomain G H hU hG hH
  have hF : ContDiffOn ℝ ∞ F Ω := contDiffOn_metricActionDensity_metricAffineVariation_joint G H hU hG hH
  have h0 (y : E) (hy : y ∈ K) : (0, y) ∈ Ω :=
    zero_mem_nonsingularVariationDomain G H y (hKU hy) (hn y (hKU hy))
  have hInit : ({0} : Set ℝ) ×ˢ K ⊆ Ω := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have ht' : t = 0 := ht
    subst t
    exact h0 y hy
  obtain ⟨I, W, hI, _, h0I, hKW, hIW⟩ := generalized_tube_lemma isCompact_singleton hK hΩ hInit
  obtain ⟨ε, hε, hIε⟩ := nhds_basis_closedBall.mem_iff.mp (hI.mem_nhds (h0I (mem_singleton 0)))
  have hSub : closedBall (0 : ℝ) ε ×ˢ K ⊆ Ω := (Set.prod_mono hIε hKW).trans hIW
  have hL (y : E) : F (0, y) = L y := by simp only [F, L, metricAffineVariation_zero]
  have hOff (t : ℝ) (y : E) (hy : y ∈ U \ K) : F (t, y) = L y := by
    have heq : metricAffineVariation G H t =ᶠ[𝓝 y] G := by
      filter_upwards [(hU.sdiff hK.isClosed).mem_nhds hy] with x hx
      have hH0 : H x = 0 := by simp only [H, assembledCoordinateMetric, hSupport x hx, map_zero]
      simp only [metricAffineVariation, hH0, smul_zero, add_zero]
    simp only [F, L, heq.self_of_nhds, coordinateJet_eq_of_eventuallyEq heq]
  have hAct := hasDerivAt_relative_integral_compact_parameter F L hΩ hF hU hK hKU hε hSub
    (fun y _ => hL y) (fun t _ y hy => hOff t y hy)
  have hV := integrableOn_and_integral_coordinateDivergence_eq_zero hU hK hKU V
    (contDiffOn_eulerVariationBoundaryVector S g h hU hg hh hn) (fun y hy a => by
      simp only [V, eulerVariationBoundaryVector, hSupport y hy, Pi.zero_apply, zero_mul, Finset.sum_const_zero])
  have hDeriv (y : E) (hy : y ∈ K) :
      fderiv ℝ F (0, y) (1, 0) = A y + coordinateDivergence V y := by
    have ht := hasDerivAt_parameterSlice F 0 y
      ((hF.contDiffAt (hΩ.mem_nhds (h0 y hy))).differentiableAt (by simp))
    have hgD := (hg.contDiffAt (hU.mem_nhds (hKU hy))).differentiableAt (by simp)
    have hhD := (hh.contDiffAt (hU.mem_nhds (hKU hy))).differentiableAt (by simp)
    have he := hasDerivAt_metricActionDensity_assembledAffineVariation S g h y hgD hhD (hn y (hKU hy))
    exact (ht.unique he).trans
      (coordinateWeakActionVariation_eq_coordinateDensityEuler_add_divergence S g h hU hg hh hn y (hKU hy))
  have hFDeriv : ContDiffOn ℝ ∞ (fderiv ℝ F) Ω := hF.fderiv_of_isOpen hΩ (by simp)
  let hDf (z : P) := fderiv ℝ F z (1, 0)
  have hDfCont : ContinuousOn hDf Ω := (hFDeriv.clm_apply contDiffOn_const).continuousOn
  have hDfInt : IntegrableOn (fun y => hDf (0, y)) K (volume : Measure E) :=
    (continuousOn_parameterSlice_compact hDf hDfCont 0 h0).integrableOn_compact hK
  have hAi : IntegrableOn A K := by
    refine (hDfInt.sub hV.1).congr ?_
    filter_upwards [ae_restrict_mem (μ := (volume : Measure E)) hK.measurableSet] with y hy
    change fderiv ℝ F (0, y) (1, 0) - coordinateDivergence V y = A y
    rw [hDeriv y hy, add_sub_cancel_right]
  refine hAct.congr_deriv ?_
  have hDEq : EqOn (fun y => fderiv ℝ F (0, y) (1, 0)) (fun y => A y + coordinateDivergence V y) K :=
    fun y hy => hDeriv y hy
  rw [setIntegral_congr_fun hK.measurableSet hDEq, integral_add hAi hV.1, hV.2, add_zero]

private theorem assembledCoordinateMetric_symmetric {ι : Type*} [Fintype ι] (S : ι → Mat)
    (hS : ∀ i, IsSymmetricTensor (S i)) (g : E → ι → ℝ) (x : E) :
    IsSymmetricTensor (assembledCoordinateMetric S g x) := by
  intro a b
  simp only [assembledCoordinateMetric, assembleMetricComponents_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun r => g x i * r) (hS i a b)

/-- The actual Euler expression pairs to zero against each compact
coordinate test when the assembled metric is genuinely Ricci flat. -/
theorem integral_coordinateDensityEuler_eq_zero_of_coordinateVacuum
    {ι : Type*} [Fintype ι] (S : ι → Mat) (hS : ∀ i, IsSymmetricTensor (S i))
    (g h : E → ι → ℝ) {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (hn : ∀ y ∈ U, Matrix.det (assembleMetricComponents S (g y)) ≠ 0)
    (hSupport : ∀ y ∈ U \ K, h y = 0)
    (hVac : ∀ y ∈ U, ∀ b c, coordinateRicci
        (coordinateConnectionFromMetric (assembledCoordinateMetric S g)) y b c = 0) :
    (∫ y in K, ∑ i, h y i * coordinateDensityEuler S g y i) = 0 := by
  let G := assembledCoordinateMetric S g
  let H := assembledCoordinateMetric S h
  have hG0 : ContDiffOn ℝ ∞ G U := (assembleMetricComponents S).contDiff.comp_contDiffOn hg
  have hH0 : ContDiffOn ℝ ∞ H U := (assembleMetricComponents S).contDiff.comp_contDiffOn hh
  have hG (i j : Index) : ContDiffOn ℝ ∞ (fun y => G y i j) U :=
    contDiffOn_pi.mp (contDiffOn_pi.mp hG0 i) j
  have hH (i j : Index) : ContDiffOn ℝ ∞ (fun y => H y i j) U :=
    contDiffOn_pi.mp (contDiffOn_pi.mp hH0 i) j
  have hSupportH (y : E) (hy : y ∈ U \ K) : H y = 0 := by
    simp only [H, assembledCoordinateMetric, hSupport y hy, map_zero]
  have hStationary := (hasDerivAt_relative_actions_of_coordinateVacuum G H hU hK hKU hG hH
    (fun y _ => assembledCoordinateMetric_symmetric S hS g y)
    (fun y _ => assembledCoordinateMetric_symmetric S hS h y) hn hSupportH hVac).2
  exact (hasDerivAt_relativeGammaGammaAction_eq_integral_coordinateDensityEuler
    S g h hU hK hKU hg hh hn hSupport).unique hStationary

end Burnett.V03.Palatini
