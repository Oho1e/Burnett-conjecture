import Burnett.Analysis.TransportWard.Weyl.ActualWindowedEulerRemainder
import Burnett.Analysis.TransportWard.Weyl.CompactMetricSegment
import Burnett.Analysis.TransportWard.Weyl.OriginalNormalizedChartJetBounds
import Burnett.Analysis.TransportWard.Weyl.NormalizedWeylPerturbationBounds
import Burnett.Analysis.TransportWard.Weyl.WeylCompactMatrixPair

set_option autoImplicit false
set_option maxHeartbeats 5400000
set_option maxRecDepth 4400

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Metric Set Function Burnett.A03 Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.CarlesonEmbedding
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped BigOperators ComplexConjugate ContDiff Matrix.Norms.Elementwise Manifold Topology

open private contDiffOn_coordinateMetricFirstJet from Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet
open private contDiffOn_coordinateMetricSecondJet from Burnett.Analysis.TransportWard.Weyl.EulerAffineRegularity

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot

private theorem norm_fderiv_cutoff_bounded (χ : D) :
    ∃ W : ℝ, 0 ≤ W ∧ (∀ x : E₀, ‖(χ : E₀ → ℝ) x‖ ≤ W) ∧
      ∀ x : E₀, ‖fderiv ℝ (χ : E₀ → ℝ) x‖ ≤ W := by
  let ρ := (χ : E₀ → ℝ)
  have hρ := test_smooth χ
  have hρc := test_compactSupport χ
  let K := tsupport ρ ∪ tsupport (fderiv ℝ ρ)
  have hK : IsCompact K := hρc.union (HasCompactSupport.fderiv ℝ hρc)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hρ.continuous.continuousOn
  obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn (hρ.continuous_fderiv (by simp)).continuousOn
  let W := max 0 (max M N)
  have hW : 0 ≤ W := le_max_left _ _
  refine ⟨W, hW, fun x => ?_, fun x => ?_⟩
  · by_cases hx : x ∈ K
    · exact (hM x hx).trans ((le_max_left M N).trans (le_max_right 0 _))
    · change ‖ρ x‖ ≤ W
      rw [image_eq_zero_of_notMem_tsupport (fun hy => hx (Or.inl hy)), norm_zero]
      exact hW
  · by_cases hx : x ∈ K
    · exact (hN x hx).trans ((le_max_right M N).trans (le_max_right 0 _))
    · rw [image_eq_zero_of_notMem_tsupport (fun hy => hx (Or.inr hy)), norm_zero]
      exact hW

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The chart bounds in the true tested Taylor limit follow from the original
geometric compact convergence, derivative control and one fixed cutoff. -/
theorem tendsto_originalNormalizedWindowedWeylEulerRemainder
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hSym : ∀ n, IsSymmetric (g n)) (hconv : LocallyUniformlyConverges r g B)
    (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : M) (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ (chartAt E₀ c).target)
    (θ : E₀ → ℝ) (β : E₀ → E₀ → ℂ) (R : ℝ)
    (ha : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hA : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hΘβ : ∀ x ξ, β x ξ ≠ 0 → θ x = 1) (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β)) (hReal : ∀ x ξ, conj (β x ξ) = β x ξ)
    (hPlateau : ∀ x ∈ tsupport θ, (χ : E₀ → ℝ) =ᶠ[𝓝 x] fun _ => 1) :
    let U := (chartAt E₀ c).target
    let S := orthonormalMetricDirection
    let b := normalizedChartMetric B c
    let h (n : ℕ) := normalizedChartPerturbation B (g n) c
    let F (n : ℕ) (i : I) := (symmetricMetricScale i : ℂ) •
      fixedWeylPerturbationSchwartz B g hB hg (AtlasChart.atPoint c) χ hχ n i.val
    let p := windowedWeylLeftSymbol θ β R ha
    Tendsto (fun n => 2 * (∫ x in U, ∑ i, conj (firstOrderAction p (F n i) x) *
      (quadraticPathRemainder (fun t => coordinateDensityEuler S (fun y => b y + t • h n y) x i) : ℂ)).im)
      atTop (𝓝 0) := by
  intro U S b h F p
  let ρ := (χ : E₀ → ℝ)
  have hρ := test_smooth χ
  have hρc := test_compactSupport χ
  let c₀ := AtlasChart.atPoint c
  obtain ⟨d, hd, hSub⟩ := hρc.exists_cthickening_subset_open (chartAt E₀ c).open_target hχ
  let J := cthickening d (tsupport ρ)
  let V := thickening d (tsupport ρ)
  have hJ : IsCompact J := hρc.cthickening
  have hV : IsOpen V := isOpen_thickening
  have hρV : tsupport ρ ⊆ V := self_subset_thickening hd _
  have hVJ : V ⊆ J := thickening_subset_cthickening _ _
  have hJU : J ⊆ U := hSub
  have hVU : V ⊆ U := hVJ.trans hJU
  have hθV : tsupport θ ⊆ V := fun x hx => hρV (subset_tsupport ρ (by
    change (χ : E₀ → ℝ) x ≠ 0
    rw [(hPlateau x hx).self_of_nhds]
    exact one_ne_zero))
  have hbU : ContDiffOn ℝ ∞ b U := contDiffOn_normalizedChartMetric B hB c
  have hhU (n : ℕ) : ContDiffOn ℝ ∞ (h n) U :=
    (contDiffOn_normalizedChartMetric (g n) (hg n) c).sub hbU
  let L := assembleMetricComponents S
  let G := L ∘ b
  let H (n : ℕ) := L ∘ h n
  have hG : ContDiffOn ℝ ∞ G U := L.contDiff.comp_contDiffOn hbU
  have hH (n : ℕ) : ContDiffOn ℝ ∞ (H n) U := L.contDiff.comp_contDiffOn (hhU n)
  have hGm : G = metricComponents (coordinateBilinear B c) :=
    assembledCoordinateMetric_orthonormalMetricComponents B hSig.isSymmetric c
  have hDet (x : E₀) (hx : x ∈ J) : G x ∈ nonsingularMetricDomain := by
    change (G x).det ≠ 0
    rw [hGm]
    exact ManifoldVolumeRegularity.coordinate_det_ne_zero B hSig.isNondegenerate c (hJU hx)
  have hHe (n : ℕ) (x : E₀) (hx : x ∈ U) : H n x =
      metricComponents (fixedForm (g n) c₀) x - metricComponents (fixedForm B c₀) x := by
    change L (normalizedChartMetric (g n) c x - normalizedChartMetric B c x) = _
    rw [map_sub, fixedForm_eq_preferred_components (g n) c hx, fixedForm_eq_preferred_components B c hx]
    exact congrArg₂ (· - ·)
      (congrFun (assembledCoordinateMetric_orthonormalMetricComponents (g n) (hSym n) c) x)
      (congrFun hGm x)
  have hUniform : TendstoUniformlyOn H (fun _ => 0) atTop J := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp
      (fixed_components_uniform_of_physical_C0loc r g B hconv c₀ J hJ hJU) ε hε] with n hn
    intro x hx
    rw [dist_zero_left, hHe n x (hJU hx), ← dist_eq_norm, dist_comm]
    exact hn x hx
  obtain ⟨K, hK, hKdet, hSeg⟩ := exists_eventually_compact_nonsingular_fieldSegments hJ G
    (hG.continuousOn.mono hJU) hDet H hUniform
  obtain ⟨ε, hε, hεlim, hSmall⟩ := exists_compact_uniform_zero_norm_modulus hJ H
    (fun n => (hH n).continuousOn.mono hJU) hUniform
  obtain ⟨N, hN⟩ := eventually_atTop.mp hSeg
  obtain ⟨C₁, D₁, hC₁, hD₁, hHfirst, hHder⟩ := exists_originalNormalizedChartPerturbation_derivative_bounds
    r B g hB hg hSig.isNondegenerate hconv hb c hJ hJU
  obtain ⟨W, hW, hW₀, hW₁⟩ := norm_fderiv_cutoff_bounded χ
  have hGder : ContDiffOn ℝ ∞ (fderiv ℝ G) U :=
    hG.fderiv_of_isOpen (chartAt E₀ c).open_target (by simp)
  obtain ⟨P, hP⟩ := hJ.exists_bound_of_continuousOn (hGder.continuousOn.mono hJU)
  obtain ⟨P₁, hP₁⟩ := hJ.exists_bound_of_continuousOn
    ((continuousOn_pi.mpr fun s : ActionSlot I =>
      (contDiffOn_coordinateMetricFirstJet (chartAt E₀ c).open_target b hbU s).continuousOn).mono hJU)
  obtain ⟨P₂, hP₂⟩ := hJ.exists_bound_of_continuousOn
    ((continuousOn_pi.mpr fun a : Fin 4 => continuousOn_pi.mpr fun s : ActionSlot I =>
      (contDiffOn_coordinateMetricSecondJet (chartAt E₀ c).open_target b hbU a s).continuousOn).mono hJU)
  choose T hT using fun i => (exists_original_normalizedWeylPerturbation_bounds
    r B g hB hg hSig.isNondegenerate hconv hb c₀ χ hχ i).1
  let f (n : ℕ) := chartMetricCutoffTest hV (h n) ((hhU n).mono hVU) ρ hρ hρV hρc
  have hf (n : ℕ) (i : I) : (f n).val i = F n i := by
    have he := normalizedChartCutoffTest_eq_weylPerturbation B g hB hg c χ hχ n i (hhU n)
    trans (chartMetricCutoffTest (chartAt E₀ c).open_target (h n) (hhU n) ρ hρ hχ hρc).val i
    · ext x
      rfl
    · exact he
  let T₀ := Real.sqrt (∑ i, (T i) ^ 2)
  have hF (n : ℕ) : compactMatrixCoordinateH1 (f n) ≤ T₀ :=
    compactMatrixCoordinateH1_le_of_component_schwartzH1Energy (f n) T (fun i => by rw [hf]; exact hT i n)
  have hTail := tendsto_actualWindowedWeylEulerRemainder_of_chartBounds θ β R ha hA hΘβ hθ hθc hβ hReal
    S hV b (fun n => h (n + N)) (hbU.mono hVU) (fun n => (hhU (n + N)).mono hVU)
    ρ hρ hρV hρc hPlateau hK hKdet (fun n => ε (n + N)) (fun n => hε (n + N))
    ((tendsto_add_atTop_iff_nat N).mpr hεlim) W (max P 0) D₁ (max P₁ 0) C₁ (max P₂ 0) T₀
    hW (le_max_right _ _) hD₁ (le_max_right _ _) hC₁ (le_max_right _ _) (Real.sqrt_nonneg _)
    hW₀ hW₁ (fun n x hx => hN (n + N) (Nat.le_add_left N n) x (hVJ hx))
    (fun n x hx => hSmall (n + N) x (hVJ hx))
    (fun x hx => (hP x (hVJ hx)).trans (le_max_left _ _))
    (fun n x hx => hHder (n + N) x (hVJ hx))
    (fun x hx s => (norm_le_pi_norm _ s).trans ((hP₁ x (hVJ (hθV hx))).trans (le_max_left _ _)))
    (fun n x hx => hHfirst (n + N) x (hVJ (hθV hx)))
    (fun x hx a s => ((norm_le_pi_norm _ s).trans (norm_le_pi_norm _ a)).trans
      ((hP₂ x (hVJ (hθV hx))).trans (le_max_left _ _)))
    (fun n => hF (n + N))
  apply (tendsto_add_atTop_iff_nat N).mp
  refine hTail.congr (fun n => ?_)
  let R₀ (x : E₀) (i : I) : ℝ := quadraticPathRemainder (fun t => coordinateDensityEuler S
    (fun y => b y + t • h (n + N) y) x i)
  change 2 * (∫ x in V, ∑ i, conj (firstOrderAction p ((f (n + N)).val i) x) * (R₀ x i : ℂ)).im =
    2 * (∫ x in U, ∑ i, conj (firstOrderAction p (F (n + N) i) x) * (R₀ x i : ℂ)).im
  simp only [hf]
  congr 2
  rw [← integral_indicator hV.measurableSet, ← integral_indicator (chartAt E₀ c).open_target.measurableSet]
  apply integral_congr_ae
  exact .of_forall fun x => by
    by_cases hx : x ∈ V
    · rw [indicator_of_mem hx, indicator_of_mem (hVU hx)]
    · rw [indicator_of_notMem hx]
      by_cases hU : x ∈ U
      · rw [indicator_of_mem hU]
        have h0 (i : I) : firstOrderAction p (F (n + N) i) x = 0 :=
          windowedWeyl_leftAction_eq_zero_of_cutoffs θ β R ha _ x
            (Or.inl (image_eq_zero_of_notMem_tsupport (fun ht => hx (hθV ht))))
        simp only [h0, map_zero, zero_mul, Finset.sum_const_zero]
      · rw [indicator_of_notMem hU]

end Burnett.V03.Palatini
