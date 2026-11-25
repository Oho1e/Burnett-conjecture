import Burnett.Analysis.BaseMarginal.IntrinsicBaseMarginal

/-! Smooth compact tests determine integrable signed densities almost everywhere. -/
set_option autoImplicit false
set_option maxRecDepth 4500
set_option maxHeartbeats 3300000

noncomputable section
namespace Burnett.F08.IntrinsicBaseMarginal

open Set MeasureTheory Filter Burnett.Geometry ConnectionDifference ManifoldMetric
open scoped ContDiff Manifold ENNReal

open private measure_eq_of_smooth_compact_tests from Burnett.Analysis.BaseMarginal.IntrinsicBaseMarginal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

theorem ae_eq_zero_of_integrable_mul_smooth_compact_tests (μ : Measure M) [IsLocallyFiniteMeasure μ]
    (F : M → ℝ) (hF : Integrable F μ)
    (hTest : ∀ φ : M → ℝ, ContMDiff Model 𝓘(ℝ) ∞ φ → HasCompactSupport φ →
      Integrable (fun x => φ x * F x) μ ∧ (∫ x, φ x * F x ∂μ) = 0) : F =ᵐ[μ] 0 := by
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace CoordinateSpace M
  let P (x : M) : ℝ := max (F x) 0
  let N (x : M) : ℝ := max (-F x) 0
  let p (x : M) := ENNReal.ofReal (P x)
  let q (x : M) := ENNReal.ofReal (N x)
  have hP : Integrable P μ := hF.sup (integrable_zero M ℝ μ)
  have hN : Integrable N μ := hF.neg.sup (integrable_zero M ℝ μ)
  have hp : AEMeasurable p μ := ENNReal.continuous_ofReal.measurable.comp_aemeasurable hP.1.aemeasurable
  have hq : AEMeasurable q μ := ENNReal.continuous_ofReal.measurable.comp_aemeasurable hN.1.aemeasurable
  have hPn (x : M) : 0 ≤ P x := le_max_right _ _
  have hNn (x : M) : 0 ≤ N x := le_max_right _ _
  have hParts (x : M) : P x - N x = F x := by
    by_cases h : 0 ≤ F x
    · simp only [P, N, max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · have h' : F x ≤ 0 := (lt_of_not_ge h).le
      simp only [P, N, max_eq_right h', max_eq_left (neg_nonneg.mpr h'), zero_sub, neg_neg]
  let νP := μ.withDensity p
  let νN := μ.withDensity q
  letI : IsFiniteMeasure νP := ⟨by
    rw [withDensity_apply p MeasurableSet.univ, Measure.restrict_univ]
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hPn)).mp hP.2⟩
  letI : IsFiniteMeasure νN := ⟨by
    rw [withDensity_apply q MeasurableSet.univ, Measure.restrict_univ]
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hNn)).mp hN.2⟩
  have hMeasure : νP = νN := by
    apply measure_eq_of_smooth_compact_tests
    intro φ hφ hc
    obtain ⟨hInt, hZero⟩ := hTest φ hφ hc
    have hf := hφ.continuous.aestronglyMeasurable (μ := μ)
    have hMint (G : M → ℝ) (hG : Integrable G μ) (h0 : ∀ x, 0 ≤ G x) (hA : ∀ x, G x ≤ |F x|) :
        Integrable (fun x => φ x * G x) μ := by
      apply hInt.norm.mono' (hf.mul hG.1)
      exact Eventually.of_forall fun x => by
        change ‖φ x * G x‖ ≤ ‖φ x * F x‖
        simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h0 x)]
        exact mul_le_mul_of_nonneg_left (hA x) (abs_nonneg _)
    have hIP := hMint P hP hPn (fun x => max_le (le_abs_self _) (abs_nonneg _))
    have hIN := hMint N hN hNn (fun x => max_le (neg_le_abs _) (abs_nonneg _))
    rw [integral_withDensity_eq_integral_toReal_smul₀ hp
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) φ,
      integral_withDensity_eq_integral_toReal_smul₀ hq (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) φ]
    simp only [p, q, ENNReal.toReal_ofReal (hPn _), ENNReal.toReal_ofReal (hNn _), smul_eq_mul]
    apply sub_eq_zero.mp
    calc
      _ = (∫ x, φ x * P x ∂μ) - ∫ x, φ x * N x ∂μ := by simp only [mul_comm]
      _ = ∫ x, φ x * F x ∂μ := by
        rw [← integral_sub hIP hIN]
        exact integral_congr_ae (Eventually.of_forall fun x => by
          change φ x * P x - φ x * N x = φ x * F x
          rw [← mul_sub, hParts])
      _ = 0 := hZero
  have hAE := (withDensity_eq_iff_of_sigmaFinite hp hq).mp hMeasure
  filter_upwards [hAE] with x hx
  have h := congrArg ENNReal.toReal hx
  change (ENNReal.ofReal (P x)).toReal = (ENNReal.ofReal (N x)).toReal at h
  rw [ENNReal.toReal_ofReal (hPn x), ENNReal.toReal_ofReal (hNn x)] at h
  exact (hParts x).symm.trans (sub_eq_zero.mpr h)

end Burnett.F08.IntrinsicBaseMarginal
