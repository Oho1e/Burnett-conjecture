import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichBaseIntegrand
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichFrequency
import Burnett.Analysis.PrincipalEnergy.Localization.ProductPartialJets
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option maxHeartbeats 2900000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Metric Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff FourierTransform Topology

private theorem contDiff_sandwichBaseIntegrand_pair {a : Space → Space → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (χ : SchwartzMap Space ℂ) (ξ : Space) :
    ContDiff ℝ ∞ (fun p : Space × Space => sandwichBaseIntegrand a χ ξ p.2 p.1) := by
  let F := SchwartzMap.fourierTransformCLM ℂ χ
  have hF : ContDiff ℝ ∞ (fun p : Space × Space => F p.2) := (F.smooth ⊤).comp contDiff_snd
  have hCut : ContDiff ℝ ∞ (fun p : Space × Space => χ p.1) := (χ.smooth ⊤).comp contDiff_fst
  have hPhase : ContDiff ℝ ∞ (fun p : Space × Space => (Real.fourierChar (inner ℝ p.2 p.1) : ℂ)) := by
    simp only [Real.fourierChar_apply]
    have hInner : ContDiff ℝ ∞ (fun p : Space × Space => inner ℝ p.2 p.1) :=
      contDiff_snd.inner ℝ contDiff_fst
    have hArg : ContDiff ℝ ∞ (fun p : Space × Space => 2 * Real.pi * inner ℝ p.2 p.1) :=
      contDiff_const.mul hInner
    exact ((Complex.ofRealCLM.contDiff.comp hArg).mul contDiff_const).cexp
  have hTranslate : ContDiff ℝ ∞ (fun p : Space × Space => ξ + p.2) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space × Space => ξ)).add contDiff_snd
  have hA : ContDiff ℝ ∞ (fun p : Space × Space => a p.1 (ξ + p.2)) :=
    ha.comp (contDiff_fst.prodMk hTranslate)
  exact hF.mul ((hCut.mul hPhase).mul hA)

private theorem cutoffSandwichSymbol_pureBase_jets {a : Space → Space → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a))
    (hPure : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (χ : SchwartzMap Space ℂ) (ξ : Space) :
    ContDiff ℝ ∞ (fun x => cutoffSandwichSymbol a χ x ξ) ∧ ∀ (n : ℕ) x,
      iteratedFDeriv ℝ n (fun y => cutoffSandwichSymbol a χ y ξ) x =
        ∫ η, iteratedFDeriv ℝ n (sandwichBaseIntegrand a χ ξ η) x := by
  let U := sandwichBaseIntegrand a χ ξ
  have hJoint : ContDiff ℝ ∞ (fun p : Space × Space => U p.2 p.1) :=
    contDiff_sandwichBaseIntegrand_pair ha χ ξ
  have hSmooth (η : Space) : ContDiff ℝ ∞ (U η) := by
    let Φ (y : Space) := (Real.fourierChar (inner ℝ η y) : ℂ)
    have hΦ : ContDiff ℝ ∞ Φ := (fourier_phase_contDiff_and_derivative_bound η).1
    have pair : ContDiff ℝ ∞ (fun x : Space => (x, ξ + η)) :=
      (contDiff_id : ContDiff ℝ ∞ (id : Space → Space)).prodMk contDiff_const
    have hb : ContDiff ℝ ∞ (fun x => a x (ξ + η)) := ha.comp pair
    change ContDiff ℝ ∞ (fun y => 𝓕 (χ : Space → ℂ) η • ((χ y * Φ y) * a y (ξ + η)))
    exact (((χ.smooth ⊤).mul hΦ).mul hb).const_smul _
  have hMeas (n : ℕ) (x : Space) :
      AEStronglyMeasurable (fun η => iteratedFDeriv ℝ n (U η) x) (volume : Measure Space) := by
    have jets : ContDiff ℝ ∞ (fun p : Space × Space => iteratedFDeriv ℝ n (U p.2) p.1) :=
      contDiff_firstPartialJet hJoint n
    have pair : Continuous (fun η : Space => (x, η)) := continuous_const.prodMk continuous_id
    letI : SecondCountableTopologyEither Space (ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ) :=
      secondCountableTopologyEither_of_left _ _
    change AEStronglyMeasurable
      ((fun p : Space × Space => iteratedFDeriv ℝ n (U p.2) p.1) ∘ (fun η : Space => (x, η))) volume
    exact (jets.continuous.comp pair).aestronglyMeasurable
  have hDom (n : ℕ) (x : Space) : ∃ B : Space → ℝ, Integrable B (volume : Measure Space) ∧
      ∀ η y, y ∈ ball x 1 → ‖iteratedFDeriv ℝ n (U η) y‖ ≤ B η := by
    obtain ⟨C, _, hC⟩ := exists_sandwichBaseIntegrand_derivative_bound ha hPure χ n
    let F := SchwartzMap.fourierTransformCLM ℂ χ
    exact ⟨fun η => C * (1 + ‖ξ‖) * ((1 + ‖η‖)^(n + 1) * ‖F η‖),
      (integrable_schwartz_weighted F (n + 1)).const_mul _, fun η y _ => hC y ξ η⟩
  rw [show (fun x => cutoffSandwichSymbol a χ x ξ) = (fun x => ∫ η, U η x) from
    funext fun x => cutoffSandwichSymbol_eq_baseIntegral a χ x ξ]
  exact contDiff_integral_of_locally_dominated_jets (volume : Measure Space) U hSmooth hMeas hDom

/-- The genuine sandwich symbol has a common compact base and retains all the
pure base order-one seminorms of the original smooth symbol. -/
theorem cutoffSandwichSymbol_compactBaseOrderOne {a : Space → Space → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a))
    (hPure : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (χ : SchwartzMap Space ℂ) (hχ : HasCompactSupport (χ : Space → ℂ)) :
    CompactBaseOrderOne (cutoffSandwichSymbol a χ) := by
  refine ⟨⟨tsupport (χ : Space → ℂ), hχ, cutoffSandwichSymbol_base_support χ⟩,
    fun ξ => (cutoffSandwichSymbol_pureBase_jets ha hPure χ ξ).1, ?_⟩
  intro n
  obtain ⟨C, hC, bound⟩ := exists_sandwichBaseIntegrand_derivative_bound ha hPure χ n
  let F := SchwartzMap.fourierTransformCLM ℂ χ
  let w (η : Space) := (1 + ‖η‖)^(n + 1) * ‖F η‖
  have hW : Integrable w (volume : Measure Space) := integrable_schwartz_weighted F (n + 1)
  have hIW : 0 ≤ ∫ η, w η := integral_nonneg (fun η => by dsimp only [w]; positivity)
  refine ⟨C * (∫ η, w η), mul_nonneg hC hIW, fun x ξ => ?_⟩
  rw [(cutoffSandwichSymbol_pureBase_jets ha hPure χ ξ).2]
  calc
    _ ≤ ∫ η, (C * (1 + ‖ξ‖)) * w η :=
      norm_integral_le_of_norm_le (hW.const_mul _) (Eventually.of_forall fun η => bound x ξ η)
    _ = _ := by rw [integral_const_mul]; ring

/-- Joint continuity of the same exact sandwich symbol. The zeroth growth
bound gives a joint locally integrable majorant for the Fourier integral. -/
theorem cutoffSandwichSymbol_jointContinuous {a : Space → Space → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a))
    (hPure : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (χ : SchwartzMap Space ℂ) : Continuous (uncurry (cutoffSandwichSymbol a χ)) := by
  let U (p : Space × Space) (η : Space) := sandwichBaseIntegrand a χ p.2 η p.1
  rw [show uncurry (cutoffSandwichSymbol a χ) = fun p => ∫ η, U p η from
    funext fun p => cutoffSandwichSymbol_eq_baseIntegral a χ p.1 p.2]
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨C, hC, bound⟩ := exists_sandwichBaseIntegrand_derivative_bound ha hPure χ 0
  let F := SchwartzMap.fourierTransformCLM ℂ χ
  let w (η : Space) := (1 + ‖η‖)^((0 : ℕ) + 1) * ‖F η‖
  have wh : Integrable w (volume : Measure Space) := integrable_schwartz_weighted F (0 + 1)
  have measurable (q : Space × Space) : AEStronglyMeasurable (U q) (volume : Measure Space) :=
    ((contDiff_sandwichBaseIntegrand_pair ha χ q.2).continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have nearby : ∀ᶠ q : Space × Space in 𝓝 p, q.2 ∈ ball p.2 1 :=
    continuous_snd.continuousAt.eventually (ball_mem_nhds p.2 zero_lt_one)
  have local_bound : ∀ᶠ q in 𝓝 p, ∀ᵐ η ∂(volume : Measure Space),
      ‖U q η‖ ≤ (C * (2 + ‖p.2‖)) * w η := by
    filter_upwards [nearby] with q hq
    have hd : ‖q.2 - p.2‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hq
    have hq' : ‖q.2‖ ≤ 1 + ‖p.2‖ :=
      (by simpa only [sub_add_cancel] using norm_add_le (q.2 - p.2) p.2 :
        ‖q.2‖ ≤ ‖q.2 - p.2‖ + ‖p.2‖).trans (add_le_add_right hd.le _)
    exact Eventually.of_forall fun η => by
      have elem := bound q.1 q.2 η
      rw [norm_iteratedFDeriv_zero] at elem
      have elem' : ‖U q η‖ ≤ (C * (1 + ‖q.2‖)) * w η := elem
      exact elem'.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [hq']) hC) (by dsimp only [w]; positivity))
  have pointwise (η : Space) : Continuous (fun q : Space × Space => U q η) := by
    have hA : Continuous (fun q : Space × Space => a q.1 (q.2 + η)) :=
      ha.continuous.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
    have hPhase : Continuous (fun q : Space × Space => (Real.fourierChar (inner ℝ η q.1) : ℂ)) :=
      ((fourier_phase_contDiff_and_derivative_bound η).1.continuous).comp continuous_fst
    exact (((χ.continuous.comp continuous_fst).mul hPhase).mul hA).const_smul _
  exact continuousAt_of_dominated (Eventually.of_forall measurable) local_bound (wh.const_mul _)
    (Eventually.of_forall fun η => (pointwise η).continuousAt)

end Burnett.Analysis.CarlesonEmbedding
