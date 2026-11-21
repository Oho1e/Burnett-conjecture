import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichFrequency
import Burnett.Analysis.PrincipalEnergy.Localization.FourierPhaseJets
import Burnett.Analysis.PrincipalEnergy.Localization.ProductPartialJets
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff FourierTransform

private theorem norm_fderiv_complex_smul_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    {f : Space → ℂ} {g : Space → F} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y => f y • g y) x‖ ≤ ‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖ := by
  letI : NormedSpace ℂ (Space →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  have hR : ‖(fderiv ℝ f x).smulRight (g x)‖ ≤ ‖fderiv ℝ f x‖ * ‖g x‖ := by
    refine ((fderiv ℝ f x).smulRight (g x)).opNorm_le_bound (by positivity) fun y => ?_
    rw [ContinuousLinearMap.smulRight_apply, norm_smul]
    exact (mul_le_mul_of_nonneg_right ((fderiv ℝ f x).le_opNorm y) (norm_nonneg _)).trans_eq (by ring)
  change ‖fderiv ℝ (f • g) x‖ ≤ _
  rw [fderiv_smul hf hg]
  exact (norm_add_le _ _).trans (add_le_add (by rw [norm_smul]) hR)

/-- Joint smoothness of the actual cutoff and phase factor. -/
theorem contDiff_sandwichFrequencyFactor (χ : SchwartzMap Space ℂ) :
    ContDiff ℝ ∞ (uncurry (sandwichFrequencyFactor χ)) := by
  let F := SchwartzMap.fourierTransformCLM ℂ χ
  have hCut : ContDiff ℝ ∞ (fun p : Space × Space => χ p.1) := (χ.smooth ⊤).comp contDiff_fst
  have hF : ContDiff ℝ ∞ (fun p : Space × Space => F p.2) := (F.smooth ⊤).comp contDiff_snd
  have hPhase : ContDiff ℝ ∞ (fun p : Space × Space => (Real.fourierChar (inner ℝ p.2 p.1) : ℂ)) := by
    simp only [Real.fourierChar_apply]
    have hInner : ContDiff ℝ ∞ (fun p : Space × Space => inner ℝ p.2 p.1) :=
      contDiff_snd.inner ℝ contDiff_fst
    have hArg : ContDiff ℝ ∞ (fun p : Space × Space => 2 * Real.pi * inner ℝ p.2 p.1) :=
      contDiff_const.mul hInner
    exact ((Complex.ofRealCLM.contDiff.comp hArg).mul contDiff_const).cexp
  exact (hCut.mul hPhase).mul hF

/-- Bounds for the actual cutoff factor and its first base derivative. -/
theorem sandwichFrequencyFactor_base_controls (χ : SchwartzMap Space ℂ) (x η : Space) :
    let S := SchwartzMap.seminorm ℝ 0 0 χ
    let T := SchwartzMap.seminorm ℝ 0 1 χ + S * (2 * Real.pi)
    let F := 𝓕 (χ : Space → ℂ) η
    ‖sandwichFrequencyFactor χ x η‖ ≤ S * ‖F‖ ∧
      ‖fderiv ℝ (fun y => sandwichFrequencyFactor χ y η) x‖ ≤ T * (1 + ‖η‖) * ‖F‖ := by
  intro S T F
  let Φ (y : Space) := (Real.fourierChar (inner ℝ η y) : ℂ)
  have hΦ : ContDiff ℝ ∞ Φ := (fourier_phase_contDiff_and_derivative_bound η).1
  have hOne : ‖Φ x‖ = 1 := Circle.norm_coe _
  have hVal : ‖χ x‖ ≤ S := SchwartzMap.norm_le_seminorm ℝ χ x
  have hDχ : ‖fderiv ℝ (χ : Space → ℂ) x‖ ≤ SchwartzMap.seminorm ℝ 0 1 χ := by
    calc
      _ = ‖iteratedFDeriv ℝ 0 (fderiv ℝ (χ : Space → ℂ)) x‖ := by rw [norm_iteratedFDeriv_zero]
      _ = ‖iteratedFDeriv ℝ 1 (χ : Space → ℂ) x‖ := norm_iteratedFDeriv_fderiv
      _ ≤ _ := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ χ 1 x
  have hDΦ : ‖fderiv ℝ Φ x‖ ≤ (2 * Real.pi) * ‖η‖ := by
    calc
      _ = ‖iteratedFDeriv ℝ 0 (fderiv ℝ Φ) x‖ := by rw [norm_iteratedFDeriv_zero]
      _ = ‖iteratedFDeriv ℝ 1 Φ x‖ := norm_iteratedFDeriv_fderiv
      _ ≤ _ := by simpa only [pow_one] using (fourier_phase_contDiff_and_derivative_bound η).2 1 x
  have hProd : ‖fderiv ℝ (fun y => χ y * Φ y) x‖ ≤ S * ((2 * Real.pi) * ‖η‖) +
      SchwartzMap.seminorm ℝ 0 1 χ := by
    calc
      _ ≤ ‖χ x‖ * ‖fderiv ℝ Φ x‖ + ‖fderiv ℝ (χ : Space → ℂ) x‖ * ‖Φ x‖ :=
        norm_fderiv_complex_smul_le χ.differentiableAt ((hΦ.differentiable (by simp)) x)
      _ ≤ _ := by
        rw [hOne, mul_one]
        exact add_le_add (mul_le_mul hVal hDΦ (norm_nonneg _) ((norm_nonneg _).trans hVal)) hDχ
  have he : (fun y => sandwichFrequencyFactor χ y η) = fun y => F • (χ y * Φ y) := by
    funext y
    simp only [sandwichFrequencyFactor, F, Φ, smul_eq_mul]
    ring
  have hp : DifferentiableAt ℝ (fun y => χ y * Φ y) x :=
    χ.differentiableAt.mul ((hΦ.differentiable (by simp)) x)
  constructor
  · change ‖(fun y => sandwichFrequencyFactor χ y η) x‖ ≤ _
    rw [he, norm_smul, norm_mul, hOne, mul_one]
    exact (mul_le_mul_of_nonneg_left hVal (norm_nonneg _)).trans_eq (mul_comm _ _)
  · rw [he, fderiv_fun_const_smul hp F, norm_smul]
    have hP : S * ((2 * Real.pi) * ‖η‖) + SchwartzMap.seminorm ℝ 0 1 χ ≤ T * (1 + ‖η‖) := by
      dsimp only [T]
      nlinarith only [(norm_nonneg _).trans hDχ,
        mul_nonneg ((norm_nonneg _).trans hDχ) (norm_nonneg η),
        mul_nonneg ((norm_nonneg _).trans hVal) (show 0 ≤ 2 * Real.pi by positivity)]
    exact (mul_le_mul_of_nonneg_left (hProd.trans hP) (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- Joint regularity of the frequency jet of the original symbol. -/
theorem contDiff_symbol_frequencyJet {a : Space → Space → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : Space × Space => iteratedFDeriv ℝ n (a p.1) p.2) := by
  have swap : ContDiff ℝ ∞ (fun p : Space × Space => a p.2 p.1) :=
    ha.comp (contDiff_snd.prodMk contDiff_fst)
  exact (contDiff_firstPartialJet swap n).comp (contDiff_snd.prodMk contDiff_fst)

/-- Uniform weighted bound of the actual first-base derivative after taking
the n-th frequency derivative inside the sandwich integral. -/
theorem exists_sandwichMixedIntegrand_derivative_bound {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (χ : SchwartzMap Space ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ η,
      ‖fderiv ℝ (fun y => sandwichFrequencyFactor χ y η • iteratedFDeriv ℝ n (a y) (ξ + η)) x‖ *
        (1 + ‖ξ‖)^n ≤ C * (1 + ‖ξ‖) *
          ((1 + ‖η‖)^(n + 2) * ‖𝓕 (χ : Space → ℂ) η‖) := by
  letI : NormedSpace ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ) :=
    ContinuousMultilinearMap.normedSpace'
  obtain ⟨A, hA, orderA⟩ := ha.frequency.order n
  obtain ⟨B, hB, orderB⟩ := ha.order n
  let S := SchwartzMap.seminorm ℝ 0 0 χ
  let T := SchwartzMap.seminorm ℝ 0 1 χ + S * (2 * Real.pi)
  have hS : 0 ≤ S := (norm_nonneg _).trans (SchwartzMap.norm_le_seminorm ℝ χ (0 : Space))
  have hT : 0 ≤ T := add_nonneg (((norm_nonneg _).trans (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ χ 1 (0 : Space))))
    (mul_nonneg hS (by positivity))
  refine ⟨S * B + T * A, by positivity, fun x ξ η => ?_⟩
  let f := fun y => sandwichFrequencyFactor χ y η
  let g := fun y => iteratedFDeriv ℝ n (a y) (ξ + η)
  let F := 𝓕 (χ : Space → ℂ) η
  let W := 1 + ‖ξ‖
  let V := 1 + ‖η‖
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hV : 1 ≤ V := le_add_of_nonneg_right (norm_nonneg _)
  have hf : DifferentiableAt ℝ f x :=
    (((contDiff_sandwichFrequencyFactor χ).comp
      ((contDiff_id : ContDiff ℝ ∞ (id : Space → Space)).prodMk contDiff_const)).differentiable (by simp)) x
  have hg : DifferentiableAt ℝ g x := (ha.baseDiff n (ξ + η)).differentiableAt
  have ⟨hf₀, hf₁⟩ := sandwichFrequencyFactor_base_controls χ x η
  have hg₀ : ‖g x‖ * W^n ≤ A * W * V^(n + 1) :=
    shifted_frequency_order_weight_le (fun y ζ => iteratedFDeriv ℝ n (a y) ζ) n hA orderA x ξ η
  have hg₁ : ‖fderiv ℝ g x‖ * W^n ≤ B * W * V^(n + 1) :=
    shifted_frequency_order_weight_le (fun y ζ => fderiv ℝ (fun z => iteratedFDeriv ℝ n (a z) ζ) y)
      n hB orderB x ξ η
  change ‖fderiv ℝ (fun y => f y • g y) x‖ * W^n ≤ (S * B + T * A) * W * (V^(n + 2) * ‖F‖)
  calc
    _ ≤ (‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖) * W^n :=
      mul_le_mul_of_nonneg_right (norm_fderiv_complex_smul_le hf hg) (pow_nonneg hW _)
    _ = ‖f x‖ * (‖fderiv ℝ g x‖ * W^n) + ‖fderiv ℝ f x‖ * (‖g x‖ * W^n) := by ring
    _ ≤ (S * ‖F‖) * (B * W * V^(n + 1)) + (T * V * ‖F‖) * (A * W * V^(n + 1)) :=
      add_le_add (mul_le_mul hf₀ hg₁ (mul_nonneg (norm_nonneg _) (pow_nonneg hW _)) (by positivity))
        (mul_le_mul hf₁ hg₀ (mul_nonneg (norm_nonneg _) (pow_nonneg hW _)) (by positivity))
    _ ≤ (S * ‖F‖) * (B * W * V^(n + 2)) + (T * V * ‖F‖) * (A * W * V^(n + 1)) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hV (Nat.le_succ _)) (mul_nonneg hB hW)) (by positivity)) _
    _ = _ := by rw [show n + 2 = (n + 1) + 1 from rfl, pow_succ V (n + 1)]; ring

end Burnett.Analysis.CarlesonEmbedding
