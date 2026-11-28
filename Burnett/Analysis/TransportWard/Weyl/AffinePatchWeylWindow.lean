import Burnett.Analysis.CubicEnergy.CompleteEnergy.FieldAndCoefficientChecks
import Burnett.Analysis.PrincipalEnergy.Freezing.RescaledPatchCutoff
import Burnett.Analysis.TransportWard.Weyl.Amplitude.LocalizedPrincipalTest
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualSymbolInputs
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.V03

open Filter Metric MeasureTheory Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open scoped ContDiff FourierTransform Topology

/-- One real affine profile is identically one on a neighborhood of the
actual C03 inner patch and has its support in the C03 outer ball. -/
theorem exists_affineWeylPatchWindow :
    ∃ (φ : E → ℝ) (Θ : SchwartzMap E ℂ) (η : E → ℝ → SchwartzMap E ℂ),
      ContDiff ℝ ∞ φ ∧ tsupport φ ⊆ closedBall (0 : E) 6 ∧
      (∀ x, Θ x = (φ x : ℂ)) ∧
      ∀ (c : E) (ℓ : ℝ), 0 < ℓ →
        (∀ x, η c ℓ x = Θ (ℓ⁻¹ • (x - c))) ∧
        (∀ x, η c ℓ x = (φ (ℓ⁻¹ • (x - c)) : ℂ)) ∧
        tsupport (η c ℓ : E → ℂ) ⊆ ball c (6 * ℓ) ∧
        (∀ x ∈ ball c (5 * ℓ), η c ℓ x = 1) := by
  obtain ⟨φ, _, hφ, hφc, _, scaled⟩ := Burnett.A03.exists_rescaled_patch_cutoff 5 6 (by norm_num) (by norm_num)
  let Θ : SchwartzMap E ℂ :=
    (hφc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφ)
  let q (c : E) (ℓ : ℝ) (x : E) := φ (ℓ⁻¹ • (x - c))
  have hq (c : E) (ℓ : ℝ) (hℓ : 0 < ℓ) : ContDiff ℝ ∞ (q c ℓ) := (scaled c ℓ hℓ).1
  have hqc (c : E) (ℓ : ℝ) (hℓ : 0 < ℓ) : HasCompactSupport (q c ℓ) := (scaled c ℓ hℓ).2.1
  let η (c : E) (ℓ : ℝ) : SchwartzMap E ℂ :=
    if hℓ : 0 < ℓ then ((hqc c ℓ hℓ).comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (hq c ℓ hℓ)) else 0
  have hη (c : E) (ℓ : ℝ) (x : E) (hℓ : 0 < ℓ) : η c ℓ x = (q c ℓ x : ℂ) := by
    simp only [η, dif_pos hℓ]
    rfl
  have hSupp : tsupport φ ⊆ ball (0 : E) 6 := by
    have hp := (scaled 0 1 zero_lt_one).2.2.2.1
    simpa only [inv_one, one_smul, sub_zero, mul_one] using hp
  refine ⟨φ, Θ, η, hφ, hSupp.trans ball_subset_closedBall, fun _ => rfl, ?_⟩
  intro c ℓ hℓ
  obtain ⟨_, _, hOne, hSupport, _⟩ := scaled c ℓ hℓ
  refine ⟨fun x => hη c ℓ x hℓ, fun x => hη c ℓ x hℓ, ?_, ?_⟩
  · rw [funext (fun x => hη c ℓ x hℓ)]
    apply (closure_mono ?_).trans hSupport
    intro x hx
    change (q c ℓ x : ℂ) ≠ 0 at hx
    change q c ℓ x ≠ 0
    intro h
    exact hx (by rw [h, Complex.ofReal_zero])
  · intro x hx
    have hqOne : q c ℓ x = 1 := hOne x (ball_subset_closedBall hx)
    rw [hη c ℓ x hℓ, hqOne, Complex.ofReal_one]

/-- The support specified by the full Euclidean array also contains the
support of each actual component entering the differentiated placements. -/
theorem fieldComponent_tsupport_subset_of_array {J : Type} [Fintype J]
    (z : J → SchwartzMap E ℂ) (K : Set E) (hz : tsupport (fieldValueArray z) ⊆ K)
    (i : J) : tsupport (z i : E → ℂ) ⊆ K := by
  apply (closure_mono ?_).trans hz
  intro x hx
  change z i x ≠ 0 at hx
  change fieldValueArray z x ≠ 0
  intro h
  exact hx (congrArg (fun v => v i) h)

/-- The original test and its double cutoff agree in all three actual
placements on a real field supported in the original four-scale patch. -/
theorem principalVariationDensity_eq_affinePatchSandwich {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℂ) (z : J → SchwartzMap E ℂ)
    (B : SchwartzMap E ℂ → E → ℂ) (η : SchwartzMap E ℂ) (c : E) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hz : tsupport (fieldValueArray z) ⊆ closedBall c (4 * ℓ))
    (hη : ∀ x ∈ ball c (5 * ℓ), η x = 1) :
    principalVariationDensity C z (fun i x => (-Complex.I) * B (z i) x) =
      principalVariationDensity C z (fun i x => (-Complex.I) * sandwichedScalarTest η B (z i) x) := by
  have hCore : closedBall c (4 * ℓ) ⊆ ball c (5 * ℓ) :=
    closedBall_subset_ball (by linarith)
  have hSupport (i : J) := fieldComponent_tsupport_subset_of_array z _ (hz.trans hCore) i
  have hSwap : (fun i x => sandwichedScalarTest η (fun u y => (-Complex.I) * B u y) (z i) x) =
      (fun i x => (-Complex.I) * sandwichedScalarTest η B (z i) x) := by
    funext i x
    simp only [sandwichedScalarTest]
    ring
  rw [← hSwap]
  exact (principal_variation_sandwiched_test C z (fun u x => (-Complex.I) * B u x)
    η (ball c (5 * ℓ)) isOpen_ball hSupport hη).symm

/-- Smoothness of the literal inverse Fourier action from the polynomial
growth of its actual symbol. The compact sandwich can therefore be made a
Schwartz field even when no global Schwartz output has been chosen. -/
theorem contDiff_radianAction_of_linear_growth (b : E → ℝ) (hb : Continuous b)
    (C : ℝ) (hC : ∀ ξ, ‖b ξ‖ ≤ C * ‖ξ‖) (u : SchwartzMap E ℂ) :
    ContDiff ℝ ∞ (radianAction b u) := by
  let U := SchwartzMap.fourierTransformCLM ℂ u
  let F := radianActionSpectrum b u
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have hF : Continuous F :=
    (Complex.ofRealCLM.continuous.comp (hb.comp (continuous_const.smul continuous_id))).mul U.continuous
  have hSize (ξ : E) : ‖F ξ‖ ≤ C * (tau * ‖ξ‖) * ‖U ξ‖ := by
    have h := hC (tau • ξ)
    rw [norm_smul, Real.norm_of_nonneg hτ.le] at h
    change ‖(b (tau • ξ) : ℂ) * U ξ‖ ≤ _
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  have moments (n : ℕ) (_ : n ≤ (⊤ : ℕ∞)) : Integrable (fun ξ : E => ‖ξ‖ ^ n * ‖F ξ‖) := by
    refine ((U.integrable_pow_mul volume (n + 1)).const_mul (C * tau)).mono'
      (continuous_norm.pow n |>.mul hF.norm |>.aestronglyMeasurable) ?_
    filter_upwards with ξ
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
    exact (mul_le_mul_of_nonneg_left (hSize ξ) (pow_nonneg (norm_nonneg _) _)).trans_eq
      (by rw [pow_succ]; ring)
  have hInv : radianAction b u = (𝓕 F) ∘ (fun x : E => -x) :=
    (radianActionSpectrum_inverse b u).symm.trans
      (funext fun x => Real.fourierIntegralInv_eq_fourierIntegral_neg F x)
  rw [hInv]
  exact (Real.contDiff_fourierIntegral moments).comp contDiff_id.neg

end Burnett.V03
