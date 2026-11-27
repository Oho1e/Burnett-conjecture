import Burnett.Analysis.PrincipalEnergy.Freezing.RadianOrderZeroSymbols
import Burnett.Analysis.PrincipalEnergy.Freezing.SummedOrderZeroJets

set_option autoImplicit false
set_option maxHeartbeats 1900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal ContDiff FourierTransform

theorem patch_moment_nonneg (r : ℕ) (f : E → ℂ) : 0 ≤ patchFourierMoment r f :=
  integral_nonneg fun _ => mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)

theorem norm_bounded_radian_fourier_average_le (m : E × E → ℝ) (meas : Measurable m)
    (grow : RadianAverageGrowth m) (D : ℝ) (bound : ∀ q, ‖m q‖ ≤ D)
    (f u : SchwartzMap E ℂ) (x : E) :
    ‖radianFourierAverage m f u x‖ ≤ D * patchFourierMoment 0 f * patchFourierMoment 0 u := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  rw [radian_fourier_average_eq_integral m meas grow]
  have eq : D * patchFourierMoment 0 f * patchFourierMoment 0 u =
      ∫ η : E, (D * patchFourierMoment 0 u) * ‖F η‖ := by
    unfold patchFourierMoment
    simp only [pow_zero, one_mul, integral_const_mul]
    change D * (∫ η, ‖F η‖) * (∫ ξ, ‖𝓕 (u : E → ℂ) ξ‖) =
      D * (∫ ξ, ‖𝓕 (u : E → ℂ) ξ‖) * (∫ η, ‖F η‖)
    ring
  rw [eq]
  apply norm_integral_le_of_norm_le (F.integrable.norm.const_mul _)
  filter_upwards with η
  simp only [norm_mul, patch_fourier_phase_norm, one_mul]
  have r := norm_radian_action_le_of_symbol_bound (fun ξ => m (η, ξ)) D (fun ξ => bound _) u x
  change ‖F η‖ * ‖radianAction (fun ξ => m (η, ξ)) u x‖ ≤ _
  rw [mul_comm ‖F η‖]
  exact mul_le_mul_of_nonneg_right (by simpa only [patchFourierMoment, pow_zero, one_mul] using r) (norm_nonneg _)

/-- Pointwise absolute control for a separated bounded frequency profile,
and the exact continuous coordinate jet needed to sum it on the physical space. -/
theorem bounded_separated_radian_action_pointwise (σ : ℝ) (b : E → ℝ) (hb : Measurable b)
    (D : ℝ) (D0 : 0 ≤ D) (bound : ∀ ξ, ‖b ξ‖ ≤ D)
    (f u : SchwartzMap E ℂ) :
    (∀ x, ‖separatedRadianQuantization σ b f u x‖ ≤ D * patchFourierMoment 0 f * patchFourierMoment 0 u) ∧
      ∀ j : Index, Continuous (actualCoordinateJet (separatedRadianQuantization σ b f u) j) ∧
        ∀ x, ‖actualCoordinateJet (separatedRadianQuantization σ b f u) j x‖ ≤
          D * (tau * patchFourierMoment 1 f) * patchFourierMoment 0 u +
            D * patchFourierMoment 0 f * patchFourierMoment 0 (energyPartial j u) := by
  let m := slantedRadianSymbol σ b
  have mM : Measurable m := slanted_radian_symbol_measurable σ b hb
  have m0 (q : E × E) : ‖m q‖ ≤ D := bound _
  have mg : RadianAverageGrowth m := by
    refine ⟨D, D0, fun η ξ => (m0 _).trans ?_⟩
    exact (le_mul_of_one_le_right D0 (le_add_of_nonneg_right (norm_nonneg η))).trans
      (le_mul_of_one_le_right (mul_nonneg D0 (by positivity)) (le_add_of_nonneg_right (norm_nonneg ξ)))
  have H (v w : SchwartzMap E ℂ) (x : E) := norm_bounded_radian_fourier_average_le m mM mg D m0 v w x
  refine ⟨H f u, ?_⟩
  intro j
  have J : actualCoordinateJet (separatedRadianQuantization σ b f u) j =
      radianFourierAverage m (energyPartial j f) u + radianFourierAverage m f (energyPartial j u) :=
    funext fun x => (radian_fourier_average_coordinate m mM mg f u j x).2
  have cs (v w : SchwartzMap E ℂ) : Continuous (radianFourierAverage m v w) :=
    (show Differentiable ℝ (radianFourierAverage m v w) from fun x =>
      (radian_fourier_average_coordinate m mM mg v w j x).1).continuous
  rw [J]
  refine ⟨(cs _ _).add (cs _ _), fun x => (norm_add_le _ _).trans ?_⟩
  exact add_le_add ((H (energyPartial j f) u x).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (patch_fourier_moment_partial 0 j f) D0) (patch_moment_nonneg _ _))) (H f (energyPartial j u) x)

end Burnett.A03
