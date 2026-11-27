import Burnett.Analysis.PrincipalEnergy.Freezing.ParametricRadianFourier
import Burnett.Analysis.PrincipalEnergy.Freezing.ProfileFourierMoment

set_option autoImplicit false
set_option maxHeartbeats 1900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Burnett.A02.FrequencySplit
open scoped ENNReal FourierTransform

/-- Frequency translations retain any established L³ bound on the actual
Schwartz inputs. The output is conjugated by unit physical modulation. -/
theorem radian_shift_preserves_L3_bound (m : E → ℝ) (B : ℝ≥0∞)
    (h : ∀ u : SchwartzMap E ℂ,
      MemLp (radianAction m u) (ENNReal.ofReal 3) volume ∧
      eLpNorm (radianAction m u) (ENNReal.ofReal 3) volume ≤
        B * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume)
    (q : E) (u : SchwartzMap E ℂ) :
    let w := radianAction (fun ξ => m (ξ + tau • q)) u
    MemLp w (ENNReal.ofReal 3) volume ∧
      eLpNorm w (ENNReal.ofReal 3) volume ≤ B * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume := by
  intro w
  let v := patchModulatedSchwartz q u
  let p := ENNReal.ofReal 3
  have old := h v
  have eq : w = fun x => patchFourierPhase (-q) x * radianAction m v x :=
    funext fun x => radian_action_shift m q u x
  have mods : AEStronglyMeasurable (fun x => patchFourierPhase (-q) x) (volume : Measure E) := by
    let args : E → E × E := fun x => (-q, x)
    have hargs : Continuous args := continuous_const.prodMk continuous_id
    exact (patch_fourier_phase_continuous.comp hargs).aestronglyMeasurable
  have same (x : E) : ‖w x‖ = ‖radianAction m v x‖ := by
    rw [eq, norm_mul, patch_fourier_phase_norm, one_mul]
  have hOut : AEStronglyMeasurable w volume := eq.symm ▸ mods.mul old.1.1
  refine ⟨old.1.congr_norm hOut (Eventually.of_forall fun x => (same x).symm), ?_⟩
  rw [eLpNorm_congr_norm_ae (Eventually.of_forall same)]
  have normIn : eLpNorm (v : E → ℂ) p volume = eLpNorm (u : E → ℂ) p volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards with x
    simp only [v, patch_modulated_schwartz_apply, norm_mul, patch_fourier_phase_norm, one_mul]
  exact old.2.trans_eq (congrArg (B * ·) normIn)

/-- The physical Fourier average is order zero whenever the measured
one-frequency actions have a weighted L³ bound. The weight is also a
pointwise multiplier majorant, which justifies the ordinary integrals. -/
theorem radian_fourier_average_L3_bound (m : E × E → ℝ)
    (meas : Measurable m) (grow : RadianAverageGrowth m) (f u : SchwartzMap E ℂ)
    (A : E → ℝ) (A0 : ∀ η, 0 ≤ A η) (bound : ∀ η ξ, ‖m (η, ξ)‖ ≤ A η)
    (int : Integrable (fun η => A η * ‖𝓕 (f : E → ℂ) η‖))
    (V : ℝ≥0∞) (hV : V < ⊤)
    (est : ∀ η,
      let t := radianAction (fun ξ => m (η, ξ)) u
      MemLp t (ENNReal.ofReal 3) volume ∧
        eLpNorm t (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (A η) * V) :
    MemLp (radianFourierAverage m f u) (ENNReal.ofReal 3) volume ∧
      eLpNorm (radianFourierAverage m f u) (ENNReal.ofReal 3) volume ≤
        ENNReal.ofReal (∫ η, A η * ‖𝓕 (f : E → ℂ) η‖) * V := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let T (η : E) := radianAction (fun ξ => m (η, ξ)) u
  let G (z : E × E) := (patchFourierPhase z.1 z.2 * F z.1) * T z.1 z.2
  let w (η : E) := A η * ‖F η‖
  let p := ENNReal.ofReal 3
  have hPhase : Measurable (fun z : E × E => patchFourierPhase z.1 z.2) :=
    patch_fourier_phase_continuous.measurable
  have hF : Measurable (fun z : E × E => F z.1) :=
    F.continuous.measurable.comp (measurable_fst : Measurable (Prod.fst : E × E → E))
  have hT : Measurable (fun z : E × E => T z.1 z.2) := radian_action_varying_measurable m meas u
  have hG : Measurable G := (hPhase.mul hF).mul hT
  have cont : Continuous (radianFourierAverage m f u) :=
    (show Differentiable ℝ (radianFourierAverage m f u) from fun x =>
      (radian_fourier_average_coordinate m meas grow f u 0 x).1).continuous
  have major (η x : E) : ‖G (η, x)‖ ≤ w η * ∫ ξ, ‖𝓕 (u : E → ℂ) ξ‖ := by
    dsimp only [G, w]
    rw [norm_mul, norm_mul, patch_fourier_phase_norm, one_mul]
    calc
      _ ≤ ‖F η‖ * (A η * ∫ ξ, ‖𝓕 (u : E → ℂ) ξ‖) :=
        mul_le_mul_of_nonneg_left (norm_radian_action_le_of_symbol_bound _ _ (bound η) u x) (norm_nonneg _)
      _ = _ := by ring
  have sections (η : E) :
      MemLp (fun x => G (η, x)) p volume ∧ eLpNorm (fun x => G (η, x)) p volume ≤ ENNReal.ofReal (w η) * V := by
    have old := est η
    have normSame (x : E) : ‖G (η, x)‖ = ‖F η • T η x‖ := by
      simp only [G, norm_mul, patch_fourier_phase_norm, one_mul, norm_smul]
    have m : AEStronglyMeasurable (fun x => G (η, x)) volume :=
      (hG.comp (measurable_const.prodMk measurable_id : Measurable (fun x : E => (η, x)))).aestronglyMeasurable
    refine ⟨(old.1.const_smul (F η)).congr_norm m (Eventually.of_forall fun x => (normSame x).symm), ?_⟩
    rw [eLpNorm_congr_norm_ae (Eventually.of_forall normSame)]
    change eLpNorm (F η • T η) p volume ≤ _
    rw [eLpNorm_const_smul]
    refine (mul_le_mul_left' old.2 _).trans_eq ?_
    simp only [w, ENNReal.ofReal_mul (A0 η), ← ofReal_norm_eq_enorm, mul_assoc]
    rw [mul_left_comm]
  exact patch_integral_L3_bound volume G hG _ cont (radian_fourier_average_eq_integral m meas grow f u)
    w int (fun η => mul_nonneg (A0 η) (norm_nonneg _)) (∫ ξ, ‖𝓕 (u : E → ℂ) ξ‖) major V hV sections

end Burnett.A03
