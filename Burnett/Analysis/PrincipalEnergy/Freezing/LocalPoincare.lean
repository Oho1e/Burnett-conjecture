import Burnett.Analysis.PrincipalEnergy.Freezing.BallLineIntegral
import Burnett.Analysis.CubicEnergy.CompleteEnergy.UniformWeightedEuclidean
import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Set Burnett.RicciSymbol
open Burnett.A02.FrequencySplit Burnett.A02.FieldAndCoefficientReview
open scoped ENNReal NNReal

private theorem ennreal_rpow_three (v : ℝ≥0∞) : v ^ (3 : ℝ) = v ^ (3 : ℕ) :=
  ENNReal.rpow_natCast v 3

private theorem eLpNorm_cube_eq_lintegral {V : Type} [NormedAddCommGroup V] (f : E → V) :
    eLpNorm f (ENNReal.ofReal 3) volume ^ (3 : ℕ) = ∫⁻ x, ‖f x‖ₑ ^ (3 : ℕ) := by
  simpa only [ENNReal.ofReal_ofNat, NNReal.coe_ofNat, ENNReal.coe_ofNat, ennreal_rpow_three]
    using (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := (volume : Measure E))
      (p := (3 : ℝ≥0)) (by norm_num))

private theorem cube_of_rpow_third (a : ℝ≥0∞) : (a ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num [ENNReal.rpow_one]

private theorem cube_of_rpow_two_thirds (a : ℝ≥0∞) :
    (a ^ (1 / (3 / 2) : ℝ)) ^ (3 : ℕ) = a ^ (2 : ℕ) := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  rw [show (1 / (3 / 2) : ℝ) * (3 : ℕ) = 2 by norm_num]
  exact ENNReal.rpow_natCast a 2

/-- The scalar integral estimate is applied to the norm of the entire
Euclidean gradient array along each line. -/
private theorem cube_line_bound {V : Type} [NormedAddCommGroup V] (f : ℝ → V)
    (hf : Continuous f) (a : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal (∫ t in (0 : ℝ)..a, ‖f t‖) ^ (3 : ℕ) ≤
      (∫⁻ t in Ioc (0 : ℝ) a, ‖f t‖ₑ ^ (3 : ℕ)) * ENNReal.ofReal a ^ (2 : ℕ) := by
  let ν := (volume : Measure ℝ).restrict (Ioc 0 a)
  have hMass : ν univ = ENNReal.ofReal a := by
    change ((volume : Measure ℝ).restrict (Ioc 0 a)) univ = _
    rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  have hIntegrable : Integrable f ν := (hf.intervalIntegrable (μ := volume) 0 a).1
  rw [intervalIntegral.integral_of_le ha, ofReal_integral_norm_eq_lintegral_enorm hIntegrable]
  have hPair : (3 : ℝ).HolderConjugate (3 / 2) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hPair
    (f := fun t => ‖f t‖ₑ) (g := fun _ => 1)
    hf.enorm.measurable.aemeasurable aemeasurable_const
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, hMass, one_mul,
    ennreal_rpow_three] at hHolder
  simpa only [mul_pow, cube_of_rpow_third, cube_of_rpow_two_thirds] using
    pow_le_pow_left' hHolder (3 : ℕ)

/-- The L³ Poincaré inequality for the actual supported field and the
actual full Euclidean gradient, with a fixed constant independent of the center. -/
theorem euclidean_field_local_poincare_eLpNorm {J : Type} [Fintype J]
    (z : J → SchwartzMap E ℂ) (c : E) (r : ℝ) (hr : 0 < r)
    (hz : tsupport (fieldValueArray z) ⊆ ball c r) :
    eLpNorm (fieldValueArray z) (ENNReal.ofReal 3) volume ≤
      ENNReal.ofReal (3 * r) * euclideanFieldGradientNorm z := by
  let v : E := EuclideanSpace.single (0 : Index) 1
  let a := 3 * r
  let ν := (volume : Measure ℝ).restrict (Ioc 0 a)
  let G (x : E) := ‖euclideanFieldGradient z x‖ₑ ^ (3 : ℕ)
  let H (x : E) (t : ℝ) := G (x + t • v)
  let M := ENNReal.ofReal a
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hMass : ν univ = M := by
    change ((volume : Measure ℝ).restrict (Ioc 0 a)) univ = ENNReal.ofReal a
    rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  have hGrad : Continuous (euclideanFieldGradient z) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => (energyPartial k.1 (z k.2)).continuous)
  have hG : Measurable G := hGrad.enorm.measurable.pow_const _
  have hH : Measurable (Function.uncurry H) := by
    change Measurable (fun p : E × ℝ => G (p.1 + p.2 • v))
    exact hG.comp (continuous_fst.add (continuous_snd.smul continuous_const)).measurable
  have hInner : Measurable (fun x => ∫⁻ t, H x t ∂ν) := hH.lintegral_prod_right
  have hPoint (x : E) : ‖fieldValueArray z x‖ₑ ^ (3 : ℕ) ≤
      (∫⁻ t, H x t ∂ν) * M ^ (2 : ℕ) := by
    let f (t : ℝ) := euclideanFieldGradient z (x + t • v)
    have hf : Continuous f := hGrad.comp (continuous_const.add (continuous_id.smul continuous_const))
    have hPoint := ENNReal.ofReal_le_ofReal (ball_field_norm_le_line_integral z c r hr hz x)
    rw [ofReal_norm_eq_enorm] at hPoint
    exact (pow_le_pow_left' hPoint (3 : ℕ)).trans (cube_line_bound f hf a ha)
  have hTranslation (t : ℝ) : (∫⁻ x, H x t) = ∫⁻ x, G x :=
    (measurePreserving_add_right (volume : Measure E) (t • v)).lintegral_comp_emb
      (Homeomorph.addRight (t • v)).measurableEmbedding G
  have hFubini : (∫⁻ x, ∫⁻ t, H x t ∂ν) = (∫⁻ x, G x) * M := by
    rw [lintegral_lintegral_swap hH.aemeasurable]
    simp only [hTranslation, lintegral_const, hMass]
  have hCube : eLpNorm (fieldValueArray z) (ENNReal.ofReal 3) volume ^ (3 : ℕ) ≤
      (M * euclideanFieldGradientNorm z) ^ (3 : ℕ) := calc
    _ = ∫⁻ x, ‖fieldValueArray z x‖ₑ ^ (3 : ℕ) := eLpNorm_cube_eq_lintegral _
    _ ≤ ∫⁻ x, (∫⁻ t, H x t ∂ν) * M ^ (2 : ℕ) := lintegral_mono hPoint
    _ = (∫⁻ x, G x) * M * M ^ (2 : ℕ) := by
      rw [lintegral_mul_const _ hInner, hFubini]
    _ = _ := by
      rw [mul_pow, euclideanFieldGradientNorm, eLpNorm_cube_eq_lintegral]
      change (∫⁻ x, G x) * M * M ^ (2 : ℕ) = M ^ (3 : ℕ) * (∫⁻ x, G x)
      ring
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : 0 < (3 : ℝ))).mp
  simpa only [ennreal_rpow_three] using hCube

/-- The same estimate written in the real-valued norms used in the energy bound. -/
theorem euclidean_field_local_poincare {J : Type} [Fintype J] (z : J → SchwartzMap E ℂ)
    (c : E) (r : ℝ) (hr : 0 < r) (hz : tsupport (fieldValueArray z) ⊆ ball c r) :
    euclideanFieldValueL3 z ≤ (3 * r) * euclideanFieldGradientL3 z := by
  have hFinite : ENNReal.ofReal (3 * r) * euclideanFieldGradientNorm z < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (euclideanFieldGradientNorm_lt_top z)
  simpa only [euclideanFieldValueL3, euclideanFieldGradientL3, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 3 * r)] using
    ENNReal.toReal_mono hFinite.ne (euclidean_field_local_poincare_eLpNorm z c r hr hz)

/-- The manuscript's patch-radius form, with the explicit constant 3R. -/
theorem euclidean_field_patch_poincare {J : Type} [Fintype J] (z : J → SchwartzMap E ℂ)
    (x₀ : E) (R ℓ : ℝ) (hR : 0 < R) (hℓ : 0 < ℓ)
    (hz : tsupport (fieldValueArray z) ⊆ ball x₀ (R * ℓ)) :
    euclideanFieldValueL3 z ≤ (3 * R) * ℓ * euclideanFieldGradientL3 z := by
  simpa only [← mul_assoc] using euclidean_field_local_poincare z x₀ (R * ℓ) (mul_pos hR hℓ) hz

end Burnett.A03
