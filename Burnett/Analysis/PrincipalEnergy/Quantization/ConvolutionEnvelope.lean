import Burnett.Analysis.PrincipalEnergy.Quantization.CompactFrequencyL2

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Function MeasureTheory Filter Burnett.Fourier Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.AngularCommutator (schur_squared_integral_le)
open scoped ENNReal

/-- A genuinely integrable convolution envelope gives the same row and column
Schur constants for a jointly measurable kernel. -/
theorem convolution_envelope_action_norm_le (K : E → E → ℂ) (hK : Measurable (uncurry K))
    (D : E → ℝ) (hD : Measurable D) (hD₀ : ∀ z, 0 ≤ D z) (hI : Integrable D)
    (hBound : ∀ x y, ‖K x y‖ ≤ D (x-y)) (f : E → ℂ) (hf : Measurable f) (hf₁ : Integrable f)
    (hf₂ : MemLp f 2 volume) :
    ∃ hA : MemLp (fun x => ∫ y, K x y * f y) 2 volume,
      ‖hA.toLp (fun x => ∫ y, K x y * f y)‖ ≤ (∫ z, D z) * ‖hf₂.toLp f‖ := by
  let V : Measure E := volume
  let M := ∫ z, D z
  have hM₀ : 0 ≤ M := integral_nonneg hD₀
  have hM : (∫⁻ z, ENNReal.ofReal (D z)) = ENNReal.ofReal M :=
    (ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hD₀)).symm
  have hBoth : Integrable (uncurry fun x y => K x y * f y) (V.prod V) := by
    let T (p : E × E) : E × E := (p.1-p.2,p.2)
    have hT : MeasurePreserving T (V.prod V) (V.prod V) := measurePreserving_sub_prod V V
    have hu : Integrable (fun p : E × E => D p.1 * ‖f p.2‖) (V.prod V) := hI.mul_prod hf₁.norm
    refine (hT.integrable_comp_of_integrable hu).mono'
      (hK.mul (hf.comp measurable_snd)).aestronglyMeasurable ?_
    filter_upwards with p
    rw [uncurry_apply_pair,norm_mul]
    exact mul_le_mul_of_nonneg_right (hBound p.1 p.2) (norm_nonneg _)
  have hRow (x : E) : (∫⁻ y, ‖K x y‖ₑ) ≤ ENNReal.ofReal M := by
    refine (lintegral_mono (g := fun y => ENNReal.ofReal (D (x-y))) fun y => ?_).trans_eq ?_
    · rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hBound x y)
    · have h := V.measurePreserving_sub_left x
      rw [← lintegral_map hD.ennreal_ofReal h.measurable,h.map_eq,hM]
  have hCol (y : E) : (∫⁻ x, ‖K x y‖ₑ) ≤ ENNReal.ofReal M := by
    refine (lintegral_mono (g := fun x => ENNReal.ofReal (D (x-y))) fun x => ?_).trans_eq ?_
    · rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hBound x y)
    · have h : MeasurePreserving (fun x => x-y) V V := by
        simpa only [sub_eq_add_neg] using measurePreserving_add_right V (-y)
      rw [← lintegral_map hD.ennreal_ofReal h.measurable,h.map_eq,hM]
  let A (x : E) := ∫ y, K x y * f y
  have hAL : Integrable A := hBoth.integral_prod_left
  have hSq (u : E → ℂ) : (∫⁻ x, ‖u x‖ₑ^(2:ℕ)) = eLpNorm u 2 volume ^ (2:ℕ) := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
    simpa only [ENNReal.toReal_ofNat,ENNReal.rpow_two] using
      (lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := (volume : Measure E))
        (f := u) (q := (2:ℝ)) (by norm_num))
  have hSchur := schur_squared_integral_le V V K hK f hf _ _ hRow hCol
  change (∫⁻ x, ‖A x‖ₑ^(2:ℕ)) ≤ ENNReal.ofReal M*ENNReal.ofReal M*∫⁻ x, ‖f x‖ₑ^(2:ℕ) at hSchur
  rw [hSq,hSq,← sq] at hSchur
  have hFin := ENNReal.mul_lt_top
    (ENNReal.pow_lt_top (n := 2) (a := ENNReal.ofReal M) ENNReal.ofReal_lt_top)
    (ENNReal.pow_lt_top (n := 2) hf₂.2)
  have hA : MemLp A 2 volume := by
    refine ⟨hAL.aestronglyMeasurable,?_⟩
    by_contra! ht
    have he : eLpNorm A 2 volume = ⊤ := top_le_iff.mp ht
    rw [he,ENNReal.top_pow (by norm_num)] at hSchur
    exact hFin.not_ge hSchur
  have hReal := ENNReal.toReal_mono hFin.ne hSchur
  rw [← Lp.enorm_toLp hA, ← Lp.enorm_toLp hf₂] at hReal
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hM₀] at hReal
  refine ⟨hA,(sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM₀ (norm_nonneg _))).mp ?_⟩
  simpa only [mul_pow] using hReal

end Burnett.Analysis.FirstOrderDyadic
