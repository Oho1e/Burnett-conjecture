import Burnett.Analysis.PrincipalEnergy.Quantization.NormalizedBaseIdentification
import Mathlib.MeasureTheory.Group.Prod

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Function MeasureTheory Filter Burnett.Fourier Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.AngularCommutator (schur_squared_integral_le)
open scoped ENNReal

def compactFrequencyKernel (a : E → E → ℂ) (η ξ : E) : ℂ :=
  normalizedBaseFourier a (η - ξ) ξ

def compactFrequencyAction (a : E → E → ℂ) (w : E → ℂ) (η : E) : ℂ :=
  ∫ ξ, compactFrequencyKernel a η ξ * w ξ

private theorem compactFrequencyKernel_continuous {a : E → E → ℂ}
    (ha : CompactBaseOrderOne a) (hCont : Continuous (uncurry a)) :
    Continuous (uncurry (compactFrequencyKernel a)) := by
  let S (p : E × E) : E × E := (p.1 - p.2,p.2)
  have hS : Continuous S := (continuous_fst.sub continuous_snd).prodMk continuous_snd
  change Continuous (uncurry (normalizedBaseFourier a) ∘ S)
  exact (normalizedBaseFourier_joint_continuous ha hCont).comp hS

private theorem squared_eLpNorm_eq (u : E → ℂ) :
    (∫⁻ x, ‖u x‖ₑ ^ (2 : ℕ)) = eLpNorm u 2 volume ^ (2 : ℕ) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    (lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := (volume : Measure E))
      (f := u) (q := (2 : ℝ)) (by norm_num))

/-- The same integrable envelope bounds both absolute kernel marginals after
the actual frequency shear. On integrable L² inputs this yields both an
integrable frequency output and its true L² norm estimate. -/
theorem compactFrequencyAction_integrable_and_norm_le {a : E → E → ℂ}
    (ha : CompactBaseOrderOne a) (hCont : Continuous (uncurry a))
    (C : ℝ) (hC : 0 ≤ C)
    (hEnv : Integrable (fun k : E => C * ((1 + ‖k‖ ^ 2) ^ 3)⁻¹))
    (hDom : ∀ k ξ, ‖normalizedBaseFourier a k ξ‖ ≤ C * ((1 + ‖k‖ ^ 2) ^ 3)⁻¹)
    (w : E → ℂ) (hwM : Measurable w) (hw₁ : Integrable w) (hw₂ : MemLp w 2 volume) :
    Integrable (compactFrequencyAction a w) ∧
      ∃ hg : MemLp (compactFrequencyAction a w) 2 volume,
        ‖hg.toLp (compactFrequencyAction a w)‖ ≤
          (∫ k : E, C * ((1 + ‖k‖ ^ 2) ^ 3)⁻¹) * ‖hw₂.toLp w‖ := by
  let env (k : E) := C * ((1 + ‖k‖ ^ 2) ^ 3)⁻¹
  let V : Measure E := volume
  let K := compactFrequencyKernel a
  let D := ∫ k : E, env k
  have hEnv₀ (k : E) : 0 ≤ env k := by dsimp [env]; positivity
  have hEnvM : Measurable env := by unfold env; fun_prop
  have hD : 0 ≤ D := integral_nonneg hEnv₀
  have hDₑ : (∫⁻ k, ENNReal.ofReal (env k)) = ENNReal.ofReal D :=
    (ofReal_integral_eq_lintegral_ofReal hEnv (Eventually.of_forall hEnv₀)).symm
  have hKm := (compactFrequencyKernel_continuous ha hCont).measurable
  have hIntegrable : Integrable (uncurry fun η ξ => K η ξ * w ξ) (V.prod V) := by
    let S (p : E × E) : E × E := (p.1 - p.2,p.2)
    have hS : MeasurePreserving S (V.prod V) (V.prod V) := measurePreserving_sub_prod V V
    have hMajorImage : Integrable (fun q : E × E => env q.1 * ‖w q.2‖) (Measure.map S (V.prod V)) := by
      rw [hS.map_eq]
      exact hEnv.mul_prod hw₁.norm
    have hMajor : Integrable (fun q : E × E => env (q.1 - q.2) * ‖w q.2‖) (V.prod V) :=
      (integrable_map_measure hMajorImage.aestronglyMeasurable hS.measurable.aemeasurable).mp hMajorImage
    refine hMajor.mono' (hKm.mul (hwM.comp measurable_snd)).aestronglyMeasurable ?_
    filter_upwards with p
    rw [uncurry_apply_pair, norm_mul]
    exact mul_le_mul_of_nonneg_right (hDom (p.1 - p.2) p.2) (norm_nonneg _)
  have hL₁ : Integrable (compactFrequencyAction a w) := hIntegrable.integral_prod_left
  have hRow (η : E) : (∫⁻ ξ, ‖K η ξ‖ₑ) ≤ ENNReal.ofReal D := by
    have hp := V.measurePreserving_sub_left η
    refine (lintegral_mono (g := fun ξ => ENNReal.ofReal (env (η - ξ))) fun ξ => ?_).trans_eq ?_
    · rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hDom (η - ξ) ξ)
    · change (∫⁻ ξ, ENNReal.ofReal (env ((fun z => η - z) ξ))) = _
      rw [← lintegral_map (hEnvM.ennreal_ofReal) hp.measurable, hp.map_eq, hDₑ]
  have hCol (ξ : E) : (∫⁻ η, ‖K η ξ‖ₑ) ≤ ENNReal.ofReal D := by
    have hp : MeasurePreserving (fun z => z - ξ) V V := by
      simpa only [sub_eq_add_neg] using measurePreserving_add_right V (-ξ)
    refine (lintegral_mono (g := fun η => ENNReal.ofReal (env (η - ξ))) fun η => ?_).trans_eq ?_
    · rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hDom (η - ξ) ξ)
    · change (∫⁻ η, ENNReal.ofReal (env ((fun z => z - ξ) η))) = _
      rw [← lintegral_map (hEnvM.ennreal_ofReal) hp.measurable, hp.map_eq, hDₑ]
  have hSq := schur_squared_integral_le V V K hKm w hwM _ _ hRow hCol
  change (∫⁻ η, ‖compactFrequencyAction a w η‖ₑ ^ (2 : ℕ)) ≤
    ENNReal.ofReal D * ENNReal.ofReal D * ∫⁻ ξ, ‖w ξ‖ₑ ^ (2 : ℕ) at hSq
  rw [squared_eLpNorm_eq, squared_eLpNorm_eq, ← sq] at hSq
  have hFinite := ENNReal.mul_lt_top
    (ENNReal.pow_lt_top (n := 2) (a := ENNReal.ofReal D) ENNReal.ofReal_lt_top)
    (ENNReal.pow_lt_top (n := 2) hw₂.2)
  have hL₂ : MemLp (compactFrequencyAction a w) 2 volume := by
    refine ⟨hL₁.aestronglyMeasurable,?_⟩
    by_contra! hAtTop
    have hh : eLpNorm (compactFrequencyAction a w) 2 volume = ⊤ := top_le_iff.mp hAtTop
    rw [hh, ENNReal.top_pow (by norm_num)] at hSq
    exact hFinite.not_ge hSq
  have hReal := ENNReal.toReal_mono hFinite.ne hSq
  rw [← Lp.enorm_toLp hL₂, ← Lp.enorm_toLp hw₂] at hReal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hD] at hReal
  refine ⟨hL₁,hL₂,(sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (norm_nonneg _))).mp ?_⟩
  simpa only [mul_pow] using hReal

end Burnett.Analysis.FirstOrderDyadic
