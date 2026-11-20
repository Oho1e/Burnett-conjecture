import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualCutoff
import Burnett.Analysis.ShiftedFourierWindow.SchwartzMaximal
import Burnett.Analysis.CenteredMaximal.MaximalLp

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Burnett.A02.FrequencySplit.CMBilinearDual
open Burnett.Analysis.CenteredMaximal
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow

open MeasureTheory Filter
open scoped ContDiff ENNReal FourierTransform RealInnerProductSpace Topology

private def phase (t : ℝ) : ℂ := Complex.exp ((↑(2 * Real.pi * t) : ℂ) * Complex.I)

private theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, Complex.norm_exp]

private theorem phase_add (t u : ℝ) : phase (t + u) = phase t * phase u := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private def lowInverse (a : SchwartzMap E ℂ) (F : E → ℂ) (s : ℝ) : E → ℂ :=
  𝓕⁻ (fun ξ => a (s • ξ) * F ξ)

/-- The cutoff acts by the physical convolution on any inverse-integral
representative with an integrable spectrum. -/
private theorem lowInverse_kernel (a : SchwartzMap E ℂ) (F : E → ℂ)
    (hF : Measurable F) (hi : Integrable F) {s : ℝ} (hs : 0 < s) (x : E) :
    lowInverse a F s x =
      ∫ y, ((s ^ 4)⁻¹ • (SchwartzMap.fourierTransformCLE ℂ).symm a (s⁻¹ • (x - y))) * 𝓕⁻ F y := by
  let φ := (SchwartzMap.fourierTransformCLE ℂ).symm a
  let T := fun (z ξ : E) => φ z * (phase (inner ℝ ξ (x - s • z)) * F ξ)
  have mT : Measurable (Function.uncurry T) := by
    have continuous_phase : Continuous (fun p : E × E => phase (inner ℝ p.2 (x - s • p.1))) := by
      unfold phase
      fun_prop
    exact ((φ.continuous.measurable.comp measurable_fst).mul
      (continuous_phase.measurable.mul (hF.comp measurable_snd)))
  have hT : Integrable (Function.uncurry T) ((volume : Measure E).prod volume) := by
    refine (φ.integrable.norm.mul_prod hi.norm).mono' mT.aestronglyMeasurable ?_
    filter_upwards with z
    change ‖φ z.1 * (phase (inner ℝ z.2 (x - s • z.1)) * F z.2)‖ ≤ ‖φ z.1‖ * ‖F z.2‖
    simp only [norm_mul, phase_norm, one_mul, le_refl]
  have physical (z : E) : φ z * 𝓕⁻ F (x - s • z) = ∫ ξ, T z ξ := by
    rw [Real.fourierIntegralInv_eq', ← integral_const_mul]
    rfl
  have frequency (ξ : E) : phase (inner ℝ ξ x) * (a (s • ξ) * F ξ) = ∫ z, T z ξ := by
    have hφ : 𝓕 (φ : E → ℂ) (s • ξ) = a (s • ξ) :=
      congrArg (fun f : SchwartzMap E ℂ => f (s • ξ)) ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply a)
    rw [← hφ, Real.fourierIntegral_eq']
    simp only [smul_eq_mul, ← integral_mul_const, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    have ph : phase (inner ℝ ξ (x - s • z)) =
        phase (inner ℝ ξ x) * phase (-inner ℝ z (s • ξ)) := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, real_inner_comm ξ z,
        sub_eq_add_neg, phase_add]
    change phase (inner ℝ ξ x) * (Complex.exp ((↑(-2 * Real.pi * inner ℝ z (s • ξ)) : ℂ) * Complex.I) *
      φ z * F ξ) = φ z * (phase (inner ℝ ξ (x - s • z)) * F ξ)
    rw [ph]
    simp only [phase, mul_neg, neg_mul]
    ring
  have integral_eq : lowInverse a F s x = ∫ z, φ z * 𝓕⁻ F (x - s • z) := by
    rw [lowInverse, Real.fourierIntegralInv_eq']
    simp only [smul_eq_mul]
    change (∫ ξ, phase (inner ℝ ξ x) * (a (s • ξ) * F ξ)) = _
    simp_rw [frequency, physical]
    exact (integral_integral_swap hT).symm
  let H := fun y => φ (s⁻¹ • y) * 𝓕⁻ F (x - y)
  have hscl := Measure.integral_comp_smul_of_nonneg (volume : Measure E) H s (hR := hs.le)
  rw [show Module.finrank ℝ E = 4 from finrank_euclideanSpace_fin] at hscl
  have unscale (z : E) : H (s • z) = φ z * 𝓕⁻ F (x - s • z) := by
    simp only [H, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  have translate : (∫ y, φ (s⁻¹ • (x - y)) * 𝓕⁻ F y) = ∫ y, H y := by
    have hc : MeasurePreserving (MeasurableEquiv.subLeft x) (volume : Measure E) volume :=
      (volume : Measure E).measurePreserving_sub_left x
    have eq := hc.integral_comp' H
    change (∫ y, H (x - y)) = ∫ y, H y at eq
    simpa only [H, sub_sub_cancel] using eq
  change lowInverse a F s x = ∫ y, ((s ^ 4)⁻¹ • φ (s⁻¹ • (x - y))) * 𝓕⁻ F y
  rw [integral_eq]
  simp_rw [smul_mul_assoc]
  rw [integral_smul, translate]
  simpa only [unscale] using hscl

private theorem cut_sub_low (F : E → ℂ) (hF : ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0})
    (hi : Integrable F) (n : ℕ) (x : E) :
    annularInput F hF n x =
      lowInverse (schwartzBump mikhlinBall) F (inputCutoffRadius n)⁻¹ x -
        lowInverse (schwartzBump mikhlinBall) F (inputCutoffRadius n) x := by
  let a := schwartzBump mikhlinBall
  let w := fun ξ : E => phase (inner ℝ ξ x)
  have cw : Continuous w := by dsimp only [w, phase]; fun_prop
  have hprod (s : ℝ) : Integrable (fun ξ => w ξ * (a (s • ξ) * F ξ)) := by
    have hA : Continuous (fun ξ => a (s • ξ)) :=
      a.continuous.comp (continuous_const.smul continuous_id)
    exact (hi.bdd_mul hA.aestronglyMeasurable ⟨_, fun ξ => a.norm_le_seminorm ℂ (s • ξ)⟩).bdd_mul
      cw.aestronglyMeasurable ⟨1, fun ξ => (phase_norm _).le⟩
  simp only [show annularInput F hF n x = 𝓕⁻ (fun ξ => (inputAnnularMask n ξ : ℂ) * F ξ) x from
    congrFun (annularInput_eq_inverse F hF n) x, lowInverse, Real.fourierIntegralInv_eq', smul_eq_mul]
  change (∫ ξ, w ξ * ((inputAnnularMask n ξ : ℂ) * F ξ)) =
    (∫ ξ, w ξ * (a ((inputCutoffRadius n)⁻¹ • ξ) * F ξ)) -
      ∫ ξ, w ξ * (a (inputCutoffRadius n • ξ) * F ξ)
  rw [← integral_sub (hprod _) (hprod _)]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [inputAnnularMask, Complex.ofReal_sub, a, schwartzBump_apply, sub_mul, mul_sub]

private theorem eLpNorm_tendsto_zero_of_domination {v : ℕ → E → ℂ} {p : ℝ} (hp : 0 < p)
    (D : E → ℝ≥0∞) (hD : eLpNorm D (ENNReal.ofReal p) volume < ⊤)
    (hv : ∀ n, AEStronglyMeasurable (v n) volume) (hb : ∀ n x, ‖v n x‖ₑ ≤ D x)
    (hlim : ∀ᵐ x ∂(volume : Measure E), Tendsto (fun n => v n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (v n) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hp₀ := (ENNReal.ofReal_pos.mpr hp).ne'
  have hf : (∫⁻ x, D x ^ p ∂(volume : Measure E)) ≠ ⊤ := by
    simpa only [enorm_eq_self, ENNReal.toReal_ofReal hp.le] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp₀ ENNReal.ofReal_ne_top hD).ne
  have conv : Tendsto (fun n => ∫⁻ x, ‖v n x‖ₑ ^ p ∂(volume : Measure E)) atTop (𝓝 0) := by
    have lim := tendsto_lintegral_of_dominated_convergence' (f := fun _ => 0) (fun x => D x ^ p)
      (fun n => (hv n).aemeasurable.enorm.pow_const p)
      (fun n => Eventually.of_forall fun x => ENNReal.rpow_le_rpow (hb n x) hp.le) hf
      (hlim.mono fun x h => by
        have c : Continuous (fun a : ℝ≥0∞ => a ^ p) := ENNReal.continuous_rpow_const
        simpa only [Function.comp_apply, enorm_zero, ENNReal.zero_rpow_of_pos hp] using
          (c.tendsto ‖(0 : ℂ)‖ₑ).comp ((continuous_enorm.tendsto (0 : ℂ)).comp h))
    simpa only [lintegral_zero] using lim
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm hp₀ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  have c : Continuous (fun a : ℝ≥0∞ => a ^ (1 / p)) := ENNReal.continuous_rpow_const
  simpa only [Function.comp_apply, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp)] using
    (c.tendsto (0 : ℝ≥0∞)).comp conv

/-- Strong convergence in each finite p > 1 of the same annular Schwartz
approximants to an actual physical inverse-integral representative. -/
theorem annularInput_tendsto_eLpNorm (F : E → ℂ)
    (hF : ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0}) (hi : Integrable F)
    {p : ℝ} (hp : 1 < p) (hu : MemLp (𝓕⁻ F) (ENNReal.ofReal p) volume) :
    Tendsto (fun n => eLpNorm ((annularInput F hF n : E → ℂ) - 𝓕⁻ F) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
  let U := 𝓕⁻ F
  let a := schwartzBump mikhlinBall
  let φ := (SchwartzMap.fourierTransformCLE ℂ).symm a
  let g := fun x : E => ‖U x‖ₑ
  let P := ENNReal.ofReal p
  have hpos : 0 < p := zero_lt_one.trans hp
  have hP : 1 ≤ P := by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have mu : Continuous U := by
    rw [show U = (𝓕 F) ∘ (fun x : E => -x) from funext (Real.fourierIntegralInv_eq_fourierIntegral_neg F)]
    exact (VectorFourier.fourierIntegral_continuous (L := innerₗ E)
      Real.continuous_fourierChar continuous_inner hi).comp continuous_neg
  have mf : Measurable F := measurable_of_continuousOn_compl_singleton 0 hF.continuousOn
  have mg : Measurable g := mu.measurable.enorm
  obtain ⟨C, hC, est⟩ := shifted_schwartz_kernel_maximal φ
  let M := centeredMax g
  let A := fun x => C * M x
  have mM : Measurable M := centeredMax_measurable g
  have ma : AEStronglyMeasurable A volume := (measurable_const.mul mM).aestronglyMeasurable
  have hmax : eLpNorm M P volume < ⊤ := (centeredMax_complex_Lp U mu.measurable p hp).trans_lt
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (one_div_pos.mpr hpos).le (maximalConstant_finite p).ne) hu.2)
  have hA : eLpNorm A P volume < ⊤ := by
    apply (eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' P (f := A) (g := M) (c := C) mM.aestronglyMeasurable
      (Eventually.of_forall fun x => by simp only [A, enorm_eq_self, le_refl])).trans_lt
    exact ENNReal.mul_lt_top hC hmax
  have hg : eLpNorm g P volume < ⊤ := (eLpNorm_enorm U).trans_lt hu.2
  have hd : eLpNorm ((A + A) + g) P volume < ⊤ :=
    (eLpNorm_add_le (ma.add ma) mg.aestronglyMeasurable hP).trans_lt (ENNReal.add_lt_top.mpr
      ⟨(eLpNorm_add_le ma ma hP).trans_lt (ENNReal.add_lt_top.mpr ⟨hA, hA⟩), hg⟩)
  have low (s : ℝ) (hs : 0 < s) (x : E) : ‖lowInverse a F s x‖ₑ ≤ A x := by
    rw [lowInverse_kernel a F mf hi hs]
    have hM := est g mg 0 x s hs
    simp only [norm_zero, add_zero, one_pow, ENNReal.ofReal_one, mul_one] at hM
    refine (enorm_integral_le_lintegral_enorm _).trans (le_trans ?_ hM)
    apply lintegral_mono
    intro y
    change ‖((s ^ 4)⁻¹ • φ (s⁻¹ • (x - y))) * U y‖ₑ ≤ _
    rw [← ofReal_norm_eq_enorm, norm_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (pow_pos hs _)), inv_mul_eq_div,
      ENNReal.ofReal_mul (div_nonneg (norm_nonneg _) (pow_nonneg hs.le _))]
    simp only [ofReal_norm_eq_enorm, g, le_refl]
  have triangle (z w : ℂ) : ‖z - w‖ₑ ≤ ‖z‖ₑ + ‖w‖ₑ := by
    simpa only [← sub_eq_add_neg, enorm_neg] using enorm_add_le z (-w)
  refine eLpNorm_tendsto_zero_of_domination hpos _ hd
    (fun n => ((annularInput F hF n).continuous.sub mu).aestronglyMeasurable) ?_ ?_
  · intro n x
    change ‖annularInput F hF n x - U x‖ₑ ≤ A x + A x + g x
    refine (triangle _ _).trans (add_le_add_right ?_ _)
    rw [cut_sub_low F hF hi]
    exact (triangle _ _).trans
      (add_le_add (low _ (inv_pos.mpr (inputCutoffRadius_pos n)) x) (low _ (inputCutoffRadius_pos n) x))
  · filter_upwards with x
    simpa only [Pi.sub_apply, U, sub_self] using
      (annularInput_tendsto_pointwise F hF hi x).sub (tendsto_const_nhds (x := U x))

end Burnett.A02.FrequencySplit.CMBilinearDual
