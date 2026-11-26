import Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension
import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicActualMultiplier
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualCutoffLp
import Burnett.Analysis.Fourier.SharpProjection

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.A07

open Burnett.A06 Burnett.A02.FrequencySplit Burnett.A02.FrequencySplit.CMBilinearDual
open Burnett.Fourier MeasureTheory Metric Set Filter
open scoped ContDiff ENNReal FourierTransform Topology

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem tau_positive : 0 < tau := mul_pos (by norm_num) Real.pi_pos

private def angularSpectrum (i : SphereHarmonicIndex) (H : SchwartzMap E ℂ) (ν : E) : ℂ :=
  (sphereHarmonicMultiplierSymbol i.1 i.2 (tau • ν) : ℂ) * 𝓕 (H : E → ℂ) ν

private theorem angularSpectrum_eq (i : SphereHarmonicIndex) (H : SchwartzMap E ℂ) :
    angularSpectrum i H = fun ν => (sphereHarmonicMultiplierSymbol i.1 i.2 ν : ℂ) * 𝓕 (H : E → ℂ) ν := by
  funext ν
  unfold angularSpectrum sphereHarmonicMultiplierSymbol
  rw [sphereHarmonicRadialSymbol_smul _ _ _ tau_positive ν]

private theorem angularSpectrum_smooth (i : SphereHarmonicIndex) (H : SchwartzMap E ℂ) :
    ContDiffOn ℝ ∞ (angularSpectrum i H) {ν | ν ≠ 0} := by
  rw [angularSpectrum_eq]
  apply (Complex.ofRealCLM.contDiff.comp_contDiffOn (sphereHarmonicRadialSymbol_contDiffOn _ _)).mul
  exact ((SchwartzMap.fourierTransformCLM ℂ H).smooth ⊤).contDiffOn

private theorem angularSpectrum_integrable (i : SphereHarmonicIndex) (H : SchwartzMap E ℂ)
    (m : BoundedSymbol E) (hm : ∀ ξ, m ξ = (sphereHarmonicMultiplierSymbol i.1 i.2 ξ : ℂ)) :
    Integrable (angularSpectrum i H) := by
  rw [angularSpectrum_eq]
  simp_rw [← hm]
  exact (SchwartzMap.fourierTransformCLM ℂ H).integrable.bdd_mul m.measurable ⟨m.bound,m.norm_le⟩

private theorem physicalAngularMultiplier_ae_inverse (i : SphereHarmonicIndex) (H : SchwartzMap E ℂ)
    (m : BoundedSymbol E) (hm : ∀ ξ, m ξ = (sphereHarmonicMultiplierSymbol i.1 i.2 ξ : ℂ))
    (Y : FirstOrderLp 4 →L[ℂ] FirstOrderLp 4)
    (hY : (Y (H.toLp 4 volume) : E → ℂ) =ᵐ[volume] (fourierMultiplier m (H.toLp 2 volume) : E → ℂ)) :
    (Y (H.toLp 4 volume) : E → ℂ) =ᵐ[volume] 𝓕⁻ (angularSpectrum i H) := by
  obtain ⟨_,_,modes⟩ := exists_sphereHarmonicMultiplier_Lp_bound 4 (by norm_num)
  let P := ENNReal.ofReal (4 : ℝ)
  letI : Fact (1 ≤ P) := ⟨by dsimp [P]; norm_num⟩
  obtain ⟨m',S,hm',_,hTogether,hSchwartz⟩ := modes i.1 i.2
  have same : fourierMultiplier m (H.toLp 2 volume) = fourierMultiplier m' (H.toLp 2 volume) := by
    rw [fourierMultiplier_congr_ae m m' (Eventually.of_forall fun ξ => (hm ξ).trans (hm' ξ).symm)]
  have h₂ := hTogether (H : E → ℂ) (H.memLp 2 volume) (H.memLp P volume)
  change (S (H.toLp P volume) : E → ℂ) =ᵐ[volume] (fourierMultiplier m' (H.toLp 2 volume) : E → ℂ) at h₂
  rw [same] at hY
  refine hY.trans (h₂.symm.trans ((hSchwartz H).trans ?_))
  exact Eventually.of_forall fun x => radianAction_eq_orderOne (sphereHarmonicMultiplierSymbol i.1 i.2) H x

private theorem angularAnnularInput_radianFourier (i : SphereHarmonicIndex) (H : SchwartzMap E ℂ)
    (n : ℕ) (p : E) :
    radianFourier (annularInput (angularSpectrum i H) (angularSpectrum_smooth i H) n : E → ℂ) p =
      (inputAnnularMask n (tau⁻¹ • p) : ℂ) *
        ((sphereHarmonicMultiplierSymbol i.1 i.2 p : ℂ) * radianFourier H p) := by
  have hscale : tau • (tau⁻¹ • p) = p := by
    rw [smul_smul, mul_inv_cancel₀ tau_positive.ne', one_smul]
  calc
    _ = 𝓕 (annularInput (angularSpectrum i H) (angularSpectrum_smooth i H) n : E → ℂ) (tau⁻¹ • p) := by
      rw [← radianFourier_scaled, hscale]
    _ = _ := by
      rw [annularInput_fourier, angularSpectrum, ← radianFourier_scaled, hscale]

private theorem angularMode_radianHighPair_tendsto (b : OrderOneSymbol ℂ)
    (H u w : SchwartzMap E ℂ) (i : SphereHarmonicIndex)
    (m : BoundedSymbol E) (hm : ∀ ξ, m ξ = (sphereHarmonicMultiplierSymbol i.1 i.2 ξ : ℂ)) :
    Tendsto (fun n => radianHighPair b
      (annularInput (angularSpectrum i H) (angularSpectrum_smooth i H) n) u w) atTop
      (𝓝 (radianHighPair (fun p => (sphereHarmonicMultiplierSymbol i.1 i.2 p.1 : ℂ) * (b : Joint → ℂ) p) H u w)) := by
  let mode (p : Joint) := (sphereHarmonicMultiplierSymbol i.1 i.2 p.1 : ℂ) * (b : Joint → ℂ) p
  let P := orderOneWeightedSeminorm ℂ 0 b
  have hP : 0 ≤ P := apply_nonneg _ _
  have hMeas : Measurable (sphereHarmonicMultiplierSymbol i.1 i.2 : E → ℝ) :=
    measurable_of_continuousOn_compl_singleton 0 (sphereHarmonicRadialSymbol_contDiffOn _ _).continuousOn
  have hh : Measurable mode := (Complex.continuous_ofReal.measurable.comp (hMeas.comp measurable_fst)).mul
    b.measurable_symbol
  have hg (p : Joint) : ‖mode p‖ ≤ (m.bound*P) * (1 + ‖p.1‖ + ‖p.2‖) := by
    change ‖(sphereHarmonicMultiplierSymbol i.1 i.2 p.1 : ℂ) * (b : Joint → ℂ) p‖ ≤ _
    rw [norm_mul, ← hm p.1, mul_assoc]
    exact mul_le_mul (m.norm_le _) (b.norm_apply_le_weightedSeminorm_zero p) (norm_nonneg _) m.bound_nonneg
  let A := radianHighPairWeight mode H u w
  have hA : Integrable A := integrable_radianHighPairWeight_of_orderOne mode hh (m.bound*P)
    (mul_nonneg m.bound_nonneg hP) hg H u w
  let mask (n : ℕ) (p : Joint) := (inputAnnularMask n (tau⁻¹ • p.1) : ℂ)
  have cm (n : ℕ) : Continuous (mask n) := Complex.continuous_ofReal.comp
    ((inputAnnularMask_contDiff n).continuous.comp (continuous_const.smul continuous_fst))
  have hLow : ∀ᵐ p : Joint ∂volume, p.1 ≠ 0 := by
    rw [Measure.volume_eq_prod E E]
    exact Measure.quasiMeasurePreserving_fst.ae ((Set.countable_singleton (0 : E)).ae_notMem volume)
  have hLim : ∀ᵐ p ∂volume, Tendsto (fun n => mask n p * A p) atTop (𝓝 (A p)) := by
    filter_upwards [hLow] with p hp
    apply tendsto_const_nhds.congr'
    have hz : tau⁻¹ • p.1 ≠ 0 := smul_ne_zero (inv_ne_zero tau_positive.ne') hp
    filter_upwards [inputAnnularMask_eventually_one hz] with n hn
    simp only [mask, hn, Complex.ofReal_one, one_mul]
  have limit := tendsto_integral_of_dominated_convergence (F := fun n p => mask n p * A p)
    (fun p => ‖A p‖) (fun n => (cm n).aestronglyMeasurable.mul hA.1) hA.norm
    (fun n => Eventually.of_forall fun p => by
      rw [norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _) (inputAnnularMask_norm_le _ _)) hLim
  have scale := (continuous_const_smul ((tau^8)⁻¹ : ℝ)).continuousAt.tendsto.comp limit
  refine scale.congr (fun n => ?_)
  unfold radianHighPair
  change (tau^8)⁻¹ • (∫ p, mask n p * A p) = _
  apply congrArg (fun z : ℂ => (tau^8)⁻¹ • z)
  apply integral_congr_ae
  filter_upwards with p
  simp only [A, mode, mask, radianHighPairWeight, angularAnnularInput_radianFourier]
  ring

/-- Evaluating the actual Cartesian extension on the physical harmonic
multiplier of a Schwartz low field agrees with the original weighted spectrum. -/
theorem physicalAngularMultiplier_pair_eq
    (b : OrderOneSymbol ℂ) (u H w : SchwartzMap E ℂ) (i : SphereHarmonicIndex)
    (m : BoundedSymbol E) (hm : ∀ ξ, m ξ = (sphereHarmonicMultiplierSymbol i.1 i.2 ξ : ℂ))
    (Y : FirstOrderLp 4 →L[ℂ] FirstOrderLp 4)
    (hY : (Y (H.toLp 4 volume) : E → ℂ) =ᵐ[volume] (fourierMultiplier m (H.toLp 2 volume) : E → ℂ))
    (T : FirstOrderLp 4 →L[ℂ] FirstOrderLp 2)
    (hT : ∀ f v : SchwartzMap E ℂ, inner ℂ (v.toLp 2 volume) (T (f.toLp 4 volume)) =
      radianHighPair b f u v) :
    inner ℂ (w.toLp 2 volume) (T (Y (H.toLp 4 volume))) =
      radianHighPair (fun p => (sphereHarmonicMultiplierSymbol i.1 i.2 p.1 : ℂ) * (b : Joint → ℂ) p) H u w := by
  let F := angularSpectrum i H
  let v := annularInput F (angularSpectrum_smooth i H)
  let U := Y (H.toLp 4 volume)
  have hU : (U : E → ℂ) =ᵐ[volume] 𝓕⁻ F := physicalAngularMultiplier_ae_inverse i H m hm Y hY
  have hMem : MemLp (𝓕⁻ F) 4 volume := (memLp_congr_ae hU).mp (Lp.memLp U)
  have hMem' : MemLp (𝓕⁻ F) (ENNReal.ofReal (4 : ℝ)) volume := by simpa using hMem
  have hFreq := annularInput_tendsto_eLpNorm F (angularSpectrum_smooth i H)
    (angularSpectrum_integrable i H m hm) (by norm_num : (1 : ℝ) < 4) hMem'
  have hAnn : Tendsto (fun n => (v n).toLp 4 volume) atTop (𝓝 U) := by
    have hEq : hMem.toLp (𝓕⁻ F) = U := Lp.ext (hMem.coeFn_toLp.trans hU.symm)
    rw [← hEq]
    apply Lp.tendsto_Lp_of_tendsto_eLpNorm (𝓕⁻ F) hMem
    have hn (n : ℕ) : eLpNorm (((v n).toLp 4 volume : E → ℂ) - 𝓕⁻ F) 4 volume =
        eLpNorm ((v n : E → ℂ) - 𝓕⁻ F) 4 volume :=
      eLpNorm_congr_ae (((v n).coeFn_toLp 4 volume).sub EventuallyEq.rfl)
    simpa only [hn, v, ENNReal.ofReal_ofNat] using hFreq
  have hCont : Continuous (fun y : FirstOrderLp 4 => inner ℂ (w.toLp 2 volume) (T y)) :=
    continuous_const.inner T.continuous
  have physical := (hCont.tendsto U).comp hAnn
  have spectral := angularMode_radianHighPair_tendsto b H u w i m hm
  exact tendsto_nhds_unique (physical.congr (fun n => hT (v n) w)) spectral

end Burnett.A07
