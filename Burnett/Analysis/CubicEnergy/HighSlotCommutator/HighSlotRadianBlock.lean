import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotLipschitzBlock
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotAdjoint
import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowPairing

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.A06

open MeasureTheory
open Burnett.A02.FrequencySplit
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform

private def conjugateTest (v : SchwartzMap E ℂ) : SchwartzMap E ℂ where
  toFun := Complex.conjLIE ∘ (v : E → ℂ)
  smooth' := Complex.conjCLE.contDiff.comp v.smooth'
  decay' k n := by
    obtain ⟨D, _, hD⟩ := v.decay k n
    refine ⟨D, fun x => ?_⟩
    rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left]
    exact hD x

private def blockTestDensity (a : Joint → ℂ) (s : ℝ)
    (f g h : SchwartzMap E ℂ) (yx : Joint × E) : ℂ :=
  blockKernel a yx.1 * (f (yx.2 - s • yx.1.1) * g (yx.2 - s • yx.1.2) * h yx.2)

private theorem blockTestDensity_integrable (a : Joint → ℂ) (ha : HasCompactSupport a)
    (hs : ContDiff ℝ ∞ a) (s : ℝ) (f g h : SchwartzMap E ℂ) :
    Integrable (blockTestDensity a s f g h) ((volume : Measure Joint).prod (volume : Measure E)) := by
  obtain ⟨hKI,hKC⟩ := blockKernel_integrable a ha hs
  have hC : Continuous (blockTestDensity a s f g h) := by
    unfold blockTestDensity
    fun_prop
  refine ⟨hC.aestronglyMeasurable, ?_⟩
  change (∫⁻ yx : Joint × E, ‖blockTestDensity a s f g h yx‖ₑ
    ∂((volume : Measure Joint).prod (volume : Measure E))) < ⊤
  rw [lintegral_prod _ hC.enorm.aemeasurable]
  letI : ENNReal.HolderTriple 4 4 2 := by
    have hR : (4 : ℝ).HolderTriple 4 2 := ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using hR.ennrealOfReal
  exact (dilated_kernel_trilinear_bound
    (p := 4) (s := 4) (r := 2) (t := 2) (blockKernel a) hKC.measurable f g h s).trans_lt
      (ENNReal.mul_lt_top hKI.hasFiniteIntegral
        (ENNReal.mul_lt_top (ENNReal.mul_lt_top (f.eLpNorm_lt_top 4 volume) (g.eLpNorm_lt_top 4 volume))
          (h.eLpNorm_lt_top 2 volume)))

private theorem blockTestDensity_integral_eq (a : Joint → ℂ) (ha : HasCompactSupport a)
    (hs : ContDiff ℝ ∞ a) (s : ℝ) (f g h : SchwartzMap E ℂ) :
    (∫ yx : Joint × E, blockTestDensity a s f g h yx
      ∂((volume : Measure Joint).prod (volume : Measure E))) = testedBlock a s f g h := by
  rw [integral_prod_symm _ (blockTestDensity_integrable a ha hs s f g h)]
  unfold testedBlock
  apply integral_congr_ae
  filter_upwards with x
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with y
  simp only [blockTestDensity, mul_assoc]

/-- The exact radian frequency symbol of a normalized reference block. -/
def radianHighReferenceBlock (a : Joint → ℂ) (s : ℝ) (p : Joint) : ℂ :=
  s⁻¹ • a ((s / tau) • p)

private theorem radianHighPair_reference (a : Joint → ℂ) (ha : HasCompactSupport a)
    (hs : ContDiff ℝ ∞ a) (s : ℝ) (f g h : SchwartzMap E ℂ) :
    radianHighPair (fun p => a ((s/tau) • p)) f g h = testedBlock a s f g (conjugateTest h) := by
  letI := jointVolume_haar
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have dimE : Module.finrank ℝ E = 4 := finrank_euclideanSpace_fin
  have dimJoint : Module.finrank ℝ Joint = 8 := by rw [Module.finrank_prod, dimE]
  have changeFreq := Measure.integral_comp_smul_of_nonneg (volume : Measure Joint)
    (radianHighPairWeight (fun p => a ((s/tau) • p)) f g h) tau (hR := hτ.le)
  rw [dimJoint] at changeFreq
  rw [radianHighPair, ← changeFreq, testedBlock_density a ha hs]
  apply integral_congr_ae
  filter_upwards with p
  have hadj : conj (radianFourier h (tau • (p.1 + p.2))) =
      𝓕 (conjugateTest h : E → ℂ) (-(p.1 + p.2)) := by
    rw [← radianFourier_scaled, smul_neg]
    exact (radianFourier_conj_neg h _).symm
  rw [radianFourier_scaled] at hadj
  have ratio : ((s/tau) * tau) = s := div_mul_cancel₀ _ hτ.ne'
  simp only [radianHighPairWeight, triDensity, smul_smul, ratio, Prod.smul_fst, Prod.smul_snd,
    ← smul_add, add_comm p.2 p.1, hadj, radianFourier_scaled, mul_assoc]

private theorem radianHighPair_smul_symbol (c : ℝ) (b : Joint → ℂ) (f g h : E → ℂ) :
    radianHighPair (c • b) f g h = c • radianHighPair b f g h := by
  have val : radianHighPairWeight (c • b) f g h = c • radianHighPairWeight b f g h := by
    funext p
    simp only [radianHighPairWeight, Pi.smul_apply, smul_mul_assoc]
  unfold radianHighPair
  rw [val]
  simp only [Pi.smul_apply, integral_smul]
  rw [smul_comm]

/-- On the original Schwartz products, the physical commutator block is
the manuscript's actual radian pairing with the same Lipschitz coefficient. -/
theorem highSlotBlockPair_eq_radianHighCommutatorPair (a : Joint → ℂ) (ha : HasCompactSupport a)
    (hs : ContDiff ℝ ∞ a) (s : ℝ) (d : E → ℝ)
    (f g h gd hd : SchwartzMap E ℂ)
    (hg : ∀ x, gd x = (d x : ℂ) * g x) (hh : ∀ x, hd x = (d x : ℂ) * h x) :
    highSlotBlockPair a s d f g h =
      radianHighCommutatorPair (radianHighReferenceBlock a s) d f g h := by
  have gEq : (gd : E → ℂ) = fun x => (d x : ℂ) * g x := funext hg
  have hEq : (hd : E → ℂ) = fun x => (d x : ℂ) * h x := funext hh
  change highSlotBlockPair a s d f g h =
    radianHighPair (s⁻¹ • (fun p => a ((s/tau) • p))) f (fun x => (d x : ℂ) * g x) h -
      radianHighPair (s⁻¹ • (fun p => a ((s/tau) • p))) f g (fun x => (d x : ℂ) * h x)
  rw [← gEq, ← hEq, radianHighPair_smul_symbol, radianHighPair_smul_symbol,
    radianHighPair_reference a ha hs, radianHighPair_reference a ha hs, ← smul_sub,
    ← blockTestDensity_integral_eq a ha hs, ← blockTestDensity_integral_eq a ha hs,
    ← integral_sub (blockTestDensity_integrable a ha hs s f gd (conjugateTest h))
      (blockTestDensity_integrable a ha hs s f g (conjugateTest hd)), ← integral_smul]
  unfold highSlotBlockPair
  apply integral_congr_ae
  filter_upwards with yx
  change highSlotBlockDensity a s d f g h yx.1 yx.2 =
    s⁻¹ •
      (blockKernel a yx.1 * (f (yx.2 - s • yx.1.1) * gd (yx.2 - s • yx.1.2) * conj (h yx.2)) -
        blockKernel a yx.1 * (f (yx.2 - s • yx.1.1) * g (yx.2 - s • yx.1.2) * conj (hd yx.2)))
  simp only [highSlotBlockDensity, hg, hh, map_mul, Complex.conj_ofReal, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_sub]
  ring

theorem radianHighCommutatorPair_referenceBlock_two_paper_bounds
    (a : Joint → ℂ) (ha : HasCompactSupport a) (hsmooth : ContDiff ℝ ∞ a)
    {s : ℝ} (hs : 0 < s) {d : E → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L d)
    (f g h gd hd : SchwartzMap E ℂ)
    (hg : ∀ x, gd x = (d x : ℂ) * g x) (hh : ∀ x, hd x = (d x : ℂ) * h x) :
    ‖radianHighCommutatorPair (radianHighReferenceBlock a s) d f g h‖ₑ ≤
      (L : ℝ≥0∞) * highSlotBlockMoment a * triLpMass f g h 4 4 2 ∧
    ‖radianHighCommutatorPair (radianHighReferenceBlock a s) d f g h‖ₑ ≤
      (L : ℝ≥0∞) * highSlotBlockMoment a * triLpMass f g h 4 2 4 := by
  rw [← highSlotBlockPair_eq_radianHighCommutatorPair a ha hsmooth s d f g h gd hd hg hh]
  exact highSlotBlockPair_two_paper_bounds a ha hsmooth hs hLip f g h

end Burnett.A06
