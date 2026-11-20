import Burnett.Analysis.CubicEnergy.JointMultiplier.BilinearKernel
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace ContDiff

theorem splitFreq_inner (u v : Freq8) :
    inner ℝ u v = inner ℝ (splitFreq u).1 (splitFreq v).1 + inner ℝ (splitFreq u).2 (splitFreq v).2 := by
  simp only [PiLp.inner_apply,Fintype.sum_sum_type]
  rfl

/-- The Fourier multiplier of the normalized translated-input kernel at scale s
is precisely a(sη,sξ) in the two original frequency coordinates. -/
theorem blockKernel_multiplier (a : Joint → ℂ) (ha : HasCompactSupport a) (hs : ContDiff ℝ ∞ a)
    (s : ℝ) (z : Joint) :
    (∫ y : Joint, Complex.exp ((↑(-2*Real.pi*(inner ℝ (s • y.1) z.1 + inner ℝ (s • y.2) z.2)) : ℂ)*Complex.I) *
      blockKernel a y) = a (s • z) := by
  let A : SchwartzMap Freq8 ℂ :=
    (ha.comp_homeomorph splitFreq.toHomeomorph).toSchwartzMap (hs.comp splitFreq.contDiff)
  let K := (SchwartzMap.fourierTransformCLE ℂ).symm A
  have hK : (K : Freq8 → ℂ) = 𝓕⁻ (fun ξ : Freq8 => a (splitFreq ξ)) :=
    SchwartzMap.fourierTransformCLE_symm_apply _ _
  have hInv : 𝓕 (K : Freq8 → ℂ) (splitFreq.symm (s • z)) = a (s • z) := by
    have h := congrArg (fun g : SchwartzMap Freq8 ℂ => g (splitFreq.symm (s • z)))
      ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply A)
    change 𝓕 (K : Freq8 → ℂ) _ = a (splitFreq (splitFreq.symm (s • z))) at h
    exact h.trans (congrArg a (splitFreq.apply_symm_apply _))
  rw [← hInv,Real.fourierIntegral_eq']
  let T := fun y : Joint => Complex.exp ((↑(-2*Real.pi*(inner ℝ (s • y.1) z.1 + inner ℝ (s • y.2) z.2)) : ℂ)*Complex.I) * blockKernel a y
  change (∫ y, T y) = _
  rw [← (splitFreq_preserves_volume.integral_comp splitFreq.toHomeomorph.measurableEmbedding T)]
  apply integral_congr_ae
  filter_upwards with u
  simp only [T,blockKernel,ContinuousLinearEquiv.symm_apply_apply,hK,smul_eq_mul,
    splitFreq_inner u (splitFreq.symm (s • z)),ContinuousLinearEquiv.apply_symm_apply,
    Prod.smul_fst,Prod.smul_snd,real_inner_smul_left,real_inner_smul_right]

end Burnett.A02.FrequencySplit
