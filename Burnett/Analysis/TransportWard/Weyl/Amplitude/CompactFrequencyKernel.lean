import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactFrequencyParameterIntegral
import Burnett.Analysis.TransportWard.Weyl.PatchFourierPhase
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option maxHeartbeats 4300000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff FourierTransform

/-- An actual inverse Fourier kernel for a compact frequency cutoff. -/
def compactFrequencyKernel (a : E → E → ℂ) (χ : E → ℝ) (q : E × E) : ℂ :=
  (𝓕⁻ (fun ξ => (χ ξ : ℂ) * a q.1 ξ)) q.2

private theorem patch_fourier_phase_contDiff :
    ContDiff ℝ 1 (fun p : E × E => patchFourierPhase p.1 p.2) := by
  have hinner : ContDiff ℝ 1 (fun p : E × E => inner ℝ p.1 p.2) := contDiff_inner
  have ht : ContDiff ℝ 1 (fun p : E × E => tau * inner ℝ p.1 p.2) := contDiff_const.mul hinner
  have harg : ContDiff ℝ 1 (fun p : E × E => (↑(tau * inner ℝ p.1 p.2) : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp ht).mul contDiff_const
  have hexpc : ContDiff ℂ 1 Complex.exp := Complex.contDiff_exp
  have hexp : ContDiff ℝ 1 Complex.exp := hexpc.restrict_scalars ℝ
  change ContDiff ℝ 1 (Complex.exp ∘ fun p : E × E => (↑(tau * inner ℝ p.1 p.2) : ℂ) * Complex.I)
  exact hexp.comp harg

private theorem compact_frequency_kernel_integral (a : E → E → ℂ) (χ : E → ℝ) (q : E × E) :
    compactFrequencyKernel a χ q = ∫ ξ : E, (patchFourierPhase ξ q.2 * (χ ξ : ℂ)) * a q.1 ξ := by
  simp only [compactFrequencyKernel, Real.fourierIntegralInv_eq', smul_eq_mul, Burnett.Microlocal.Overlap.baseFourierPhase, mul_assoc]

/-- The compact frequency band is jointly C¹. Its derivative in a base
direction is the same band applied to the actual derivative of its symbol. -/
theorem compact_frequency_kernel_contDiff_and_base (a : E → E → ℂ) (χ : E → ℝ)
    (R : ℝ) (asmooth : ContDiff ℝ 1 (Function.uncurry a)) (χsmooth : ContDiff ℝ 1 χ)
    (χsupport : ∀ ξ, ξ ∉ closedBall (0 : E) R → χ ξ = 0) :
    ContDiff ℝ 1 (compactFrequencyKernel a χ) ∧
    ∀ x z e : E, fderiv ℝ (compactFrequencyKernel a χ) (x,z) (e,0) =
      compactFrequencyKernel (fun y ξ => fderiv ℝ (fun t => a t ξ) y e) χ (x,z) := by
  let F (q : E × E) (ξ : E) := (patchFourierPhase ξ q.2 * (χ ξ : ℂ)) * a q.1 ξ
  have cfst : ContDiff ℝ 1 (Prod.fst : (E × E) × E → E × E) := contDiff_fst
  have csnd : ContDiff ℝ 1 (Prod.snd : (E × E) × E → E) := contDiff_snd
  have xD : ContDiff ℝ 1 (fun p : (E × E) × E => p.1.1) :=
    (show ContDiff ℝ 1 (Prod.fst : E × E → E) from contDiff_fst).comp cfst
  have zD : ContDiff ℝ 1 (fun p : (E × E) × E => p.1.2) :=
    (show ContDiff ℝ 1 (Prod.snd : E × E → E) from contDiff_snd).comp cfst
  have phase : ContDiff ℝ 1 (fun p : (E × E) × E => patchFourierPhase p.2 p.1.2) := by
    change ContDiff ℝ 1 ((fun r : E × E => patchFourierPhase r.1 r.2) ∘ fun p : (E × E) × E => (p.2,p.1.2))
    exact patch_fourier_phase_contDiff.comp (csnd.prodMk zD)
  have cχ : ContDiff ℝ 1 (fun p : (E × E) × E => (χ p.2 : ℂ)) := by
    change ContDiff ℝ 1 ((Complex.ofRealCLM : ℝ → ℂ) ∘ χ ∘ (Prod.snd : (E × E) × E → E))
    exact Complex.ofRealCLM.contDiff.comp (χsmooth.comp csnd)
  have ca : ContDiff ℝ 1 (fun p : (E × E) × E => a p.1.1 p.2) := by
    change ContDiff ℝ 1 (Function.uncurry a ∘ fun p : (E × E) × E => (p.1.1,p.2))
    exact asmooth.comp (xD.prodMk csnd)
  have smooth : ContDiff ℝ 1 (Function.uncurry F) := (phase.mul cχ).mul ca
  have supp (q : E × E) (ξ : E) (hξ : ξ ∉ closedBall (0 : E) R) : F q ξ = 0 := by
    simp [F, χsupport ξ hξ]
  obtain ⟨diff,integralDeriv⟩ := compact_frequency_parameter_integral_contDiff F R smooth supp
  have integral : compactFrequencyKernel a χ = (fun q => ∫ ξ : E, F q ξ) :=
    funext fun q => compact_frequency_kernel_integral a χ q
  constructor
  · rwa [integral]
  · intro x z e
    have D (ξ : E) : compactFrequencyParameterDerivative F (x,z) ξ (e,0) =
        (patchFourierPhase ξ z * (χ ξ : ℂ)) * fderiv ℝ (fun t => a t ξ) x e := by
      have asection : DifferentiableAt ℝ (fun t => a t ξ) x :=
        ((asmooth.comp (contDiff_id.prodMk contDiff_const)).differentiable le_rfl x)
      have sectionHas := asection.hasFDerivAt.const_mul (patchFourierPhase ξ z * (χ ξ : ℂ))
      have Fsection : HasFDerivAt (fun t : E => F (t,z) ξ)
          ((compactFrequencyParameterDerivative F (x,z) ξ).comp (ContinuousLinearMap.inl ℝ E E)) x := by
        have pair₁ : HasFDerivAt (fun t : E × E => (t,ξ))
            (ContinuousLinearMap.inl ℝ (E × E) E) (x,z) := hasFDerivAt_prodMk_left _ _
        have pair₂ : HasFDerivAt (fun t : E => (t,z))
            (ContinuousLinearMap.inl ℝ E E) x := hasFDerivAt_prodMk_left _ _
        have d := (smooth.differentiable le_rfl ((x,z),ξ)).hasFDerivAt
        exact (d.comp (x,z) pair₁).comp x pair₂
      exact congrArg (fun T : E →L[ℝ] ℂ => T e) (Fsection.unique sectionHas)
    rw [integral, (integralDeriv (x,z)).2.fderiv, ContinuousLinearMap.integral_apply (integralDeriv (x,z)).1,
      compact_frequency_kernel_integral]
    exact integral_congr_ae (Eventually.of_forall D)

end Burnett.A03
