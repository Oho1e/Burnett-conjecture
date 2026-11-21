import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletOperator
import Burnett.Analysis.PrincipalEnergy.Commutator.RenormalizedKernel
import Burnett.Analysis.H1FourierEnergy

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.HminusWeightedDual (fourier_pderiv)
open Burnett.Microlocal.AngularCommutator (fourierL2Equiv_eq_fourier_ae_of_integrable)
open scoped FourierTransform

/-- The Schwartz realization of the actual wavelet convolution, using
exactly the same Fourier symbol as the existing L² action. -/
def schwartzWaveletAction (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    (f : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  let e := (LinearEquiv.smulOfNeZero (K := ℝ) (M := Space) s hs.ne').toContinuousLinearEquiv
  (SchwartzMap.fourierTransformCLE ℂ).symm (scalarSchwartzProduct
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (compactWaveletFrequency ψ))
    (SchwartzMap.fourierTransformCLM ℂ f))

theorem fourier_schwartzWaveletAction (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    (f : SchwartzMap Space ℂ) (ξ : Space) :
    𝓕 (schwartzWaveletAction ψ s hs f : Space → ℂ) ξ =
      waveletSymbol ψ s ξ*𝓕 (f : Space → ℂ) ξ := by
  change ((SchwartzMap.fourierTransformCLE ℂ) (schwartzWaveletAction ψ s hs f)) ξ=_
  rw [schwartzWaveletAction,ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem schwartzWaveletAction_toLp (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    (f : SchwartzMap Space ℂ) :
    (schwartzWaveletAction ψ s hs f).toLp 2 volume =
      fourierMultiplier (waveletSymbol ψ s) (f.toLp 2 volume) := by
  let g := schwartzWaveletAction ψ s hs f
  apply fourierL2Equiv.injective
  rw [fourier_fourierMultiplier]
  apply Lp.ext
  have hG := fourierL2Equiv_eq_fourier_ae_of_integrable (g : Space → ℂ) g.integrable (g.memLp 2 volume)
  have hF := fourierL2Equiv_eq_fourier_ae_of_integrable (f : Space → ℂ) f.integrable (f.memLp 2 volume)
  filter_upwards [hG,hF,symbolL2_ae (waveletSymbol ψ s) (fourierL2Equiv (f.toLp 2 volume))] with ξ hg hf hm
  change fourierL2Equiv (g.toLp 2 volume) ξ =
    symbolL2 (waveletSymbol ψ s) (fourierL2Equiv (f.toLp 2 volume)) ξ
  change fourierL2Equiv (g.toLp 2 volume) ξ=𝓕 (g : Space → ℂ) ξ at hg
  change fourierL2Equiv (f.toLp 2 volume) ξ=𝓕 (f : Space → ℂ) ξ at hf
  rw [hg,hm,hf]
  exact fourier_schwartzWaveletAction ψ s hs f ξ

theorem schwartzWaveletAction_eq_actual (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    (f : SchwartzMap Space ℂ) :
    (schwartzWaveletAction ψ s hs f : Space → ℂ)=compactWaveletAction ψ s f := by
  let g := schwartzWaveletAction ψ s hs f
  have hL := g.coeFn_toLp 2 (volume : Measure Space)
  rw [schwartzWaveletAction_toLp ψ s hs f] at hL
  have hR := waveletMultiplier_ae_eq_action ψ s hs f f.integrable (f.memLp 2 volume)
  exact Measure.eq_of_ae_eq (hL.symm.trans hR) g.continuous
    (compactWaveletAction_continuous ψ s hs f f.integrable)

theorem schwartzWaveletAction_pderiv (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    (f : SchwartzMap Space ℂ) (v : Space) :
    SchwartzMap.pderivCLM ℂ v (schwartzWaveletAction ψ s hs f)=
      schwartzWaveletAction ψ s hs (SchwartzMap.pderivCLM ℂ v f) := by
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext ξ
  change 𝓕 (SchwartzMap.pderivCLM ℂ v (schwartzWaveletAction ψ s hs f) : Space → ℂ) ξ=
    𝓕 (schwartzWaveletAction ψ s hs (SchwartzMap.pderivCLM ℂ v f) : Space → ℂ) ξ
  rw [fourier_pderiv,fourier_schwartzWaveletAction,fourier_schwartzWaveletAction,fourier_pderiv]
  ring

end Burnett.Analysis.CarlesonEmbedding
