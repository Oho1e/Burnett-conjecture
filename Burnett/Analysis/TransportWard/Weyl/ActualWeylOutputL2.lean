import Burnett.Analysis.TransportWard.Weyl.ActualWeylCompactMatrixTest
import Burnett.Analysis.PrincipalEnergy.Localization.GlobalOrderOneH1Action

set_option autoImplicit false
set_option maxHeartbeats 2300000

noncomputable section

namespace Burnett.V03

open MeasureTheory Burnett.A03 Burnett.Analysis.CarlesonEmbedding
open Burnett.A02.FrequencySplit (E)
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.HminusReverse (schwartzH1Energy)
open scoped ComplexConjugate ContDiff

/-- Weyl testing the actual compact field costs one derivative in L².
The factor `-I` preserves the bound for the real cubic output. -/
theorem exists_windowedWeylRealOutput_L2_bound
    (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (hAmp : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hDir : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hθβ : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hθ : HasCompactSupport θ) (hβ : ScaledJointOrderOne (normalizedWeylSymbol β)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z w : SchwartzMap E ℂ, HasCompactSupport (z : E → ℂ) →
      (∀ x, w x = (-Complex.I) * firstOrderAction (windowedWeylLeftSymbol θ β R hAmp) z x) →
      ‖w.toLp 2 volume‖ ≤ C * Real.sqrt (schwartzH1Energy z) := by
  let a := windowedWeylLeftSymbol θ β R hAmp
  have hA := windowedWeyl_leftSymbol_scaled_order_one θ β R hAmp hDir hθβ hβ
  have hProper := windowedWeyl_leftSymbol_proper θ β R hAmp hθ
    hA.firstBaseFrequency.frequency hA.smooth.continuous
  obtain ⟨C, hC, hb⟩ := exists_firstOrderAction_global_h1_bound_of_properSupport
    hA.firstBaseFrequency hA.smooth hA.pureBase hProper
  refine ⟨C, hC, fun z w hz hw => ?_⟩
  obtain ⟨hMem, hBd⟩ := hb z hz
  have hNorm : ‖w.toLp 2 volume‖ = ‖hMem.toLp (firstOrderAction a z)‖ := by
    change ‖(w.memLp 2 volume).toLp (w : E → ℂ)‖ = _
    simp only [Lp.norm_toLp]
    congr 1
    apply eLpNorm_congr_norm_ae
    exact Filter.Eventually.of_forall fun x => by
      change ‖w x‖ = ‖firstOrderAction a z x‖
      rw [hw, norm_mul, norm_neg, Complex.norm_I, one_mul]
  rw [hNorm]
  exact hBd

end Burnett.V03
