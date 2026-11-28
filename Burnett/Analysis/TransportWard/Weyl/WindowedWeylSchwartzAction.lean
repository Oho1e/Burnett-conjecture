import Burnett.Analysis.TransportWard.Weyl.WindowedWeylFullSymbol
import Burnett.Analysis.TransportWard.Weyl.WindowedWeylKernel
import Burnett.Analysis.TransportWard.Weyl.WeylBaseSupport

set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option maxRecDepth 1900

noncomputable section

namespace Burnett.V03

open Function Filter MeasureTheory Set Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.CarlesonEmbedding (firstOrderAction_contDiff_of_pureBaseOrder)
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open scoped ContDiff ComplexConjugate

/-- The exact real double-cutoff Weyl left action takes values in the same
Schwartz test domain, with support in the original output cutoff. -/
theorem exists_windowedWeylSchwartz_selfAdjoint
    (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β))
    (hReal : ∀ x ξ, conj (β x ξ) = β x ξ) :
    ∃ B : SchwartzMap E ℂ → SchwartzMap E ℂ,
      (∀ u x, B u x = firstOrderAction (windowedWeylLeftSymbol θ β R h) u x) ∧
      (∀ u, tsupport (B u : E → ℂ) ⊆ tsupport θ) ∧
      ∀ f v : SchwartzMap E ℂ, (∫ x, conj (v x) * B f x) = ∫ x, conj (B v x) * f x := by
  let a := windowedWeylLeftSymbol θ β R h
  have ha := windowedWeyl_leftSymbol_scaled_order_one θ β R h hAmp hPlateau hβ
  have hBase (u : SchwartzMap E ℂ) : tsupport (firstOrderAction a u) ⊆ tsupport θ := by
    apply closure_minimal _ (isClosed_tsupport θ)
    intro x hx
    by_contra hOut
    apply hx
    have hZero (ξ : E) : a x ξ = 0 := windowedWeylLeftSymbol_eq_zero_of_output θ β R h x ξ
      (image_eq_zero_of_notMem_tsupport hOut)
    rw [firstOrderAction_eq_leftActionIntegrand]
    simp only [leftActionIntegrand,hZero,mul_zero,zero_mul,integral_zero]
  have hCompact (u : SchwartzMap E ℂ) : HasCompactSupport (firstOrderAction a u) :=
    hθc.of_isClosed_subset (isClosed_tsupport _) (hBase u)
  let B (u : SchwartzMap E ℂ) := (hCompact u).toSchwartzMap
    (firstOrderAction_contDiff_of_pureBaseOrder ha.smooth ha.pureBase u)
  have hB := windowedWeyl_leftAction_formallySymmetric θ β R h hθ hθc
    (hβ.smooth.of_le (by simp)) hβ.firstBaseFrequency.frequency hReal
  exact ⟨B,fun _ _ => rfl,hBase,fun f v => hB v f⟩

end Burnett.V03
