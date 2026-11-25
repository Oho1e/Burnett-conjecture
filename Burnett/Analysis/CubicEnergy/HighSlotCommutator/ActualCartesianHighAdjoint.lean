import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CartesianHighSlotAngularJets

set_option autoImplicit false
set_option maxHeartbeats 4200000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal ComplexConjugate

/-- The original high adjoint has low input L⁴, high input L⁴, and
high test L², by the second exponent placement on the original symbol
and the exact real-coefficient high-slot adjunction identity. -/
theorem exists_regularizedLowCartesian_highAdjoint_rough_angularJetBound
    (η χ : ℝ → ℝ) {ρ r R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hr : 0<r) (hR : 1≤R)
    (hη : ContDiff ℝ ∞ η) (hηzero : ∀ z≤r, η z=0) (hηone : ∀ z≥R, η z=1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ z≥ρ^2, χ z=0) :
    ∃ (K : ℕ) (C : ℝ), 0≤C ∧ ∀ {V : Set Joint}, IsOpen V →
      closedBall (0:E) ρ ×ˢ sphere (0:E) 1 ⊆ V →
      ∀ (b : Joint → ℂ) (A : ℝ), 0≤A → ContDiffOn ℝ ∞ b V →
      (∀ n≤K, ∀ z ∈ closedBall (0:E) ρ ×ˢ sphere (0:E) 1,
        ‖iteratedFDeriv ℝ n b z‖≤A) →
      ∀ (d : SchwartzMap E ℝ) (L : ℝ≥0), LipschitzWith L d →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (highAdjointSymbol (regularizedLowCartesianSymbol η χ b)) d f g h‖ₑ≤
        (L : ℝ≥0∞)*ENNReal.ofReal (C*A)*triLpMass f g h 4 4 2 := by
  obtain ⟨K,C,hC,forward⟩ := exists_regularizedLowCartesian_highSlot_common_angularJetBound
    η χ hρ hρ' hr hR hη hηzero hηone hχ hcut
  refine ⟨K,C,hC,?_⟩
  intro V hV hContains b A hA hb hJet d L hd f g h
  let a := regularizedLowCartesianSymbol η χ b
  have adj := radianHighCommutatorPair_highAdjoint a d (gapConjugate f) h g
  have eq : (fun x => conj (gapConjugate f x)) = (f : E → ℂ) := by
    funext x
    exact starRingEnd_self_apply (f x)
  rw [eq] at adj
  change ‖radianHighCommutatorPair (highAdjointSymbol a) d f g h‖ₑ≤_
  rw [adj,enorm_neg,RCLike.enorm_conj]
  have H := forward true hV hContains b A hA hb hJet d L hd (gapConjugate f) h g
  change ‖radianHighCommutatorPair a d (gapConjugate f) h g‖ₑ≤
    (L : ℝ≥0∞)*ENNReal.ofReal (C*A)*triLpMass (gapConjugate f) h g 4 2 4 at H
  have N : eLpNorm (gapConjugate f : E → ℂ) (ENNReal.ofReal 4) volume =
      eLpNorm (f : E → ℂ) (ENNReal.ofReal 4) volume :=
    eLpNorm_congr_norm_ae (.of_forall fun x => Complex.norm_conj (f x))
  have mass : triLpMass (gapConjugate f) h g 4 2 4 = triLpMass f g h 4 4 2 := by
    unfold triLpMass
    rw [N,mul_right_comm]
  rw [mass] at H
  exact H

end Burnett.A06
