import Burnett.Analysis.FrozenTransport.PatchCorrection.ExplicitThreeDivergenceTerms
import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualLowTriadInfrared
import Burnett.Analysis.FrozenTransport.PatchCorrection.UniformAngularJets

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000
noncomputable section
namespace Burnett.V11

open Set Metric Matrix MeasureTheory Burnett.A06 Burnett.A07 Burnett.A08 Burnett.V08 Burnett.P01
open Burnett.A02.FrequencySplit (E Joint radianFourier)
open scoped ContDiff Matrix BigOperators ENNReal NNReal ComplexConjugate

theorem exists_actualGauge_threeDivergenceTerms :
    ∃ (N : ℕ) (K : ℝ), 0 ≤ K ∧
    ∀ (θ : ℝ → ℝ), (∀ t : ℝ, 1 ≤ t → θ t = 0) → ∀ (κ : ℝ), 0 < κ → κ < 1/16 →
    ∀ (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ), ContDiffOn ℝ ∞ a {x : E | x ≠ 0} →
    (∀ x, a (-x) = -a x) → (∀ t : ℝ, 0 < t → ∀ x, a (t • x) = t*a x) →
    ∀ (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen), (∀ t : ℝ, 0 < t → ∀ x, S (t • x) = S x) →
    ∀ (k I J : TensorSlot) (M : ℝ), 0 ≤ M → GaugeProfileBound N M (gaugeTriadAngularProfile θ κ m w a C S k I J) →
    ∀ (d : Fin 4 → Fin 4 → SchwartzMap E ℝ), (∀ i j, d i j = d j i) →
    ∀ D : ℝ, 0 ≤ D → (∀ i j x, |d i j x| ≤ D) → ∀ L : ℝ≥0, (∀ i j x, ‖fderiv ℝ (d i j : E → ℝ) x‖ ≤ (L:ℝ)) →
    ∀ z : ProjectionSchwartzMatrix,
    let H := Burnett.C03.projectedGaugeComplement z k.1 k.2
    let b := gaugeRawEntry θ gaugeCorrectionInfrared gaugeCorrectionInfrared κ m w a C S k I J
    ∃ (T Tstar : SchwartzMap E ℂ → FirstOrderLp 2) (A B : Fin 4 → SchwartzMap E ℂ → FirstOrderLp 2),
      (∀ u v : SchwartzMap E ℂ, inner ℂ (v.toLp 2 volume) (T u) = radianHighPair b H u v ∧
        inner ℂ (v.toLp 2 volume) (T u) = inner ℂ (Tstar v) (u.toLp 2 volume)) ∧
      (∀ (r : Fin 4) (u v : SchwartzMap E ℂ), inner ℂ (v.toLp 2 volume) (A r u) = radianHighPair b (coordinateDerivative r H) u v ∧
        inner ℂ (u.toLp 2 volume) (B r v) = conj (radianHighPair b (coordinateDerivative r H) u v)) ∧
      ∀ u v : SchwartzMap E ℂ,
      let left (r s : Fin 4) := inner ℂ ((realSchwartzMultiply (d r s) (coordinateDerivative r v)).toLp 2 volume) (A s u)
      let middle (r s : Fin 4) := inner ℂ ((coordinateDerivative r v).toLp 2 volume) (coefficientCommutatorOutput (d r s) T (coordinateDerivative s u))
      let right (r s : Fin 4) := inner ℂ (B r v) ((realSchwartzMultiply (d r s) (coordinateDerivative s u)).toLp 2 volume)
      weakDivergenceCommutatorPair d T u v = ∑ r, ∑ s, (left r s + middle r s - right r s) ∧ ∀ r s,
      ‖left r s‖ ≤ (D * schwartzGradientNorm 2 v) * (K*M*schwartzGradientNorm 4 H*schwartzGradientNorm 4 u) ∧
      ‖middle r s‖ ≤ schwartzGradientNorm 2 v * (K*M*(L:ℝ)*‖H.toLp 4 volume‖*schwartzGradientNorm 4 u) ∧
      ‖right r s‖ ≤ (K*M*schwartzGradientNorm 4 H*schwartzGradientNorm 4 v) * (D*schwartzGradientNorm 2 u) := by
  obtain ⟨N,K,hK,all⟩ := exists_originalAngular_threeDivergenceTerms gaugeCorrectionInfrared gaugeRatioGuard
    (r:=1/2) (ρ:=1/4) (R₀:=1) (by norm_num) (by norm_num) (by norm_num) le_rfl gaugeCorrectionInfrared_smooth
    gaugeCorrectionInfrared_zero gaugeCorrectionInfrared_one gaugeRatioGuard_smooth (fun _ h => gaugeRatioGuard_vanishes h)
  refine ⟨N,K,hK,?_⟩
  intro θ hcut κ hκ hsmall m w a ha hOdd hHom C S hS k I J M hM jets d symm D hD dBound L slope z H b
  obtain ⟨W,hW,sub,smooth,jet⟩ := jets
  obtain ⟨T,Tstar,A,B,pair,der,terms⟩ := all hW sub smooth M hM (fun n hn p hp x => jet n hn (p,(x:E)) ⟨hp,x.property⟩)
    d symm D hD dBound L slope H
  have inert := actualGaugeA08_pair θ hcut κ hκ hsmall m w a ha hOdd hHom C S hS k I J
  refine ⟨T,Tstar,A,B, fun u v => ⟨(pair u v).1.trans (inert H (gaugeLow_spectrum_zero z k) u v).symm,(pair u v).2⟩,?_,terms⟩
  intro r u v
  have low (p : E) (hp : ‖p‖ ≤ 1) : radianFourier (coordinateDerivative r H) p = 0 := by
    rw [radianFourier_coordinateDerivative, show radianFourier H p = 0 from gaugeLow_spectrum_zero z k p hp, mul_zero]
  have re := inert (coordinateDerivative r H) low u v
  refine ⟨(der r u v).1.trans re.symm,?_⟩
  rw [(der r v u).2,radianHighPair_highAdjoint,re]

end Burnett.V11
