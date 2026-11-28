import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualThreeGauge
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualThinPhysical
import Burnett.Analysis.AllScaleTransfer.RadianTrilinearSymmetry

set_option autoImplicit false
set_option maxRecDepth 7200
set_option maxHeartbeats 15500000

noncomputable section

namespace Burnett.C02

open MeasureTheory Burnett.RicciSymbol Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.V08 (originalGaugeSpectrum signedCyclicPhase)

private abbrev WardSpectrum := E → ComplexTensor2

/-- The genuine symmetric cyclic energy integrand, with the exact factor
from the three original test placements. -/
def wardCyclicCubicWeight (G : Mat) (a : E → ℝ) (F H J : WardSpectrum) (x : Joint) : ℂ :=
  let p := x.1
  let q := x.2
  let r := -(p+q)
  (-Complex.I / 3) * (signedCyclicPhase a p q : ℂ) *
    complexPrincipalVertex G (fun d => p d) (F p) (fun d => q d) (H q) (fun d => r d) (J r)

def wardCyclicCubicForm (G : Mat) (a : E → ℝ) (F H J : WardSpectrum) : ℂ :=
  (tau^8)⁻¹ • (∫ x, wardCyclicCubicWeight G a F H J x)

theorem wardCyclicCubicWeight_cycle (G : Mat) (a : E → ℝ) (F H J : WardSpectrum) (x : Joint) :
    wardCyclicCubicWeight G a F H J (radianCycle x) = wardCyclicCubicWeight G a J F H x := by
  let p := x.1
  let q := x.2
  let r := -(p+q)
  have hp : -(q+r) = p := by dsimp [r]; abel
  have hα : signedCyclicPhase a q r = signedCyclicPhase a p q := by
    unfold signedCyclicPhase
    rw [hp]
    change a q + a r + a p = a p + a q + a r
    ring
  change (-Complex.I / 3) * (signedCyclicPhase a q r : ℂ) *
    complexPrincipalVertex G (fun d => q d) (F q) (fun d => r d) (H r) (fun d => (-(q+r)) d) (J (-(q+r))) =
    (-Complex.I / 3) * (signedCyclicPhase a p q : ℂ) *
    complexPrincipalVertex G (fun d => p d) (J p) (fun d => q d) (F q) (fun d => r d) (H r)
  rw [hp,hα, ← complexPrincipalVertex_cyclic G (fun d => p d) (J p)]

theorem wardCyclicCubicForm_cycle (G : Mat) (a : E → ℝ) (F H J : WardSpectrum) :
    wardCyclicCubicForm G a J F H = wardCyclicCubicForm G a F H J := by
  have h : wardCyclicCubicWeight G a J F H = wardCyclicCubicWeight G a F H J ∘ radianCycle :=
    funext fun x => (wardCyclicCubicWeight_cycle G a F H J x).symm
  rw [wardCyclicCubicForm, wardCyclicCubicForm, h]
  change (tau^8)⁻¹ • (∫ x, wardCyclicCubicWeight G a F H J (radianCycle x)) = _
  rw [measurePreserving_radianCycle.integral_comp' (wardCyclicCubicWeight G a F H J)]

private theorem wardCyclicCubicWeight_cycle_integrable (G : Mat) (a : E → ℝ) (F H J : WardSpectrum)
    (h : Integrable (wardCyclicCubicWeight G a F H J)) :
    Integrable (wardCyclicCubicWeight G a J F H) := by
  have hx : wardCyclicCubicWeight G a J F H = wardCyclicCubicWeight G a F H J ∘ radianCycle :=
    funext fun x => (wardCyclicCubicWeight_cycle G a F H J x).symm
  rw [hx]
  exact measurePreserving_radianCycle.integrable_comp_of_integrable h

private theorem wardCyclicCubicWeight_sum_slots (G : Mat) (hG : Matrix.det G ≠ 0) (a : E → ℝ)
    (P Q : WardSpectrum) (x : Joint) :
    wardCyclicCubicWeight G a (P+Q) (P+Q) (P+Q) x =
      wardCyclicCubicWeight G a P P P x +
      wardCyclicCubicWeight G a Q P P x + wardCyclicCubicWeight G a P Q P x + wardCyclicCubicWeight G a P P Q x +
      wardCyclicCubicWeight G a P Q Q x + wardCyclicCubicWeight G a Q P Q x + wardCyclicCubicWeight G a Q Q P x +
      wardCyclicCubicWeight G a Q Q Q x := by
  simp only [wardCyclicCubicWeight, Pi.add_apply, complexPrincipalVertex_add_first_amplitude G hG,
    complexPrincipalVertex_add_second_amplitude G hG, complexPrincipalVertex_add_third_amplitude G hG]
  ring

/-- Integrating the action vertex gives the actual coefficients 1, 3, 3, 1.
The multiplicities follow from the measure-preserving triad cycle. -/
theorem wardCyclicCubicForm_expand (G : Mat) (hG : Matrix.det G ≠ 0) (a : E → ℝ) (P Q : WardSpectrum)
    (h₀ : Integrable (wardCyclicCubicWeight G a P P P))
    (h₁ : Integrable (wardCyclicCubicWeight G a Q P P))
    (h₂ : Integrable (wardCyclicCubicWeight G a P Q Q))
    (h₃ : Integrable (wardCyclicCubicWeight G a Q Q Q)) :
    wardCyclicCubicForm G a (P+Q) (P+Q) (P+Q) =
      wardCyclicCubicForm G a P P P + 3 * wardCyclicCubicForm G a Q P P +
      3 * wardCyclicCubicForm G a P Q Q + wardCyclicCubicForm G a Q Q Q := by
  let W := wardCyclicCubicWeight G a
  let I := wardCyclicCubicForm G a
  have h₁₁ : Integrable (W P Q P) := wardCyclicCubicWeight_cycle_integrable G a Q P P h₁
  have h₁₂ : Integrable (W P P Q) := wardCyclicCubicWeight_cycle_integrable G a P Q P h₁₁
  have h₂₁ : Integrable (W Q P Q) := wardCyclicCubicWeight_cycle_integrable G a P Q Q h₂
  have h₂₂ : Integrable (W Q Q P) := wardCyclicCubicWeight_cycle_integrable G a Q P Q h₂₁
  let U : Fin 8 → Joint → ℂ := ![W P P P, W Q P P, W P Q P, W P P Q, W P Q Q, W Q P Q, W Q Q P, W Q Q Q]
  have hInt (j : Fin 8) : Integrable (U j) := by
    fin_cases j
    · exact h₀
    · exact h₁
    · exact h₁₁
    · exact h₁₂
    · exact h₂
    · exact h₂₁
    · exact h₂₂
    · exact h₃
  have hU : W (P+Q) (P+Q) (P+Q) = fun x => ∑ j, U j x := by
    funext x
    change wardCyclicCubicWeight G a (P+Q) (P+Q) (P+Q) x = _
    rw [wardCyclicCubicWeight_sum_slots G hG]
    simp only [U, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
    ring
  have hi : I (P+Q) (P+Q) (P+Q) = ∑ j, (tau^8)⁻¹ • ∫ x, U j x := by
    change (tau^8)⁻¹ • (∫ x, W (P+Q) (P+Q) (P+Q) x) = _
    rw [hU, integral_finset_sum Finset.univ (fun j _ => hInt j), Finset.smul_sum]
  change I (P+Q) (P+Q) (P+Q) = I P P P + 3 * I Q P P + 3 * I P Q Q + I Q Q Q
  rw [hi]
  simp only [U, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  change I P P P + (I Q P P + (I P Q P + (I P P Q + (I P Q Q + (I Q P Q + (I Q Q P + I Q Q Q)))))) = _
  have h₁a : I P Q P = I Q P P := wardCyclicCubicForm_cycle G a Q P P
  have h₁b : I P P Q = I Q P P := (wardCyclicCubicForm_cycle G a P Q P).trans h₁a
  have h₂a : I Q P Q = I P Q Q := wardCyclicCubicForm_cycle G a P Q Q
  have h₂b : I Q Q P = I P Q Q := (wardCyclicCubicForm_cycle G a Q P Q).trans h₂a
  rw [h₁a, h₁b, h₂a, h₂b]
  ring

end Burnett.C02
