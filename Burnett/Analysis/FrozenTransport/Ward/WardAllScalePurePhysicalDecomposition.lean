import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleCyclicCubicExpansion

set_option autoImplicit false
set_option maxRecDepth 7200
set_option maxHeartbeats 6200000

noncomputable section

namespace Burnett.C02

open MeasureTheory Burnett.A02.FrequencySplit Burnett.A05 Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight comparableSlotWeight angularNearWeight)

def wardPurePhysicalNearWeight (ϑ : ℝ → ℝ) (κ δ : ℝ) (x : Joint) : ℝ :=
  let p := x.1
  let q := x.2
  let r := -(p+q)
  comparableSlotWeight ϑ κ p q r +
    lowSlotWeight ϑ κ p q r * angularNearWeight ϑ δ p q r +
    lowSlotWeight ϑ κ q r p * angularNearWeight ϑ δ q r p +
    lowSlotWeight ϑ κ r p q * angularNearWeight ϑ δ r p q

def wardPurePhysicalFirstFarWeight (ϑ : ℝ → ℝ) (κ δ : ℝ) (x : Joint) : ℝ :=
  let p := x.1
  let q := x.2
  let r := -(p+q)
  lowSlotWeight ϑ κ p q r * (1-angularNearWeight ϑ δ p q r)

/-- With the original four-sector partition, the pure physical numerator
is the precise near numerator plus the three signed rotations of the
original separated low piece. -/
theorem wardPurePhysicalCyclicWeight_split (G : Mat) (a : E → ℝ)
    (H : E → ComplexTensor2) (ϑ : ℝ → ℝ) (κ δ : ℝ) (x : Joint) :
    let W := wardCyclicCubicWeight G a H H H
    let F (y : Joint) := (wardPurePhysicalFirstFarWeight ϑ κ δ y : ℂ) * W y
    W x = (wardPurePhysicalNearWeight ϑ κ δ x : ℂ) * W x +
      F x + F (radianCycle x) + F (radianCycle (radianCycle x)) := by
  intro W F
  have hCycle (y : Joint) : W (radianCycle y) = W y := wardCyclicCubicWeight_cycle G a H H H y
  have h₁ : W (radianCycle x) = W x := hCycle x
  have h₂ : W (radianCycle (radianCycle x)) = W x := (hCycle _).trans h₁
  let p := x.1
  let q := x.2
  let r := -(p+q)
  let L (s t u : E) := lowSlotWeight ϑ κ s t u
  let N (s t u : E) := angularNearWeight ϑ δ s t u
  have hp : -(q+r) = p := by dsimp only [r]; abel
  have hq : -(r+p) = q := by dsimp only [r]; abel
  change W x = ((comparableSlotWeight ϑ κ p q r + L p q r * N p q r +
      L q r p * N q r p + L r p q * N r p q : ℝ) : ℂ) * W x +
    ((L p q r * (1-N p q r) : ℝ) : ℂ) * W x +
    ((L q r (-(q+r)) * (1-N q r (-(q+r))) : ℝ) : ℂ) * W (radianCycle x) +
    ((L r (-(q+r)) (-(r + -(q+r))) * (1-N r (-(q+r)) (-(r + -(q+r)))) : ℝ) : ℂ) *
      W (radianCycle (radianCycle x))
  rw [h₁,h₂,hp,hq]
  unfold comparableSlotWeight
  push_cast
  ring

/-- The separated physical-low Fourier integral appears three times
after the measure-preserving signed cyclic relabeling. -/
theorem wardPurePhysicalCubicForm_eq_near_add_far (G : Mat) (a : E → ℝ)
    (H : E → ComplexTensor2) (ϑ : ℝ → ℝ) (κ δ : ℝ) :
    let W := wardCyclicCubicWeight G a H H H
    let F (y : Joint) := (wardPurePhysicalFirstFarWeight ϑ κ δ y : ℂ) * W y
    let N (y : Joint) := (wardPurePhysicalNearWeight ϑ κ δ y : ℂ) * W y
    Integrable W → Integrable F →
    Integrable N ∧
      wardCyclicCubicForm G a H H H =
        ((tau^8)⁻¹ : ℝ) • (∫ x, N x) + 3 * (((tau^8)⁻¹ : ℝ) • (∫ x, F x)) := by
  intro W F N hW hF
  have hF₁ : Integrable (fun x => F (radianCycle x)) :=
    measurePreserving_radianCycle.integrable_comp_of_integrable hF
  have hF₂ : Integrable (fun x => F (radianCycle (radianCycle x))) :=
    measurePreserving_radianCycle.integrable_comp_of_integrable hF₁
  have hEq (x : Joint) : W x = N x + F x + F (radianCycle x) + F (radianCycle (radianCycle x)) :=
    wardPurePhysicalCyclicWeight_split G a H ϑ κ δ x
  have hEqN : N = fun x => W x - F x - F (radianCycle x) - F (radianCycle (radianCycle x)) := by
    funext x
    linear_combination -(hEq x)
  have hN : Integrable N := hEqN.symm ▸ ((hW.sub hF).sub hF₁).sub hF₂
  refine ⟨hN, ?_⟩
  have hC₁ : (∫ x, F (radianCycle x)) = ∫ x, F x := measurePreserving_radianCycle.integral_comp' F
  have hC₂ : (∫ x, F (radianCycle (radianCycle x))) = ∫ x, F x :=
    (measurePreserving_radianCycle.integral_comp' (fun y => F (radianCycle y))).trans hC₁
  change (((tau^8)⁻¹ : ℝ) • (∫ x, W x)) = _
  rw [show W = (fun x => N x + F x + F (radianCycle x) + F (radianCycle (radianCycle x))) from funext hEq]
  have h0 : (∫ x, N x + F x) = (∫ x, N x) + (∫ x, F x) := integral_add hN hF
  have h1 : (∫ x, N x + F x + F (radianCycle x)) = (∫ x, N x + F x) + (∫ x, F (radianCycle x)) :=
    integral_add (hN.add hF) hF₁
  have h2 : (∫ x, N x + F x + F (radianCycle x) + F (radianCycle (radianCycle x))) =
      (∫ x, N x + F x + F (radianCycle x)) + (∫ x, F (radianCycle (radianCycle x))) :=
    integral_add ((hN.add hF).add hF₁) hF₂
  rw [h2,h1,h0,hC₂,hC₁]
  simp only [Complex.real_smul]
  ring

end Burnett.C02
