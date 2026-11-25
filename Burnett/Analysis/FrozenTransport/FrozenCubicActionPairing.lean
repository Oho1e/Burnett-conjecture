import Burnett.Analysis.FrozenTransport.CompactReceivingCubicCoefficients
import Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedLowerOrderCompleteCubic
import Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedInfraredStructure

set_option autoImplicit false
set_option maxRecDepth 6200
set_option maxHeartbeats 13000000
noncomputable section

namespace Burnett.C02

open MeasureTheory Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped BigOperators ComplexConjugate ContDiff ENNReal

open private realHermitianTest realHermitianTest_apply linearCoefficientTerm quadraticCoefficientTerm from
  Burnett.Analysis.FrozenTransport.CubicCoefficientFunctional
open private fixed_homogeneous_spectrum_integrable from Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedInfraredStructure

local notation "Lin" => CubicLinearIndex OrderedPair
local notation "Quad" => CubicQuadraticIndex OrderedPair

private def undifferentiatedTestSlot : Lin ≃ Quad where
  toFun a := (a.2, ((a.1.1.1,a.1.2.1),(a.1.1.2,a.1.2.2)))
  invFun a := (((a.2.1.1,a.2.2.1),(a.2.1.2,a.2.2.2)),a.1)
  left_inv _ := rfl
  right_inv _ := rfl

private def derivativeOnCoefficientSlot : Lin ≃ Quad where
  toFun a := (a.1.2.1, ((a.1.1.1,a.2),(a.1.1.2,a.1.2.2)))
  invFun a := (((a.2.1.1,a.2.2.1),(a.1,a.2.2.2)),a.2.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

private def cubicDirectTest (b : E → ℝ) (u : RealEnergyField OrderedPair) (k : Lin) : ℂ :=
  ∫ x, energyPartial k.1.1.1 (u.1 k.1.2.1) x * energyPartial k.1.1.2 (u.1 k.1.2.2) x *
    conj (radianAction b (u.1 k.2) x)

private def cubicDerivativeTest (b : E → ℝ) (u : RealEnergyField OrderedPair) (k : Lin) : ℂ :=
  ∫ x, u.1 k.2 x * energyPartial k.1.1.2 (u.1 k.1.2.2) x *
    conj (radianAction b (energyPartial k.1.1.1 (u.1 k.1.2.1)) x)

/-- Literal cyclic principal action with the imaginary part of the actual
test in the real slot. Exchange symmetry identifies the two differentiated
placements, giving their multiplicity two. -/
def frozenActionCyclicRadianEnergy (G : Mat) (b : E → ℝ) (u : RealEnergyField OrderedPair) : ℝ :=
  ∑ k : Lin, frozenActionCubicLinear G k.1 k.2 *
    (-(cubicDirectTest b u k).im - 2 * (cubicDerivativeTest b u k).im)

private theorem cubicRadianIntegrationByParts (b : E → ℝ) (u : RealEnergyField OrderedPair)
    (hSpectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum b g))
    (hLp : ∀ g : SchwartzMap E ℂ, MemLp (radianAction b g) (ENNReal.ofReal 3) volume) (k : Lin) :
    -(cubicDirectTest b u k).im - 2 * (cubicDerivativeTest b u k).im =
      linearCoefficientTerm b u hLp k +
        quadraticCoefficientTerm b u hLp (derivativeOnCoefficientSlot k) -
        (1 / 2 : ℝ) * quadraticCoefficientTerm b u hLp (undifferentiatedTestSlot k) := by
  let a := k.1.1.1
  let d := k.1.1.2
  let i := k.1.2.1
  let j := k.1.2.2
  let l := k.2
  let f := energyProduct (u.1 l) (energyPartial d (u.1 j))
  let f₁ := energyProduct (energyPartial a (u.1 l)) (energyPartial d (u.1 j))
  let f₂ := energyProduct (u.1 l) (energyPartial a (energyPartial d (u.1 j)))
  let g := u.1 i
  have hF (x : E) : energyPartial a f x = f₁ x + f₂ x :=
    energyPartial_product a (u.1 l) (energyPartial d (u.1 j)) x
  have hDer := radian_partial_pairing_of_integrable_spectrum b hSpectrum a f g
  have hInt : (∫ x, energyPartial a f x * conj (radianAction b g x)) =
      (∫ x, f₁ x * conj (radianAction b g x)) + ∫ x, f₂ x * conj (radianAction b g x) := by
    simp only [hF, add_mul]
    exact integral_add (radian_test_integrable_of_L3 b f₁ g (hLp g))
      (radian_test_integrable_of_L3 b f₂ g (hLp g))
  rw [hInt] at hDer
  have hSigns := congrArg Complex.im hDer
  simp only [Complex.add_im, Complex.neg_im] at hSigns
  have hL : linearCoefficientTerm b u hLp k =
      2 * (∫ x, f₂ x * conj (radianAction b g x)).im := rfl
  have hQ : quadraticCoefficientTerm b u hLp (derivativeOnCoefficientSlot k) =
      2 * (∫ x, f₁ x * conj (radianAction b g x)).im := rfl
  have hUndiff : quadraticCoefficientTerm b u hLp (undifferentiatedTestSlot k) =
      2 * (cubicDirectTest b u k).im := rfl
  have hDiff : cubicDerivativeTest b u k =
      ∫ x, f x * conj (radianAction b (energyPartial a g) x) := rfl
  rw [hL, hQ, hUndiff, hDiff]
  linarith only [hSigns]

/-- The complete A02 expression evaluates the same actual cyclic action.
This identity fixes the coefficient of each first- and second-derivative
monomial after moving the two differentiated test placements. -/
theorem frozenActionCyclicRadianEnergy_eq_complete (G : Mat) (b : E → ℝ) (u : RealEnergyField OrderedPair)
    (hSpectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum b g))
    (hLp : ∀ g : SchwartzMap E ℂ, MemLp (radianAction b g) (ENNReal.ofReal 3) volume) :
    frozenActionCyclicRadianEnergy G b u =
      completeCubicEnergy (frozenActionCubicLinear G) (frozenActionCubicQuadratic G) b u := by
  let C (k : Lin) := frozenActionCubicLinear G k.1 k.2
  let P := linearCoefficientTerm b u hLp
  let Q := quadraticCoefficientTerm b u hLp
  have hMoved : (∑ k : Lin, C k * Q (derivativeOnCoefficientSlot k)) =
      ∑ a : Quad, frozenActionCubicLinear G ((a.2.1.1,a.2.2.1),(a.1,a.2.2.2)) a.2.1.2 * Q a :=
    Fintype.sum_equiv derivativeOnCoefficientSlot _ _ fun _ => rfl
  have hDirect : (∑ k : Lin, C k * ((1 / 2 : ℝ) * Q (undifferentiatedTestSlot k))) =
      ∑ a : Quad, ((1 / 2 : ℝ) *
        frozenActionCubicLinear G ((a.2.1.1,a.2.2.1),(a.2.1.2,a.2.2.2)) a.1) * Q a :=
    Fintype.sum_equiv undifferentiatedTestSlot _ _ fun a => by
      change C a * ((1 / 2 : ℝ) * Q (undifferentiatedTestSlot a)) =
        ((1 / 2 : ℝ) * C a) * Q (undifferentiatedTestSlot a)
      ring
  rw [completeCubicEnergy_eq_coefficientFunctional _ _ _ _ hLp]
  change (∑ k : Lin, C k * (-(cubicDirectTest b u k).im - 2 * (cubicDerivativeTest b u k).im)) =
    (∑ k : Lin, C k * P k) +
      ∑ a : Quad, frozenActionCubicQuadratic G a.2.1.1 a.2.2.1 a.2.1.2 a.2.2.2 a.1 * Q a
  simp_rw [cubicRadianIntegrationByParts b u hSpectrum hLp]
  change (∑ k : Lin, C k * (P k + Q (derivativeOnCoefficientSlot k) -
      (1 / 2 : ℝ) * Q (undifferentiatedTestSlot k))) = _
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, hMoved, hDirect,
    frozenActionCubicQuadratic, sub_mul]
  ring

private theorem fixedInfraredSymbol_spectrum_integrable (cut add : SchwartzMap E ℂ)
    (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ) (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (f : SchwartzMap E ℂ) :
    Integrable (radianActionSpectrum (fixedInfraredSymbol cut add b) f) := by
  have hB := fixed_homogeneous_spectrum_integrable b hb hom f
  have hC := fixed_cut_spectrum_integrable cut hcut b hb hom f
  have hR := fixed_profile_spectrum_integrable add hadd f
  have hEq : radianActionSpectrum (fixedInfraredSymbol cut add b) f =
      radianActionSpectrum b f - radianActionSpectrum (fun ζ => fixedRadianProfile cut ζ * b ζ) f +
        radianActionSpectrum (fixedRadianProfile add) f := by
    funext ξ
    simp only [Pi.add_apply, Pi.sub_apply, fixedInfraredSymbol, radianActionSpectrum, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [hEq]
  exact (hB.sub hC).add hR

theorem frozenActionCyclicRadianEnergy_fixedInfrared_eq_complete
    (G : Mat) (cut add : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ) (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (D : ℝ) (hD : 0 ≤ D)
    (jets : ∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ Metric.sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D)
    (u : RealEnergyField OrderedPair) :
    frozenActionCyclicRadianEnergy G (fixedInfraredSymbol cut add b) u =
      completeCubicEnergy (frozenActionCubicLinear G) (frozenActionCubicQuadratic G)
        (fixedInfraredSymbol cut add b) u := by
  obtain ⟨_, _, _, _, _, _, hLp⟩ := fixedInfraredSymbol_W1p_bound cut add hcut hadd 3 (by norm_num)
  exact frozenActionCyclicRadianEnergy_eq_complete G _ u
    (fixedInfraredSymbol_spectrum_integrable cut add hcut hadd b hb hom)
    (fun g => (hLp b hb hom D hD jets g).1)

end Burnett.C02
