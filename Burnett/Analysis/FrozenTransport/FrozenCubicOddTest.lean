import Burnett.Analysis.FrozenTransport.FrozenCubicActionPairing
import Burnett.Analysis.FrozenTransport.FourierSchwartzTransportInputs

set_option autoImplicit false
set_option maxRecDepth 5700
set_option maxHeartbeats 10500000
noncomputable section

namespace Burnett.C02

open Filter MeasureTheory Burnett.A02.FrequencySplit Burnett.Fourier
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped BigOperators ComplexConjugate ContDiff FourierTransform

open private realFourier_reflection from Burnett.Analysis.FrozenTransport.FourierSchwartzTransportInputs
open private cubicDirectTest cubicDerivativeTest from Burnett.Analysis.FrozenTransport.FrozenCubicActionPairing

theorem radianAction_conj_neg_of_real_and_odd (b : E → ℝ) (hb : ∀ ξ, b (-ξ) = -b ξ)
    (f : SchwartzMap E ℂ) (hf : ∀ x, conj (f x) = f x) (x : E) :
    conj (radianAction b f x) = -radianAction b f x := by
  let F := radianActionSpectrum b f
  have hF : (fun ξ => conj (F ξ)) = (fun ξ => -(F (-ξ))) := by
    funext ξ
    change conj ((b (tau • ξ) : ℂ) * 𝓕 (f : E → ℂ) ξ) =
      -((b (tau • (-ξ)) : ℂ) * 𝓕 (f : E → ℂ) (-ξ))
    rw [map_mul, Complex.conj_ofReal, realFourier_reflection f hf, smul_neg, hb, Complex.ofReal_neg,
      neg_mul, neg_neg]
  rw [← radianActionSpectrum_inverse, ← fourier_conj_eq_conj_inverse, hF,
    Real.fourierIntegralInv_eq_fourierIntegral_comp_neg, Real.fourierIntegral_eq', Real.fourierIntegral_eq']
  simp only [smul_neg, integral_neg, F]

private theorem odd_radianTest_Re (b : E → ℝ) (hb : ∀ ξ, b (-ξ) = -b ξ)
    (f : SchwartzMap E ℂ) (hf : ∀ x, conj (f x) = f x) (w : E → ℂ) :
    (∫ x, w x * (-Complex.I * radianAction b f x)).re =
      -(∫ x, w x * conj (radianAction b f x)).im := by
  have h : (∫ x, w x * (-Complex.I * radianAction b f x)) =
      Complex.I * (∫ x, w x * conj (radianAction b f x)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change w x * (-Complex.I * radianAction b f x) = Complex.I * (w x * conj (radianAction b f x))
    rw [radianAction_conj_neg_of_real_and_odd b hb f hf]
    ring
  rw [h]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]

local notation "Lin" => CubicLinearIndex OrderedPair

private def swapDifferentiatedFields : Lin ≃ Lin where
  toFun k := (((k.1.1.2,k.1.1.1),(k.1.2.2,k.1.2.1)),k.2)
  invFun k := (((k.1.1.2,k.1.1.1),(k.1.2.2,k.1.2.1)),k.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The three original test placements of the cyclic action on the same
real field, with the actual test action (-i b(D)) and its first
coordinate derivatives interpreted weakly. -/
def frozenActionCyclicOddTestEnergy (G : Mat) (b : E → ℝ) (u : RealEnergyField OrderedPair) : ℝ :=
  ∑ k : Lin, frozenActionCubicLinear G k.1 k.2 *
    ((∫ x, (energyPartial k.1.1.1 (u.1 k.1.2.1) x * energyPartial k.1.1.2 (u.1 k.1.2.2) x) *
      (-Complex.I * radianAction b (u.1 k.2) x)).re +
     (∫ x, (u.1 k.2 x * energyPartial k.1.1.2 (u.1 k.1.2.2) x) *
      (-Complex.I * radianAction b (energyPartial k.1.1.1 (u.1 k.1.2.1)) x)).re +
     (∫ x, (u.1 k.2 x * energyPartial k.1.1.1 (u.1 k.1.2.1) x) *
      (-Complex.I * radianAction b (energyPartial k.1.1.2 (u.1 k.1.2.2)) x)).re)

private theorem energyPartial_real (f : SchwartzMap E ℂ) (hf : ∀ x, conj (f x) = f x)
    (a : Burnett.RicciSymbol.Index) (x : E) : conj (energyPartial a f x) = energyPartial a f x := by
  have h : (fun y => conj (f y)) = (f : E → ℂ) := funext hf
  have hD := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x (f.differentiable x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => conj (f y)) x =
    Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ (f : E → ℂ) x) at hD
  rw [h] at hD
  exact (congrArg (fun L : E →L[ℝ] ℂ => L (EuclideanSpace.single a 1)) hD).symm

theorem frozenActionCyclicOddTestEnergy_eq_radian (G : Mat) (b : E → ℝ)
    (hb : ∀ ξ, b (-ξ) = -b ξ) (u : RealEnergyField OrderedPair) :
    frozenActionCyclicOddTestEnergy G b u = frozenActionCyclicRadianEnergy G b u := by
  let C (k : Lin) := frozenActionCubicLinear G k.1 k.2
  let τ := swapDifferentiatedFields
  let L (k : Lin) := (cubicDirectTest b u k).im
  let R (k : Lin) := (cubicDerivativeTest b u k).im
  have hFold : (∑ k : Lin, C k * R (τ k)) = ∑ k : Lin, C k * R k :=
    Fintype.sum_equiv τ _ _ (fun k => by
      have heq : C k = C (τ k) := frozenActionCubicLinear_symmetry G _ _ _ _ _
      rw [heq])
  have hTwo : (∑ k : Lin, C k * (2 * R k)) = 2 * ∑ k : Lin, C k * R k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  calc
    _ = ∑ k : Lin, C k * (-L k - R k - R (τ k)) := by
      unfold frozenActionCyclicOddTestEnergy
      apply Finset.sum_congr rfl
      intro k _
      rw [odd_radianTest_Re b hb _ (u.property k.2),
        odd_radianTest_Re b hb _ (energyPartial_real _ (u.property k.1.2.1) k.1.1.1),
        odd_radianTest_Re b hb _ (energyPartial_real _ (u.property k.1.2.2) k.1.1.2)]
      change C k * (-L k + -R k + -R (τ k)) = C k * (-L k - R k - R (τ k))
      ring
    _ = (∑ k : Lin, C k * (-L k)) - (∑ k : Lin, C k * R k) - ∑ k : Lin, C k * R k := by
      simp only [mul_sub, Finset.sum_sub_distrib, hFold]
    _ = _ := by
      change _ = ∑ k : Lin, C k * (-L k - 2 * R k)
      rw [show (∑ k : Lin, C k * (-L k - 2 * R k)) =
        (∑ k : Lin, C k * (-L k)) - ∑ k : Lin, C k * (2 * R k) by
          simp only [mul_sub, Finset.sum_sub_distrib], hTwo]
      ring

theorem frozenActionCyclicOddTestEnergy_fixedInfrared_eq_complete
    (G : Mat) (cut add : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ) (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (D : ℝ) (hD : 0 ≤ D)
    (jets : ∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ Metric.sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D)
    (hOdd : ∀ ξ, fixedInfraredSymbol cut add b (-ξ) = -fixedInfraredSymbol cut add b ξ)
    (u : RealEnergyField OrderedPair) :
    frozenActionCyclicOddTestEnergy G (fixedInfraredSymbol cut add b) u =
      completeCubicEnergy (frozenActionCubicLinear G) (frozenActionCubicQuadratic G)
        (fixedInfraredSymbol cut add b) u :=
  (frozenActionCyclicOddTestEnergy_eq_radian G _ hOdd u).trans
    (frozenActionCyclicRadianEnergy_fixedInfrared_eq_complete G cut add hcut hadd b hb hom D hD jets u)

end Burnett.C02
