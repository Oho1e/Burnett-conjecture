import Burnett.Analysis.CubicEnergy.CompleteEnergy.InfraredCubicContinuity

set_option autoImplicit false
set_option maxRecDepth 5300
set_option maxHeartbeats 7400000
noncomputable section

namespace Burnett.A02.FrequencySplit

open Filter MeasureTheory Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ENNReal

open private derivativeSchwartzArray derivativeSchwartzArray_apply from
  Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedLowerOrderCompleteCubic

abbrev CubicLinearIndex (J : Type) := EnergyIndex J × J
abbrev CubicQuadraticIndex (J : Type) := J × ((Index × J) × (Index × J))

def cubicLinearEntries {J : Type} (c : EnergyIndex J → J → ℝ) : CubicLinearIndex J → ℝ :=
  fun a => c a.1 a.2

def cubicQuadraticEntries {J : Type} (q : Index → Index → J → J → J → ℝ) :
    CubicQuadraticIndex J → ℝ :=
  fun a => q a.2.1.1 a.2.2.1 a.2.1.2 a.2.2.2 a.1

private def realHermitianTest (m : E → ℝ) (g : SchwartzMap E ℂ)
    (hg : MemLp (radianAction m g) (ENNReal.ofReal 3) volume) : SchwartzMap E ℂ →ₗ[ℝ] ℝ where
  toFun f := 2 * (∫ x, f x * conj (radianAction m g x)).im
  map_add' f h := by
    have hf := radian_test_integrable_of_L3 m f g hg
    have hh := radian_test_integrable_of_L3 m h g hg
    simp only [SchwartzMap.add_apply, add_mul]
    rw [show (∫ x, (f x * conj (radianAction m g x) + h x * conj (radianAction m g x))) =
      (∫ x, f x * conj (radianAction m g x)) + ∫ x, h x * conj (radianAction m g x) from integral_add hf hh,
      Complex.add_im, mul_add]
  map_smul' r f := by
    change 2 * (∫ x, ((r : ℂ) * f x) * conj (radianAction m g x)).im = r *
      (2 * (∫ x, f x * conj (radianAction m g x)).im)
    simp only [mul_assoc, integral_const_mul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, add_zero,
      zero_mul]
    ring

private theorem realHermitianTest_apply (m : E → ℝ) (g f : SchwartzMap E ℂ)
    (hg : MemLp (radianAction m g) (ENNReal.ofReal 3) volume) :
    realHermitianTest m g hg f = 2 * (∫ x, f x * conj (radianAction m g x)).im := rfl

private def productRightLinear (f : SchwartzMap E ℂ) : SchwartzMap E ℂ →ₗ[ℝ] SchwartzMap E ℂ :=
  (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) f.hasTemperateGrowth).toLinearMap.restrictScalars ℝ

private theorem productRightLinear_apply (f g : SchwartzMap E ℂ) :
    productRightLinear g f = energyProduct f g := rfl

private def linearCoefficientTerm {J : Type} [Fintype J] (m : E → ℝ) (u : RealEnergyField J)
    (hm : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) (ENNReal.ofReal 3) volume)
    (a : CubicLinearIndex J) : ℝ :=
  realHermitianTest m (u.1 a.1.2.1) (hm _) (energyProduct (u.1 a.2)
    (energyPartial a.1.1.1 (energyPartial a.1.1.2 (u.1 a.1.2.2))))

private def quadraticCoefficientTerm {J : Type} [Fintype J] (m : E → ℝ) (u : RealEnergyField J)
    (hm : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) (ENNReal.ofReal 3) volume)
    (a : CubicQuadraticIndex J) : ℝ :=
  realHermitianTest m (u.1 a.1) (hm _) (energyProduct
    (energyPartial a.2.1.1 (u.1 a.2.1.2)) (energyPartial a.2.2.1 (u.1 a.2.2.2)))

/-- The actual regularized energy is linear in the two finite coefficient
arrays when the field and Fourier multiplier are fixed. -/
def cubicCoefficientFunctional {J : Type} [Fintype J] (m : E → ℝ) (u : RealEnergyField J)
    (hm : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) (ENNReal.ofReal 3) volume) :
    ((CubicLinearIndex J → ℝ) × (CubicQuadraticIndex J → ℝ)) →ₗ[ℝ] ℝ where
  toFun w := (∑ a, w.1 a * linearCoefficientTerm m u hm a) +
    (∑ a, w.2 a * quadraticCoefficientTerm m u hm a)
  map_add' w z := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r w := by
    change (∑ a, (r * w.1 a) * linearCoefficientTerm m u hm a) +
      (∑ a, (r * w.2 a) * quadraticCoefficientTerm m u hm a) =
      r * ((∑ a, w.1 a * linearCoefficientTerm m u hm a) +
        (∑ a, w.2 a * quadraticCoefficientTerm m u hm a))
    simp only [mul_assoc, mul_add, Finset.mul_sum]

theorem completeCubicEnergy_eq_coefficientFunctional {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ) (q : Index → Index → J → J → J → ℝ)
    (m : E → ℝ) (u : RealEnergyField J)
    (hm : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) (ENNReal.ofReal 3) volume) :
    completeCubicEnergy c q m u =
      cubicCoefficientFunctional m u hm (cubicLinearEntries c, cubicQuadraticEntries q) := by
  let Q (k : EnergyIndex J) := energyPartial k.1.1 (energyPartial k.1.2 (u.1 k.2.2))
  have hLinear (k : EnergyIndex J) :
      2 * (∫ x, linearEnergyCoefficient c u k x * Q k x * conj (radianAction m (u.1 k.2.1) x)).im =
      ∑ j, c k j * linearCoefficientTerm m u hm (k, j) := by
    rw [show (fun x => linearEnergyCoefficient c u k x * Q k x * conj (radianAction m (u.1 k.2.1) x)) =
      (fun x => (energyProduct (linearEnergyCoefficient c u k) (Q k)) x *
        conj (radianAction m (u.1 k.2.1) x)) from rfl]
    rw [← realHermitianTest_apply m (u.1 k.2.1) _ (hm _), ← productRightLinear_apply]
    simp only [linearEnergyCoefficient, map_sum, map_smul, smul_eq_mul, productRightLinear_apply,
      linearCoefficientTerm, Q]
  have hQuadratic (k : J) :
      2 * (∫ x, semilinearDerivativeTerm q u u k x * conj (radianAction m (u.1 k) x)).im =
      ∑ a : (Index × J) × (Index × J),
        q a.1.1 a.2.1 a.1.2 a.2.2 k * quadraticCoefficientTerm m u hm (k, a) := by
    simp_rw [← derivativeSchwartzArray_apply q (u : J → SchwartzMap E ℂ) (u : J → SchwartzMap E ℂ) k]
    rw [← realHermitianTest_apply m (u.1 k) _ (hm _)]
    simp only [derivativeSchwartzArray, map_sum, map_smul, smul_eq_mul, quadraticCoefficientTerm]
  change completeCubicEnergy c q m u =
    (∑ a : CubicLinearIndex J, cubicLinearEntries c a * linearCoefficientTerm m u hm a) +
    (∑ a : CubicQuadraticIndex J, cubicQuadraticEntries q a * quadraticCoefficientTerm m u hm a)
  rw [completeCubicEnergy, Complex.add_im, mul_add, quasilinearPairing, semilinearHermitianPairing,
    Complex.im_sum, Complex.im_sum, Finset.mul_sum, Finset.mul_sum,
    Fintype.sum_prod_type (fun a : CubicLinearIndex J => cubicLinearEntries c a * linearCoefficientTerm m u hm a),
    Fintype.sum_prod_type (fun a : CubicQuadraticIndex J =>
      cubicQuadraticEntries q a * quadraticCoefficientTerm m u hm a)]
  simp only [cubicLinearEntries, cubicQuadraticEntries, ← hLinear, ← hQuadratic]
  rfl

end Burnett.A02.FrequencySplit
