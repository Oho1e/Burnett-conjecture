import Burnett.Analysis.TransportWard.Weyl.SymmetricFieldNormalization
import Burnett.Analysis.TransportWard.Weyl.LinearizedEulerPrincipal
import Burnett.Analysis.TransportWard.Weyl.FrozenKineticHessian

/-! The Fourier principal quadratic form of the same ΓΓ Euler derivative
in the paper's Euclidean orthonormal field coordinates. -/

set_option autoImplicit false
set_option maxHeartbeats 5700000
set_option maxRecDepth 4900

noncomputable section

namespace Burnett.V03.Palatini

open Burnett.RicciSymbol Burnett.V02 Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ComplexConjugate

open private metricKineticBilinear from Burnett.Analysis.FrozenTransport.V03MetricActionCoefficient
open private inverseMatrix_symmetric from Burnett.Analysis.TransportWard.Weyl.FrozenKineticHessian

local notation "I" => SymmetricMetricSlot

private theorem metricAxisJet_orthonormal (s : ActionSlot I) :
    metricAxisJet orthonormalMetricDirection s =
      (symmetricMetricScale s.2)⁻¹ • metricAxisJet symmetricMetricDirection s := by
  funext a
  by_cases ha : a = s.1
  · subst a
    simp [metricAxisJet, orthonormalMetricDirection]
  · simp [metricAxisJet, orthonormalMetricDirection, ha]

/-- Both tensor slots of the kinetic coefficient change by the inverse
basis scale, with the metric in the coefficients kept fixed. -/
theorem metricActionCoefficient_orthonormal (s t : ActionSlot I) (G : Mat) :
    metricActionCoefficient orthonormalMetricDirection s t G =
      (symmetricMetricScale s.2)⁻¹ * (symmetricMetricScale t.2)⁻¹ *
        metricActionCoefficient symmetricMetricDirection s t G := by
  simp only [metricActionCoefficient, metricAxisJet_orthonormal,
    metricKineticCoefficient, kineticCoefficient_smul_left, kineticCoefficient_smul_right]
  ring

/-- Fourier convention `∂a ↦ iξa` applied to the `-C` second-jet term of
`linearizedCoordinateDensityEuler_eq_lower_sub_secondJet`. -/
def densityEulerPrincipalMatrix {ι : Type*} (S : ι → Mat) (G : Mat) (ξ : Covector)
    (i j : ι) : ℝ :=
  ∑ a, ∑ b, metricActionCoefficient S (a, i) (b, j) G * (ξ a * ξ b)

theorem densityEulerPrincipalMatrix_orthonormal (G : Mat) (ξ : Covector) (i j : I) :
    densityEulerPrincipalMatrix orthonormalMetricDirection G ξ i j =
      (symmetricMetricScale i)⁻¹ * (symmetricMetricScale j)⁻¹ *
        densityEulerPrincipalMatrix symmetricMetricDirection G ξ i j := by
  simp only [densityEulerPrincipalMatrix, metricActionCoefficient_orthonormal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem planeJet_eq_axis_sum {ι : Type*} (S : ι → Mat) (ξ : Covector) (i : ι) :
    planeJet ξ (S i) = ∑ a, ξ a • metricAxisJet S (a, i) := by
  funext a
  rw [Finset.sum_apply, Finset.sum_eq_single a]
  · ext b c
    simp [planeJet, metricAxisJet, Matrix.smul_apply, smul_eq_mul]
  · intro b _ hb
    simp [metricAxisJet, hb.symm]
  · simp

private theorem planeJet_eq_field_sum {ι : Type*} [Fintype ι] (S : ι → Mat) (ξ : Covector)
    (z : ι → ℝ) : planeJet ξ (assembleMetricComponents S z) = ∑ j, z j • planeJet ξ (S j) := by
  funext a b c
  simp only [planeJet, assembleMetricComponents_apply, Finset.sum_apply, Matrix.sum_apply,
    Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem metricKineticCoefficient_planepair_eq_fourier (G : Mat) (ξ : Covector) (J L : Mat) :
    metricKineticCoefficient G (planeJet ξ J) (planeJet ξ L) = principalHessianPairing G ξ J L := by
  have hNeg : planeJet (-ξ) L = (-1 : ℝ) • planeJet ξ L := by
    simpa only [neg_one_smul] using planeJet_smul_covector ξ L (-1 : ℝ)
  rw [principalHessianPairing, hNeg]
  simp only [metricKineticCoefficient, kineticCoefficient_smul_right, neg_one_mul, mul_neg, neg_neg]

/-- Exact sign and Fourier normalization, on each output row and input
column of the actual density Hessian. -/
theorem densityEulerPrincipalMatrix_eq_fourierHessian {ι : Type*} (S : ι → Mat)
    (G : Mat) (ξ : Covector) (i j : ι) :
    densityEulerPrincipalMatrix S G ξ i j = principalHessianPairing G ξ (S j) (S i) := by
  rw [← metricKineticCoefficient_planepair_eq_fourier]
  change _ = metricKineticBilinear G (planeJet ξ (S j)) (planeJet ξ (S i))
  rw [planeJet_eq_axis_sum S ξ j, planeJet_eq_axis_sum S ξ i]
  simp only [densityEulerPrincipalMatrix, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change metricActionCoefficient S (a, i) (b, j) G * (ξ a * ξ b) =
    ξ a * (ξ b * metricActionCoefficient S (b, j) (a, i) G)
  rw [metricActionCoefficient_swap S (b, j) (a, i)]
  ring

theorem densityEulerPrincipalMatrix_eq_raisedRicci (G : Mat) (ξ : Covector) (i j : I)
    (hG : IsSymmetricTensor G) :
    densityEulerPrincipalMatrix orthonormalMetricDirection G ξ i j = metricDensity G *
      physicalPairing (inverseMatrix G) (ricciSymbol (inverseMatrix G) ξ (orthonormalMetricDirection j))
        (orthonormalMetricDirection i) := by
  rw [densityEulerPrincipalMatrix_eq_fourierHessian]
  exact principalHessianPairing_eq_physicalRicci G ξ _ _ hG
    (orthonormalMetricDirection_isSymmetric j) (orthonormalMetricDirection_isSymmetric i)

private theorem eulerPrincipal_real_pairing_eq_fourier {ι : Type*} [Fintype ι] (S : ι → Mat)
    (G : Mat) (ξ : Covector) (z w : ι → ℝ) :
    principalHessianPairing G ξ (assembleMetricComponents S z) (assembleMetricComponents S w) =
      ∑ i, ∑ j, densityEulerPrincipalMatrix S G ξ i j * z j * w i := by
  rw [← metricKineticCoefficient_planepair_eq_fourier]
  change metricKineticBilinear G _ _ = _
  rw [planeJet_eq_field_sum S ξ z, planeJet_eq_field_sum S ξ w]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change w i * (z j * metricKineticCoefficient G (planeJet ξ (S j)) (planeJet ξ (S i))) = _
  rw [metricKineticCoefficient_planepair_eq_fourier, ← densityEulerPrincipalMatrix_eq_fourierHessian S]
  ring

/-- Complexification of the same real lower tensor assembly. -/
def assembleComplexMetricComponents {ι : Type*} [Fintype ι] (S : ι → Mat)
    (z : ι → ℂ) : ComplexTensor2 := fun a b =>
  ⟨assembleMetricComponents S (fun i => (z i).re) a b,
    assembleMetricComponents S (fun i => (z i).im) a b⟩

theorem assembleComplexMetricComponents_isSymmetric {ι : Type*} [Fintype ι] (S : ι → Mat)
    (hS : ∀ i, IsSymmetricTensor (S i)) (z : ι → ℂ) :
    IsSymmetricComplexTensor (assembleComplexMetricComponents S z) := by
  intro a b
  apply Complex.ext <;>
    simp only [assembleComplexMetricComponents, assembleMetricComponents_apply,
      Matrix.sum_apply, Matrix.smul_apply, hS _ a b]

/-- Fourier pairing is linear in the input and conjugate-linear in the
test, as in the paper. Both field slots may be complex. -/
def densityEulerPrincipalForm {ι : Type*} [Fintype ι] (S : ι → Mat) (G : Mat) (ξ : Covector)
    (z w : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, (densityEulerPrincipalMatrix S G ξ i j : ℂ) * z j * conj (w i)

theorem densityEulerPrincipalForm_eq_hermitianFourierHessian {ι : Type*} [Fintype ι]
    (S : ι → Mat) (G : Mat) (ξ : Covector) (z w : ι → ℂ) :
    densityEulerPrincipalForm S G ξ z w = hermitianPrincipalHessianPairing G ξ
      (assembleComplexMetricComponents S z) (assembleComplexMetricComponents S w) := by
  apply Complex.ext
  · change (densityEulerPrincipalForm S G ξ z w).re =
      principalHessianPairing G ξ (assembleMetricComponents S (fun i => (z i).re))
        (assembleMetricComponents S (fun i => (w i).re)) +
      principalHessianPairing G ξ (assembleMetricComponents S (fun i => (z i).im))
        (assembleMetricComponents S (fun i => (w i).im))
    simp only [densityEulerPrincipalForm, Complex.re_sum,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, zero_mul, sub_zero,
      eulerPrincipal_real_pairing_eq_fourier, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · change (densityEulerPrincipalForm S G ξ z w).im =
      principalHessianPairing G ξ (assembleMetricComponents S (fun i => (z i).im))
        (assembleMetricComponents S (fun i => (w i).re)) -
      principalHessianPairing G ξ (assembleMetricComponents S (fun i => (z i).re))
        (assembleMetricComponents S (fun i => (w i).im))
    simp only [densityEulerPrincipalForm, Complex.im_sum,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, zero_mul, sub_zero,
      eulerPrincipal_real_pairing_eq_fourier, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The paper's density Hessian in the orthonormal basis, retaining the
actual Lorentz contraction, the metric density and the multiplier `4P`. -/
theorem normalizedDensityEulerPrincipalForm_eq_phase_sub_gauge
    (G : Mat) (hG : IsSymmetricTensor G) (ξ : Covector) (z w : I → ℂ) :
    let J := assembleComplexMetricComponents orthonormalMetricDirection z
    let L := assembleComplexMetricComponents orthonormalMetricDirection w
    let B := inverseMatrix G
    densityEulerPrincipalForm orthonormalMetricDirection G ξ z w =
      (metricDensity G : ℂ) *
        (4 * ((symbolNorm B ξ / 2 : ℝ) : ℂ) * physicalForm B J L -
          gaugeHermitianPairing B (gaugeCovector B ξ J) (gaugeCovector B ξ L)) := by
  intro J L B
  have hJ := assembleComplexMetricComponents_isSymmetric orthonormalMetricDirection
    orthonormalMetricDirection_isSymmetric z
  have hL := assembleComplexMetricComponents_isSymmetric orthonormalMetricDirection
    orthonormalMetricDirection_isSymmetric w
  rw [densityEulerPrincipalForm_eq_hermitianFourierHessian,
    hermitianPrincipalHessianPairing_eq_hessianPairing G ξ J L hG hJ hL,
    hessianPairing_eq_phase_sub_gauge B (inverseMatrix_symmetric G hG) _ ξ J L hL]

end Burnett.V03.Palatini
