import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugePhase
import Burnett.Analysis.GaugeProjection.GaugeProjectionFourier

set_option autoImplicit false
set_option maxRecDepth 6500
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.C02

open Set Metric MeasureTheory Burnett.A02.FrequencySplit Burnett.A05 Burnett.Analysis.CapFourier
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight quadratic)
open Burnett.V08 (signedCyclicPhase normalizedGaugePotential originalGaugeSpectrum)
open Burnett.RicciSymbol (Tensor2)
open Burnett.P01 (ComplexComponents ComplexCovector ProjectionSchwartzMatrix)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.C03 (projectedGaugeComplement)
open scoped ContDiff Matrix

open private complexFrequency from Burnett.Analysis.GaugeProjection.GaugeProjectionFourier

private theorem wardTensorBasis_expand (H : ComplexComponents) :
    H = ∑ k : OrderedPair, H k.1 k.2 • wardTensorBasis k := by
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4, Matrix.single i j (H i j) := Matrix.matrix_eq_sum_single H
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [wardTensorBasis, Matrix.smul_single, smul_eq_mul, mul_one]

private def normalizedGaugePotentialLinear (d : E) : ComplexComponents →ₗ[ℂ] ComplexCovector where
  toFun := normalizedGaugePotential d
  map_add' A B := by
    simp only [normalizedGaugePotential, Matrix.add_mulVec, dotProduct_add, add_div, add_smul]
    abel
  map_smul' c H := by
    simp only [RingHom.id_apply, normalizedGaugePotential, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      mul_div_assoc, ← smul_smul, smul_sub]

private def wardGaugeDotLinear (m : Tensor2) (p : E) : ComplexCovector →ₗ[ℂ] ℂ where
  toFun := fun v => raisedWardGaugeDot m v p
  map_add' u v := by
    simp only [raisedWardGaugeDot, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [raisedWardGaugeDot, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

private def wardGaugePotentialContraction (m : Tensor2) (p : E) : ComplexComponents →ₗ[ℂ] ℂ :=
  (wardGaugeDotLinear m p).comp (((‖p‖⁻¹ : ℝ) : ℂ) • normalizedGaugePotentialLinear (‖p‖⁻¹ • p))

private def wardScreenPairRight (m : Tensor2) (H : ComplexComponents) : ComplexComponents →ₗ[ℂ] ℂ where
  toFun := frozenWardScreenPair m H
  map_add' J L := by
    simp only [frozenWardScreenPair, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c J := by
    simp only [frozenWardScreenPair, RingHom.id_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← mul_assoc c, mul_comm c (1 / 4 : ℂ), mul_assoc]
    apply congrArg (fun z => (1 / 4 : ℂ) * z)
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

private def wardScreenPairBilinear (m : Tensor2) : ComplexComponents →ₗ[ℂ] ComplexComponents →ₗ[ℂ] ℂ where
  toFun := wardScreenPairRight m
  map_add' H K := by
    ext J
    change frozenWardScreenPair m (H+K) J = frozenWardScreenPair m H J + frozenWardScreenPair m K J
    simp only [frozenWardScreenPair, Matrix.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  map_smul' c H := by
    ext J
    change frozenWardScreenPair m (c • H) J = c * frozenWardScreenPair m H J
    simp only [frozenWardScreenPair, Matrix.smul_apply, smul_eq_mul]
    rw [← mul_assoc c, mul_comm c (1 / 4 : ℂ), mul_assoc]
    apply congrArg (fun z => (1 / 4 : ℂ) * z)
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

private def wardMiddleScalar (ϑ : ℝ → ℝ) (κ : ℝ) (m : Tensor2) (w : ℝ) (a : E → ℝ) (x : Joint) : ℂ :=
  (lowSlotWeight ϑ κ x.1 x.2 (-(x.1+x.2)) : ℂ) * (signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) *
    ((quadratic m x.2 : ℂ) + (quadratic m (-(x.1+x.2)) : ℂ))

private def wardMiddleTrilinear (ϑ : ℝ → ℝ) (κ : ℝ) (m : Tensor2) (w : ℝ) (a : E → ℝ) (x : Joint) :
    ComplexComponents →ₗ[ℂ] ComplexComponents →ₗ[ℂ] ComplexComponents →ₗ[ℂ] ℂ := by
  classical
  exact if x.1 ≠ 0 ∧ x.2 ≠ 0 then
    ((LinearMap.lsmul ℂ (ComplexComponents →ₗ[ℂ] ComplexComponents →ₗ[ℂ] ℂ)).flip
      (wardScreenPairBilinear m)).comp (wardMiddleScalar ϑ κ m w a x • wardGaugePotentialContraction m x.1)
  else 0

private theorem wardMiddleTrilinear_eq_symbol (ϑ : ℝ → ℝ) (κ : ℝ) (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (x : Joint) (G H J : ComplexComponents) :
    wardMiddleTrilinear ϑ κ m w a x G H J = wardLowGaugeMiddleSymbol ϑ κ m w a G H J x := by
  classical
  by_cases hx : x.1 ≠ 0 ∧ x.2 ≠ 0
  · rw [wardMiddleTrilinear, if_pos hx, wardLowGaugeMiddleSymbol, if_pos hx]
    let v : ComplexCovector := (↑‖x.1‖⁻¹ : ℂ) • normalizedGaugePotential (endpointDirection x.1) G
    change wardMiddleScalar ϑ κ m w a x * raisedWardGaugeDot m v x.1 * frozenWardScreenPair m H J =
      (lowSlotWeight ϑ κ x.1 x.2 (-(x.1+x.2)) : ℂ) * ((signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) *
        raisedWardGaugeDot m v x.1 * ((quadratic m x.2 : ℂ) + (quadratic m (-(x.1+x.2)) : ℂ)) *
        frozenWardScreenPair m H J)
    unfold wardMiddleScalar
    ring
  · simp only [wardMiddleTrilinear, wardLowGaugeMiddleSymbol, if_neg hx, LinearMap.zero_apply]

private theorem expand_wardMiddleTrilinear
    (A : ComplexComponents →ₗ[ℂ] ComplexComponents →ₗ[ℂ] ComplexComponents →ₗ[ℂ] ℂ) (G H J : ComplexComponents) :
    A G H J = ∑ k : OrderedPair, ∑ l : OrderedPair, ∑ j : OrderedPair,
      A (wardTensorBasis k) (wardTensorBasis l) (wardTensorBasis j) * G k.1 k.2 * H l.1 l.2 * J j.1 j.2 := by
  conv_lhs => rw [wardTensorBasis_expand G]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  conv_lhs => rw [wardTensorBasis_expand H]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  conv_lhs => rw [wardTensorBasis_expand J]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The exact tensor integrand for a low gauge and two thin-screen
physical factors of the same original receiving-chart fluctuation. -/
def wardLowGaugeMiddleTensorWeight (ϑ : ℝ → ℝ) (κ : ℝ) (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) (x : Joint) : ℂ :=
  let V := actualThinSchwartzField m wi wo hm hη i o z
  let H (ξ : E) : ComplexComponents := fun a b => radianFourier (V (a,b)) ξ
  wardLowGaugeMiddleSymbol ϑ κ m w a (originalGaugeSpectrum z x.1) (H x.2) (H (-(x.1+x.2))) x

/-- Finite tensor recombination of the exact scalar branch. All three
slots are the fixed input's actual Fourier spectra. -/
theorem wardLowGaugeMiddleTensorWeight_eq_sum (ϑ : ℝ → ℝ) (κ : ℝ) (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) (x : Joint) :
    let V := actualThinSchwartzField m wi wo hm hη i o z
    wardLowGaugeMiddleTensorWeight ϑ κ m w a wi wo hm hη i o z x =
      ∑ k : OrderedPair, ∑ l : OrderedPair, ∑ j : OrderedPair,
        radianTrilinearWeight (wardLowGaugeMiddleSymbol ϑ κ m w a (wardTensorBasis k) (wardTensorBasis l) (wardTensorBasis j))
          (projectedGaugeComplement z k.1 k.2) (V l) (V j) x := by
  intro V
  rw [wardLowGaugeMiddleTensorWeight, ← wardMiddleTrilinear_eq_symbol, expand_wardMiddleTrilinear]
  simp only [wardMiddleTrilinear_eq_symbol, radianTrilinearWeight, radianWeight, originalGaugeSpectrum,
    Complex.ofReal_one, one_mul, mul_assoc, V]

end Burnett.C02
