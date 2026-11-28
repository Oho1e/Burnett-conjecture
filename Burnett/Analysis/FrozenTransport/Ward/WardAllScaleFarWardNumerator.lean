import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleDensityVertex
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleCyclicHighPassTest
import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalLowGaugeCorrection

set_option autoImplicit false
set_option maxRecDepth 7800
set_option maxHeartbeats 10800000

noncomputable section

namespace Burnett.C02

open MeasureTheory Burnett.Analysis.TransportWardSymbol Burnett.RicciSymbol Burnett.V04
open Burnett.A02.FrequencySplit (E Joint radianFourier)
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight angularNearWeight)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix projectionFullSchwartz
  projectionFullSchwartz_radianFourier regularizedComplexGaugeProjection
  gaugeProjectionInfrared gaugeProjectionInfrared_zero gaugeProjectionInfrared_one)
open Burnett.V08 (signedCyclicPhase)
open scoped ComplexConjugate Matrix

open private radianFourier_real_reflection from Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalLowGaugeCorrection

private theorem wardVertex_expand_column_sums (G : Mat) (hG : Matrix.det G ≠ 0)
    (p q r : Cov) (A B C : OrderedPair → ComplexTensor2) (a b c : OrderedPair → ℂ) :
    complexPrincipalVertex G p (∑ k, a k • A k) q (∑ j, b j • B j) r (∑ i, c i • C i) =
      ∑ i : OrderedPair, ∑ j : OrderedPair, ∑ k : OrderedPair,
        c i * (b j * (a k * complexPrincipalVertex G p (A k) q (B j) r (C i))) := by
  let L₀ (J K : ComplexTensor2) : ComplexTensor2 →ₗ[ℂ] ℂ := {
    toFun := fun H => complexPrincipalVertex G p H q J r K
    map_add' := fun _ _ => complexPrincipalVertex_add_first_amplitude G hG p _ _ q J r K
    map_smul' := fun _ _ => complexPrincipalVertex_smul_first_amplitude G hG p _ q J r K _ }
  let L₁ (H K : ComplexTensor2) : ComplexTensor2 →ₗ[ℂ] ℂ := {
    toFun := fun J => complexPrincipalVertex G p H q J r K
    map_add' := fun _ _ => complexPrincipalVertex_add_second_amplitude G hG p H q _ _ r K
    map_smul' := fun _ _ => complexPrincipalVertex_smul_second_amplitude G hG p H q _ r K _ }
  let L₂ (H J : ComplexTensor2) : ComplexTensor2 →ₗ[ℂ] ℂ := {
    toFun := fun K => complexPrincipalVertex G p H q J r K
    map_add' := fun _ _ => complexPrincipalVertex_add_third_amplitude G hG p H q J r _ _
    map_smul' := fun _ _ => complexPrincipalVertex_smul_third_amplitude G hG p H q J r _ _ }
  have hA (J K : ComplexTensor2) :
      complexPrincipalVertex G p (∑ k, a k • A k) q J r K =
        ∑ k, a k * complexPrincipalVertex G p (A k) q J r K := by
    change L₀ J K (∑ k, a k • A k) = ∑ k, a k * L₀ J K (A k)
    simp only [map_sum, map_smul, smul_eq_mul]
  have hB (H K : ComplexTensor2) :
      complexPrincipalVertex G p H q (∑ j, b j • B j) r K =
        ∑ j, b j * complexPrincipalVertex G p H q (B j) r K := by
    change L₁ H K (∑ j, b j • B j) = ∑ j, b j * L₁ H K (B j)
    simp only [map_sum, map_smul, smul_eq_mul]
  have hC (H J : ComplexTensor2) :
      complexPrincipalVertex G p H q J r (∑ i, c i • C i) =
        ∑ i, c i * complexPrincipalVertex G p H q J r (C i) := by
    change L₂ H J (∑ i, c i • C i) = ∑ i, c i * L₂ H J (C i)
    simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [hC,hB,hA,Finset.mul_sum]

/-- The signed first physical-low far sector has exactly the original
V11 ordered numerator, including all three screen columns, both nested
high-frequency windows, and the original high tested adjoint. -/
theorem wardActualFarWeight_eq_original_numerator (G : Mat) (hG : Matrix.det G ≠ 0)
    (a : E → ℝ) (ϑ : ℝ → ℝ) (κ δ : ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) (hz : ∀ a b x, conj (z a b x) = z a b x)
    (x : Joint) :
    let p := x.1
    let q := x.2
    let r := -(p+q)
    let S := thinScreenAngular (inverseMatrix G) wi wo hm hη i o
    let H := wardActualThinSpectrum (inverseMatrix G) wi wo hm hη i o z
    let u (k : OrderedPair) (ξ : E) := radianFourier (projectionFullSchwartz z k.1 k.2) ξ
    let C (ξ : E) (k t : OrderedPair) := S.complex ξ t k
    let w := ((lowSlotWeight ϑ κ p q r * (1 - angularNearWeight ϑ δ p q r) : ℝ) : ℂ)
    w * wardCyclicCubicWeight G a H H H x =
      ∑ I : OrderedPair, ∑ J : OrderedPair, ∑ k : OrderedPair,
        (gaugeProjectionInfrared (2 * ‖q‖) : ℂ) * (gaugeProjectionInfrared (2 * ‖p+q‖) : ℂ) *
        (w * ((-Complex.I / 3) * (signedCyclicPhase a p q : ℂ) *
          frozenDensityCubicVertex frozenActionOrderedBasis G p (C p k) q (C q J) r (C r I))) *
        u k p * u J q * conj (u I (q+p)) := by
  intro p q r S H u C w
  let F (ξ : E) (k : OrderedPair) : ComplexTensor2 := fun a b => C ξ k (a,b)
  have hH (ξ : E) : H ξ = ∑ k, u k ξ • F ξ k := by
    funext a b
    rw [show H ξ a b = wardActualThinSpectrum (inverseMatrix G) wi wo hm hη i o z ξ (a,b).1 (a,b).2 from rfl,
      wardActualThinSpectrum_eq_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, F, C, RealOrderedAngularMatrix.complex]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hLow (ξ : E) (hξ : ‖ξ‖ ≤ 1) (k : OrderedPair) : u k ξ = 0 := by
    change radianFourier (projectionFullSchwartz z k.1 k.2) ξ = 0
    rw [projectionFullSchwartz_radianFourier]
    simp only [regularizedComplexGaugeProjection, gaugeProjectionInfrared_zero hξ,
      Complex.ofReal_zero, zero_smul, Matrix.zero_apply]
  have hIR (ξ : E) (k : OrderedPair) :
      (gaugeProjectionInfrared (2 * ‖ξ‖) : ℂ) * u k ξ = u k ξ := by
    by_cases hξ : 1 < ‖ξ‖
    · rw [gaugeProjectionInfrared_one (by linarith only [hξ]), Complex.ofReal_one, one_mul]
    · rw [hLow ξ (le_of_not_gt hξ), mul_zero]
  have href (k : OrderedPair) : conj (u k (q+p)) = u k r := by
    rw [add_comm q p]
    exact (radianFourier_real_reflection (projectionFullSchwartz z k.1 k.2)
      (projectionFullSchwartz_real_of_source z hz k) (p+q)).symm
  have hr : ‖p+q‖ = ‖r‖ := (norm_neg (p+q)).symm
  change w * ((-Complex.I / 3) * (signedCyclicPhase a p q : ℂ) *
    complexPrincipalVertex G (fun d => p d) (H p) (fun d => q d) (H q) (fun d => r d) (H r)) = _
  rw [hH p, hH q, hH r, wardVertex_expand_column_sums G hG]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  apply Finset.sum_congr rfl
  intro k _
  rw [wardComplexPrincipalVertex_eq_physicalDensityVertex G hG, href I, hr]
  have h₁ := hIR q J
  have h₂ := hIR r I
  conv_rhs =>
    rw [show (gaugeProjectionInfrared (2 * ‖q‖) : ℂ) * (gaugeProjectionInfrared (2 * ‖r‖) : ℂ) *
        (w * ((-Complex.I / 3) * (signedCyclicPhase a p q : ℂ) *
          frozenDensityCubicVertex frozenActionOrderedBasis G p (C p k) q (C q J) r (C r I))) *
        u k p * u J q * u I r =
      (w * ((-Complex.I / 3) * (signedCyclicPhase a p q : ℂ) *
          frozenDensityCubicVertex frozenActionOrderedBasis G p (C p k) q (C q J) r (C r I))) *
        u k p * ((gaugeProjectionInfrared (2 * ‖q‖) : ℂ) * u J q) *
        ((gaugeProjectionInfrared (2 * ‖r‖) : ℂ) * u I r) by ring, h₁, h₂]
  dsimp only [F]
  ring

end Burnett.C02
