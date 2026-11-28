import Burnett.Analysis.FrozenTransport.Ward.WardActualThinSpectrum
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers
import Burnett.Analysis.TransportPatches.ActualWideOrderedSymbols
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers

set_option autoImplicit false
set_option maxRecDepth 6700
set_option maxHeartbeats 12900000
noncomputable section

namespace Burnett.C02

open Matrix Burnett.RicciSymbol Burnett.V06 Burnett.A02.FrequencySplit
open Burnett.P01 (ComplexComponents ProjectionSchwartzMatrix projectionFullSchwartz)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Analysis.ProjectiveNullCaps (thinConeProfile)
open scoped Matrix

open private orderedBasis from Burnett.Analysis.TransportPatches.ActualWideOrderedSymbols
open private raisedWardScreenEntry from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
open private raisedScreenBilinear from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers

private theorem wardFiniteColumnContraction_zero (D : OrderedPair → Index → ℝ)
    (c : OrderedPair → ℂ) (v : Covector) (hD : ∀ j, ∑ b, D j b * v b = 0) :
    (∑ b, (∑ j, (D j b : ℂ) * c j) * (v b : ℂ)) = 0 := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  calc
    _ = (∑ b, (D j b : ℂ) * (v b : ℂ)) * c j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = 0 := by
      have h := congrArg Complex.ofReal (hD j)
      push_cast at h
      rw [h, zero_mul]

/-- The true infrared/thin-screen Schwartz Fourier tensor has both metric
transversality identities at every frequency. Each ordered column is used
before summing against the actual projected input coefficients. -/
theorem wardActualThinSpectrum_metricTransverse (m : Tensor2) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix) (ξ : E) :
    let H := wardActualThinSpectrum m wi wo hm hη i o z ξ
    let v := m *ᵥ (fun j : Index => ξ j)
    (∀ a, ∑ b, H a b * (v b : ℂ) = 0) ∧ (∀ b, ∑ a, H a b * (v a : ℂ) = 0) := by
  intro H v
  let S := thinScreenAngular m wi wo hm hη i o
  let c (j : OrderedPair) := radianFourier (projectionFullSchwartz z j.1 j.2) ξ
  let D (j : OrderedPair) : Tensor2 := fun a b => S.matrix ξ (a,b) j
  have hD (j : OrderedPair) : D j *ᵥ v = 0 ∧ (D j)ᵀ *ᵥ v = 0 := by
    let K := globalAngularScreenSymbol wi wo m (orderedBasis j) (fun d => ξ d)
    let χ := thinConeProfile m η i o ξ
    have hK : K *ᵥ v = 0 ∧ Kᵀ *ᵥ v = 0 :=
      globalAngularScreenSymbol_kills_metricCovector wi wo m (orderedBasis j) (fun d => ξ d)
    have he : D j = χ • K := rfl
    constructor
    · rw [he, smul_mulVec, hK.1, smul_zero]
    · rw [he, transpose_smul, smul_mulVec, hK.2, smul_zero]
  have hH (a b : Index) : H a b = ∑ j : OrderedPair, (D j a b : ℂ) * c j :=
    wardActualThinSpectrum_eq_sum m wi wo hm hη i o z ξ (a,b)
  constructor
  · intro a
    simp_rw [hH]
    exact wardFiniteColumnContraction_zero (fun j b => D j a b) c v (fun j => congrFun (hD j).1 a)
  · intro b
    simp_rw [hH]
    exact wardFiniteColumnContraction_zero (fun j a => D j a b) c v (fun j => congrFun (hD j).2 b)

private theorem wardRaisedScreenEntry_eq_matrix (m : Tensor2) (H : ComplexComponents) (a b : Index) :
    let M := Matrix.map (Matrix.of m) Complex.ofReal
    raisedWardScreenEntry m H a b = (M * H * Mᵀ) a b := by
  intro M
  simp only [M, raisedWardScreenEntry, Matrix.mul_apply, transpose_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem wardRaisedScreenEntry_transverse (m : Tensor2) (H : ComplexComponents) (ξ : E)
    (hm : mᵀ = m) (h₀ : ∀ a, ∑ b, H a b * ((m *ᵥ (fun j => ξ j)) b : ℂ) = 0)
    (h₁ : ∀ b, ∑ a, H a b * ((m *ᵥ (fun j => ξ j)) a : ℂ) = 0) :
    (∀ b, ∑ a, raisedWardScreenEntry m H a b * (ξ a : ℂ) = 0) ∧
    (∀ a, ∑ b, raisedWardScreenEntry m H a b * (ξ b : ℂ) = 0) := by
  let M := Matrix.map (Matrix.of m) Complex.ofReal
  let q : Index → ℂ := fun j => (ξ j : ℂ)
  have hM : Mᵀ = M := by ext i j; exact congrArg Complex.ofReal (congrFun (congrFun hm i) j)
  have hq (b : Index) : (M *ᵥ q) b = ((m *ᵥ (fun j => ξ j)) b : ℂ) := by
    simp only [M, q, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Complex.ofReal_sum, Complex.ofReal_mul]
  have hv₀ : H *ᵥ (M *ᵥ q) = 0 := by
    funext a
    change ∑ b, H a b * (M *ᵥ q) b = 0
    simp only [hq, h₀]
  have hv₁ : Hᵀ *ᵥ (M *ᵥ q) = 0 := by
    funext b
    change ∑ a, H a b * (M *ᵥ q) a = 0
    simp only [hq, h₁]
  have hR : (M * H * Mᵀ) *ᵥ q = 0 := by
    simp only [← mulVec_mulVec, hM, hv₀, mulVec_zero]
  have hL : (M * H * Mᵀ)ᵀ *ᵥ q = 0 := by
    simp only [transpose_mul, ← mulVec_mulVec, hM, hv₁, mulVec_zero]
  constructor
  · intro b
    simp_rw [wardRaisedScreenEntry_eq_matrix]
    exact congrFun hL b
  · intro a
    simp_rw [wardRaisedScreenEntry_eq_matrix]
    exact congrFun hR a

/-- The exact double-gauge signed-third substitution has no additional
transversality input for the actual C02 thin-screen Fourier field. -/
theorem wardActualThinSpectrum_doubleGauge_signedThird (m : Tensor2) (hSym : mᵀ = m)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) (p q : E) :
    let H := wardActualThinSpectrum m wi wo hm hη i o z q
    raisedScreenBilinear m H (-(p+q)) (-(p+q)) = raisedScreenBilinear m H p p := by
  intro H
  obtain ⟨h₀,h₁⟩ := wardActualThinSpectrum_metricTransverse m wi wo hm hη i o z q
  obtain ⟨hL,hR⟩ := wardRaisedScreenEntry_transverse m H q hSym h₀ h₁
  exact raisedScreenBilinear_signedThird_self m H p q hL hR

end Burnett.C02
