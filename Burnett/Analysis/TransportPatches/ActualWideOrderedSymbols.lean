import Burnett.Analysis.TransportPatches.OriginalWeightedFrozenCompression

/-! The actual two error symbols in the original ordered tensor slots. -/

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 6200000

noncomputable section

namespace Burnett.C02

open Matrix Burnett.RicciSymbol Burnett.V06
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.PhysicalDensity (OrderedPair tensorOfVector)
open Burnett.P01 (principalGaugeProjectionMatrix)
open scoped BigOperators Matrix ComplexConjugate

open private globalScreen_smul from Burnett.Analysis.TransportPatches.ActualWideScreenLipschitz

local notation "V" => OrderedPair → ℂ
local notation "Mat" => Matrix OrderedPair OrderedPair ℂ

private def wideScreenLinear (inner outer : ℝ) (m : ScreenMatrix) (q : Covector) :
    ScreenMatrix →ₗ[ℝ] ScreenMatrix where
  toFun H := globalAngularScreenSymbol inner outer m H q
  map_add' H K := by
    simp only [globalAngularScreenSymbol, frozenScreenSymbol, frozenScreenProjection,
      Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, add_div, add_smul, add_sub_add_comm, smul_add]
  map_smul' t H := globalScreen_smul inner outer m H q t

private def orderedBasis (j : OrderedPair) : ScreenMatrix :=
  fun i k => if i = j.1 ∧ k = j.2 then 1 else 0

private theorem realBasisExpansion (H : ScreenMatrix) :
    ∑ j : OrderedPair, H j.1 j.2 • orderedBasis j = H := by
  classical
  ext i k
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, orderedBasis]
  rw [Finset.sum_eq_single (i, k)]
  · simp
  · intro a _ ha
    rw [if_neg (fun h => ha (Prod.ext h.1.symm h.2.symm)), mul_zero]
  · simp

/-- The true wide screen in the same ordered coordinate slots as the
original Gram density. The entries are real and act complex-linearly. -/
def actualWideScreenOrdered (inner outer : ℝ) (m : ScreenMatrix) (q : Covector) : Mat :=
  fun i j => (globalAngularScreenSymbol inner outer m (orderedBasis j) q i.1 i.2 : ℂ)

theorem tensorOfVector_actualWideScreenOrdered (inner outer : ℝ) (m : ScreenMatrix) (q : Covector) (u : V) :
    tensorOfVector (actualWideScreenOrdered inner outer m q *ᵥ u) =
      complexWideScreen inner outer m (tensorOfVector u) q := by
  let S := wideScreenLinear inner outer m q
  have hS (H : ScreenMatrix) (i j : Index) :
      globalAngularScreenSymbol inner outer m H q i j =
        ∑ k : OrderedPair, H k.1 k.2 * globalAngularScreenSymbol inner outer m (orderedBasis k) q i j := by
    have h := congrArg S (realBasisExpansion H)
    rw [map_sum] at h
    simp only [map_smul] at h
    have h' := congrFun (congrFun h i) j
    simpa only [S, wideScreenLinear, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using h'.symm
  funext i j
  apply Complex.ext
  · change ((actualWideScreenOrdered inner outer m q *ᵥ u) (i, j)).re =
      globalAngularScreenSymbol inner outer m (tensorRe (tensorOfVector u)) q i j
    rw [hS (tensorRe (tensorOfVector u)) i j]
    simp only [Matrix.mulVec, dotProduct, actualWideScreenOrdered, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, tensorRe, tensorOfVector]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · change ((actualWideScreenOrdered inner outer m q *ᵥ u) (i, j)).im =
      globalAngularScreenSymbol inner outer m (tensorIm (tensorOfVector u)) q i j
    rw [hS (tensorIm (tensorOfVector u)) i j]
    simp only [Matrix.mulVec, dotProduct, actualWideScreenOrdered, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, tensorIm, tensorOfVector]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

def actualFrozenScreenErrorOrdered (inner outer : ℝ) (m : ScreenMatrix) (ξ : E) : Mat :=
  (1 - actualWideScreenOrdered inner outer m (fun i => ξ i)) * principalGaugeProjectionMatrix ξ

def actualFrozenPhaseErrorOrdered (inner outer : ℝ) (m : ScreenMatrix) (ξ : E) : Mat :=
  (normalizedFrozenPhase m ξ : ℂ) •
    (actualWideScreenOrdered inner outer m (fun i => ξ i) * principalGaugeProjectionMatrix ξ)

theorem tensorOfVector_actualFrozenScreenErrorOrdered (inner outer : ℝ) (m : ScreenMatrix)
    (ξ : E) (u : V) :
    let J := tensorOfVector (principalGaugeProjectionMatrix ξ *ᵥ u)
    tensorOfVector (actualFrozenScreenErrorOrdered inner outer m ξ *ᵥ u) =
      J - complexWideScreen inner outer m J (fun i => ξ i) := by
  dsimp only [actualFrozenScreenErrorOrdered]
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [← tensorOfVector_actualWideScreenOrdered]
  rfl

theorem tensorOfVector_actualFrozenPhaseErrorOrdered (inner outer : ℝ) (m : ScreenMatrix)
    (ξ : E) (u : V) :
    let J := tensorOfVector (principalGaugeProjectionMatrix ξ *ᵥ u)
    tensorOfVector (actualFrozenPhaseErrorOrdered inner outer m ξ *ᵥ u) =
      (normalizedFrozenPhase m ξ : ℂ) • complexWideScreen inner outer m J (fun i => ξ i) := by
  dsimp only [actualFrozenPhaseErrorOrdered]
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← tensorOfVector_actualWideScreenOrdered]
  rfl

end Burnett.C02
