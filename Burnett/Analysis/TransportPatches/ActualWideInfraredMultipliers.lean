import Burnett.Analysis.TransportPatches.SharedInfraredAngularMatrix
import Burnett.Analysis.TransportPatches.ActualWideOrderedSymbols

/-! The two concrete frozen wide errors acting on the one original projected field. -/

set_option autoImplicit false
set_option maxRecDepth 5100
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Matrix Burnett.Fourier Burnett.RicciSymbol Burnett.V06
open Burnett.A02.FrequencySplit (E tau)
open Burnett.Analysis.ProjectiveNullCaps (quadratic quadratic_smul)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (principalGaugeProjectionMatrix regularizedProjectionComponentSymbol
  regularizedGaugeProjectionSymbol gaugeProjectionInfrared gaugeProjectionSymbol_scale)
open scoped BigOperators ContDiff Matrix

open private orderedBasis from Burnett.Analysis.TransportPatches.ActualWideOrderedSymbols

/-- The compact-family wide construction provides smoothness for these
same cutoffs and ordered screen entries. -/
def WideScreenFrequencySmooth (inner outer : ℝ) (m : ScreenMatrix) : Prop :=
  ∀ H : ScreenMatrix, ∀ a b : Index,
    ContDiffOn ℝ ∞ (fun ξ : E => globalAngularScreenSymbol inner outer m H (fun i => ξ i) a b)
      ({0}ᶜ : Set E)

theorem normalizedFrozenPhase_contDiffOn (m : ScreenMatrix) :
    ContDiffOn ℝ ∞ (normalizedFrozenPhase m) ({0}ᶜ : Set E) := by
  have hQ : ContDiff ℝ ∞ (quadratic m : E → ℝ) := by
    unfold quadratic Burnett.Analysis.ProjectiveNullCaps.pairing Burnett.Analysis.ProjectiveNullCaps.rowValue
    apply ContDiff.sum
    intro j _
    apply ContDiff.mul _ (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
    apply ContDiff.sum
    intro i _
    exact contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  unfold normalizedFrozenPhase
  exact hQ.contDiffOn.div (contDiff_norm_sq ℝ).contDiffOn
    (fun _ hξ => pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ))

theorem normalizedFrozenPhase_degreeZero (m : ScreenMatrix) (t : ℝ) (ht : 0 < t) (ξ : E) :
    normalizedFrozenPhase m (t • ξ) = normalizedFrozenPhase m ξ := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  unfold normalizedFrozenPhase
  rw [quadratic_smul, norm_smul, Real.norm_of_nonneg ht.le, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 ht.ne')

def RealOrderedAngularMatrix.identity : RealOrderedAngularMatrix where
  matrix _ := 1
  smooth _ _ := contDiffOn_const
  degree _ _ _ := rfl

theorem RealOrderedAngularMatrix.identity_complex (ξ : E) :
    RealOrderedAngularMatrix.identity.complex ξ = 1 := by
  ext k i
  by_cases h : k = i <;>
    simp [RealOrderedAngularMatrix.complex, RealOrderedAngularMatrix.identity, Matrix.one_apply, h]

def originalProjectedMatrixMultiplier : ClassicalMatrixMultiplier OrderedPair :=
  RealOrderedAngularMatrix.identity.afterOriginalProjection

theorem originalProjectedMatrixMultiplier_principal (ξ : E) :
    originalProjectedMatrixMultiplier.principal ξ = principalGaugeProjectionMatrix ξ := by
  change RealOrderedAngularMatrix.identity.complex ξ * principalGaugeProjectionMatrix ξ = _
  rw [RealOrderedAngularMatrix.identity_complex, one_mul]

theorem originalProjectedMatrixMultiplier_full (k i : OrderedPair) (ξ : E) :
    originalProjectedMatrixMultiplier.full k i ξ = regularizedProjectionComponentSymbol k.1 k.2 i.1 i.2 ξ := by
  rw [originalProjectedMatrixMultiplier, RealOrderedAngularMatrix.afterOriginalProjection_full,
    ← originalProjectedMatrixMultiplier, originalProjectedMatrixMultiplier_principal]
  change (gaugeProjectionInfrared ‖tau • ξ‖ : ℂ) *
      (P01.gaugeProjectionSymbol k.1 k.2 i.1 i.2 ξ : ℂ) =
    (regularizedGaugeProjectionSymbol k.1 k.2 i.1 i.2 (tau • ξ) : ℂ)
  rw [regularizedGaugeProjectionSymbol, gaugeProjectionSymbol_scale _ _ _ _ _ (mul_pos (by norm_num) Real.pi_pos),
    Complex.ofReal_mul]

theorem originalProjectedMatrixMultiplier_output (u : OrderedPair → ComplexL2 E) (k : OrderedPair) :
    originalProjectedMatrixMultiplier.output u k = originalOrderedProjectedField u k := by
  unfold ClassicalMatrixMultiplier.output originalOrderedProjectedField
  apply Finset.sum_congr rfl
  intro i _
  rw [fourierMultiplier_congr_ae _ _ (Eventually.of_forall (originalProjectedMatrixMultiplier_full k i))]

def wideScreenAngular (inner outer : ℝ) (m : ScreenMatrix) (h : WideScreenFrequencySmooth inner outer m) :
    RealOrderedAngularMatrix where
  matrix ξ k j := globalAngularScreenSymbol inner outer m (orderedBasis j) (fun i => ξ i) k.1 k.2
  smooth k j := h (orderedBasis j) k.1 k.2
  degree t ht ξ := by
    ext k j
    exact congrFun (congrFun
      (globalAngularScreenSymbol_degreeZero inner outer m (orderedBasis j) (fun i => ξ i) t ht) k.1) k.2

def frozenScreenErrorAngular (inner outer : ℝ) (m : ScreenMatrix) (h : WideScreenFrequencySmooth inner outer m) :
    RealOrderedAngularMatrix where
  matrix ξ := 1 - (wideScreenAngular inner outer m h).matrix ξ
  smooth k i := contDiffOn_const.sub ((wideScreenAngular inner outer m h).smooth k i)
  degree t ht ξ := by rw [(wideScreenAngular inner outer m h).degree t ht ξ]

def frozenPhaseErrorAngular (inner outer : ℝ) (m : ScreenMatrix) (h : WideScreenFrequencySmooth inner outer m) :
    RealOrderedAngularMatrix where
  matrix ξ := normalizedFrozenPhase m ξ • (wideScreenAngular inner outer m h).matrix ξ
  smooth k i := (normalizedFrozenPhase_contDiffOn m).mul ((wideScreenAngular inner outer m h).smooth k i)
  degree t ht ξ := by
    rw [normalizedFrozenPhase_degreeZero m t ht ξ, (wideScreenAngular inner outer m h).degree t ht ξ]

def actualFrozenScreenErrorMultiplier (inner outer : ℝ) (m : ScreenMatrix)
    (h : WideScreenFrequencySmooth inner outer m) : ClassicalMatrixMultiplier OrderedPair :=
  (frozenScreenErrorAngular inner outer m h).afterOriginalProjection

def actualFrozenPhaseErrorMultiplier (inner outer : ℝ) (m : ScreenMatrix)
    (h : WideScreenFrequencySmooth inner outer m) : ClassicalMatrixMultiplier OrderedPair :=
  (frozenPhaseErrorAngular inner outer m h).afterOriginalProjection

theorem actualFrozenScreenErrorMultiplier_principal (inner outer : ℝ) (m : ScreenMatrix)
    (h : WideScreenFrequencySmooth inner outer m) (ξ : E) :
    (actualFrozenScreenErrorMultiplier inner outer m h).principal ξ =
      actualFrozenScreenErrorOrdered inner outer m ξ := by
  change (frozenScreenErrorAngular inner outer m h).complex ξ * principalGaugeProjectionMatrix ξ =
    (1 - actualWideScreenOrdered inner outer m (fun i => ξ i)) * principalGaugeProjectionMatrix ξ
  congr 1
  ext k i
  by_cases hki : k = i <;> simp [RealOrderedAngularMatrix.complex, frozenScreenErrorAngular,
    wideScreenAngular, actualWideScreenOrdered, hki]

theorem actualFrozenPhaseErrorMultiplier_principal (inner outer : ℝ) (m : ScreenMatrix)
    (h : WideScreenFrequencySmooth inner outer m) (ξ : E) :
    (actualFrozenPhaseErrorMultiplier inner outer m h).principal ξ =
      actualFrozenPhaseErrorOrdered inner outer m ξ := by
  change (frozenPhaseErrorAngular inner outer m h).complex ξ * principalGaugeProjectionMatrix ξ = _
  rw [actualFrozenPhaseErrorOrdered, ← Matrix.smul_mul]
  congr 1
  ext k i
  simp [RealOrderedAngularMatrix.complex, frozenPhaseErrorAngular, wideScreenAngular, actualWideScreenOrdered]

/-- Both actual wide operators have precisely the same fixed scalar infrared
cutoff as the original projected source, in the radian normalization. -/
theorem actualFrozenWideErrors_sharedInfrared (inner outer : ℝ) (m : ScreenMatrix)
    (h : WideScreenFrequencySmooth inner outer m) (ξ : E) (k i : OrderedPair) :
    (actualFrozenScreenErrorMultiplier inner outer m h).full k i ξ =
      (gaugeProjectionInfrared ‖tau • ξ‖ : ℂ) * actualFrozenScreenErrorOrdered inner outer m ξ k i ∧
    (actualFrozenPhaseErrorMultiplier inner outer m h).full k i ξ =
      (gaugeProjectionInfrared ‖tau • ξ‖ : ℂ) * actualFrozenPhaseErrorOrdered inner outer m ξ k i := by
  refine ⟨?_, ?_⟩
  · rw [← actualFrozenScreenErrorMultiplier_principal inner outer m h ξ]
    exact (frozenScreenErrorAngular inner outer m h).afterOriginalProjection_full k i ξ
  · rw [← actualFrozenPhaseErrorMultiplier_principal inner outer m h ξ]
    exact (frozenPhaseErrorAngular inner outer m h).afterOriginalProjection_full k i ξ

/-- Each full multiplier acts on the very same original regularized
projection in the actual ordered tensor entries. -/
theorem actualFrozenWideErrors_originalProjectedOutput (inner outer : ℝ) (m : ScreenMatrix)
    (h : WideScreenFrequencySmooth inner outer m) (u : OrderedPair → ComplexL2 E) (k : OrderedPair) :
    (actualFrozenScreenErrorMultiplier inner outer m h).output u k =
      (frozenScreenErrorAngular inner outer m h).output (originalProjectedMatrixMultiplier.output u) k ∧
    (actualFrozenPhaseErrorMultiplier inner outer m h).output u k =
      (frozenPhaseErrorAngular inner outer m h).output (originalProjectedMatrixMultiplier.output u) k := by
  have hOriginal : originalProjectedMatrixMultiplier.output u = originalOrderedProjectedField u :=
    funext (originalProjectedMatrixMultiplier_output u)
  rw [hOriginal]
  exact ⟨(frozenScreenErrorAngular inner outer m h).afterOriginalProjection_output u k,
    (frozenPhaseErrorAngular inner outer m h).afterOriginalProjection_output u k⟩

end Burnett.C02
