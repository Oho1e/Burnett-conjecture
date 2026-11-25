import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularCutoff

set_option autoImplicit false
set_option maxRecDepth 3700
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.A08

open Burnett.A07 Burnett.A06 Burnett.A02.FrequencySplit
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

open private inner_eq_of_schwartz from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension
open private forwardBounds from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAngularCutoff

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2

private theorem angularTail_tendsto (C : ℝ) :
    Tendsto (fun L : ℕ => C / ((L : ℝ) + 1)^2) atTop (𝓝 0) := by
  have hNat : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hShift := tendsto_atTop_add_const_right _ 1 hNat
  have hSquare := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hShift
  simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
    ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp hSquare).const_mul C

/-- Strong removal of the upper cutoff for a single raw high-slot entry,
with the adjoint tested on the opposite entry of the matrix. -/
theorem symmetricUpperCutoffOutput_tendsto_of_dual (T S : Test → LP2) (C : ℝ)
    (dual : ∀ u w : Test, inner ℂ (w.toLp 2 volume) (T u) = inner ℂ (S w) (u.toLp 2 volume))
    (bound : ∀ u, ‖T u‖ ≤ C * highDerivativeLp4Sum u) (u : Test) :
    Tendsto (fun Λ : ℝ => symmetricUpperCutoffOutput T Λ u) atTop (𝓝 (T u)) := by
  have sub (v w : Test) : T (v - w) = T v - T w := by
    apply inner_eq_of_schwartz
    intro z
    rw [inner_sub_right, dual (v - w) z, dual v z, dual w z]
    exact congrArg (inner ℂ (S z)) ((SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_sub v w) |>.trans
      (inner_sub_right _ _ _)
  have split (Λ : ℝ) : symmetricUpperCutoffOutput T Λ u - T u =
      upperFrequencyCutoffL2 Λ (T (upperFrequencyError Λ u)) +
        (upperFrequencyCutoffL2 Λ (T u) - T u) := by
    rw [symmetricUpperCutoffOutput, upperFrequencyError, sub, map_sub]
    abel
  have smallInput : Tendsto (fun Λ : ℝ => highDerivativeLp4Sum (upperFrequencyError Λ u))
      atTop (𝓝 0) := by
    simpa only [highDerivativeLp4Sum, Finset.sum_const_zero] using (tendsto_finset_sum Finset.univ fun j _ =>
      (coordinateDerivative_upperFrequencyError_tendsto_L2_L4 j u).2)
  have smallOutput : Tendsto (fun Λ : ℝ => ‖upperFrequencyCutoffL2 Λ (T u) - T u‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (upperFrequencyCutoffL2_tendsto (T u))
  have majorant : Tendsto (fun Λ : ℝ => C * highDerivativeLp4Sum (upperFrequencyError Λ u) +
      ‖upperFrequencyCutoffL2 Λ (T u) - T u‖) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (smallInput.const_mul C).add smallOutput
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (fun Λ => ?_) majorant
  rw [split]
  exact (norm_add_le _ _).trans
    (add_le_add_right ((upperFrequencyCutoffL2_norm_le Λ _).trans (bound _)) _)

namespace OriginalAngularCutoff

open scoped ComplexConjugate

variable {η χ : ℝ → ℝ} {F : Joint × RotationSpace → ℂ} {M C₀ C₁ : ℝ}

/-- First remove both high frequency cutoffs at fixed angular truncation,
then exhaust the angular modes of the same raw correction. The two high
fields can be distinct throughout. -/
theorem mixedWavePair_cutoff_recovery (P : OriginalAngularCutoff η χ F M C₀ C₁)
    (m : Fin 4 → Fin 4 → ℝ) (H u w : Test) :
    (∀ N : ℕ, Tendsto (fun Λ : ℝ => weakConstantWaveCommutatorPair m
      (symmetricUpperCutoffOutput (P.partialForward N H) Λ) u w) atTop
      (𝓝 (weakConstantWaveCommutatorPair m (P.partialForward N H) u w))) ∧
    Tendsto (fun N : ℕ => weakConstantWaveCommutatorPair m (P.partialForward N H) u w) atTop
      (𝓝 (weakConstantWaveCommutatorPair m (P.fullForward H) u w)) := by
  constructor
  · intro N
    have dual (v z : Test) : inner ℂ (z.toLp 2 volume) (P.partialForward N H v) =
        inner ℂ (P.partialAdjoint N H z) (v.toLp 2 volume) := by
      rw [← inner_conj_symm (P.partialAdjoint N H z), (P.partialPairs N H z v).2,
        (P.partialPairs N H v z).1]
      simp only [radianHighPair_highAdjoint, map_sum, starRingEnd_self_apply]
    have bound (v : Test) : ‖P.partialForward N H v‖ ≤
        (2 * (C₀ * M * ‖H.toLp 4 volume‖)) * highDerivativeLp4Sum v := by
      simpa only [partialForward, mul_assoc] using (forwardBounds P H v).finiteBound (angularDegreeFinset N)
    have h (v : Test) := symmetricUpperCutoffOutput_tendsto_of_dual _ _ _ dual bound v
    exact (tendsto_const_nhds.inner (h u)).sub (tendsto_const_nhds.inner (h (constantWave m u)))
  · have h (v : Test) : Tendsto (fun N : ℕ => P.partialForward N H v) atTop
        (𝓝 (P.fullForward H v)) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _)
        (fun N => (P.partialPairs_tail N H v).1) (angularTail_tendsto _))
    exact (tendsto_const_nhds.inner (h u)).sub (tendsto_const_nhds.inner (h (constantWave m u)))

end OriginalAngularCutoff
end Burnett.A08
