import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalMixedWeakEnergy
import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalMixedCutoffRecovery
import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalProjectedSourceBridge
import Burnett.Analysis.TransportPatches.PatchCorrectionEnergyScale
import Burnett.Analysis.TransportPatches.PatchCorrectionLpBudget

set_option autoImplicit false
set_option maxRecDepth 4500
set_option maxHeartbeats 6800000

noncomputable section

namespace Burnett.C03

open Burnett.P01 Burnett.A08 Burnett.A07 Burnett.A06 Burnett.A02.FrequencySplit
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal NNReal Topology

open private inner_eq_of_schwartz from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The volume bound for the original scalar equation applied to any two
entries of the same projected original high field. The raw correction acts
with its true adjoint. Its low entry can be physical or gauge. -/
theorem exists_originalAngular_projectedPatch_envelope
    (η χ : ℝ → ℝ) {r ρ R₀ : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hsmall : ρ < 1/2) (hR : 1 ≤ R₀)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ x ≤ r, η x = 0) (hone : ∀ x ≥ R₀, η x = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ x ≥ ρ ^ 2, χ x = 0) :
    let Q := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
    ∃ (K : ℕ) (C₀ C₁ Corder Cweak : ℝ), 0 ≤ Corder ∧ 0 ≤ Cweak ∧
      ∀ {F : Joint × RotationSpace → ℂ} {U : Set (Joint × RotationSpace)},
      IsOpen U → Q ×ˢ sphere (0 : RotationSpace) 1 ⊆ U → ContDiffOn ℝ ∞ F U →
      ∀ M : ℝ, 0 ≤ M →
      (∀ n ≤ K, ∀ p ∈ Q, ∀ x : RoundSphere3,
        ‖iteratedFDeriv ℝ n F (p, (x : RotationSpace))‖ ≤ M) →
      ∃ P : OriginalAngularCutoff η χ F M C₀ C₁,
        ∀ (m : Tensor2) (d : Index → Index → SchwartzMap E ℝ)
          (A : ProjectedSourceCoefficients) (z : ProjectionSchwartzMatrix) (W : Set E)
          (B ℓ e : ℝ), 1 ≤ B → 0 < ℓ → 0 ≤ e →
        Corder * M ≤ B → 2 * Cweak * M ≤ B →
        (∀ a b, d a b = d b a) →
        (∀ a b x, A.entry a b x = ((m a b + d a b x : ℝ) : ℂ)) →
        (∀ a b x, |d a b x| ≤ B * (ℓ + e)) →
        (∀ a b x, ‖fderiv ℝ (d a b : E → ℝ) x‖ ≤ B * (1 + e / ℓ)) →
        (‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤
          B * (volume W ^ ((1 : ℝ) / 2)).toReal * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e)) →
        (∃ v, ProjectedPatchLpBounds 2 z W v ((B / 4) * (1 + e / ℓ))) →
        ProjectedPatchLpBounds 4 z W (B * e) ((B / 4) * (1 + e / ℓ)) →
        ∀ (low : ProjectionSchwartzMatrix),
          (low = projectionFullSchwartz z ∨ low = projectedGaugeComplement z) →
        ∀ (i j a b k l : Index),
          let u := projectionFullSchwartz z i j
          let w := projectionFullSchwartz z a b
          let H := low k l
          (‖Complex.I * weakConstantWaveCommutatorPair m (P.fullForward H) u w‖ ≤
            (3 * B^5) * (volume W).toReal * Burnett.C04.correctionEnvelope ℓ e) ∧
          (∀ N : ℕ, Tendsto (fun Λ : ℝ => weakConstantWaveCommutatorPair m
            (symmetricUpperCutoffOutput (P.partialForward N H) Λ) u w) atTop
            (𝓝 (weakConstantWaveCommutatorPair m (P.partialForward N H) u w))) ∧
          Tendsto (fun N : ℕ => weakConstantWaveCommutatorPair m (P.partialForward N H) u w) atTop
            (𝓝 (weakConstantWaveCommutatorPair m (P.fullForward H) u w)) := by
  obtain ⟨Ka, C₀, C₁, _, _, _, hAngular⟩ := exists_originalAngular_hermitian_angular_cutoff
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  obtain ⟨Km, Corder, Cweak, hCorder, hCweak, hMixed⟩ := exists_originalAngular_mixed_weak_energy
    η χ hr hρ hsmall hR hη hzero hone hχ hcut
  refine ⟨max Ka Km, C₀, C₁, Corder, Cweak, hCorder, hCweak, ?_⟩
  intro F U hU hQU hSmooth M hM hJet
  obtain ⟨P⟩ := hAngular hU hQU hSmooth M hM (fun n hn => hJet n (hn.trans (Nat.le_max_left Ka Km)))
  refine ⟨P, ?_⟩
  intro m d A z W B ℓ e hB hℓ he hBo hBw hd hA hMag hSlope hSource h₂ h₄ low hLow i j a b k l
  obtain ⟨v₂, h₂⟩ := h₂
  let S := 1 + e / ℓ
  let u := projectionFullSchwartz z i j
  let w := projectionFullSchwartz z a b
  let H := low k l
  let D := B * (ℓ + e)
  let L := Real.toNNReal (B * S)
  let V := (volume W).toReal
  let U₂ := B * S * V ^ ((1 : ℝ) / 2)
  let U₄ := B * S * V ^ ((1 : ℝ) / 4)
  let N := ‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  have hS : 0 ≤ S := add_nonneg zero_le_one (div_nonneg he hℓ.le)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hD : 0 ≤ D := mul_nonneg hB₀ (add_nonneg hℓ.le he)
  have hL : (L : ℝ) = B * S := Real.coe_toNNReal _ (mul_nonneg hB₀ hS)
  have hU₂ : 0 ≤ U₂ := mul_nonneg (mul_nonneg hB₀ hS) (Real.rpow_nonneg hV _)
  have hU₄ : 0 ≤ U₄ := mul_nonneg (mul_nonneg hB₀ hS) (Real.rpow_nonneg hV _)
  have hW₀ : Cweak * M ≤ B := by
    calc
      _ ≤ 2 * Cweak * M := by nlinarith [mul_nonneg hCweak hM]
      _ ≤ _ := hBw
  obtain ⟨T, Tstar, hPair, hT, hEnergy⟩ := hMixed hU hQU hSmooth M hM
    (fun n hn => hJet n (hn.trans (Nat.le_max_right Ka Km))) d hd D hD hMag L
    (fun a' b' x => (hSlope a' b' x).trans_eq hL.symm) H
  have hForward : P.fullForward H = T := funext fun v =>
    inner_eq_of_schwartz fun t => (P.fullPairs H v t).1.trans (hPair v t).1.symm
  let source (v : SchwartzMap E ℂ) := (constantWave m v + schwartzDivergence d v).toLp 2 volume
  have sourceBound (p q : Index) : ‖source (projectionFullSchwartz z p q)‖ ≤ N := by
    dsimp only [source]
    rw [← projectedSourceDivergenceL2_eq_constantWave_add_schwartzDivergence A m d hA z p q]
    let f := projectedSourceDivergenceL2 A (projectionFullSchwartz z)
    exact (norm_le_pi_norm (f p) q).trans (norm_le_pi_norm f p)
  obtain ⟨hu₂, hu₄, hAll⟩ := projectedPatch_correctionLpBudget h₂ h₄ i j
  obtain ⟨hw₂, hw₄, _⟩ := projectedPatch_correctionLpBudget h₂ h₄ a b
  have hFactor : 4 * (B / 4 * (1 + e / ℓ)) = B * S := by dsimp [S]; ring
  rw [hFactor] at hu₂ hu₄ hw₂ hw₄ hAll
  have hLowBudget : ‖H.toLp 4 volume‖ ≤ B * e * V ^ ((1 : ℝ) / 4) ∧
      schwartzGradientNorm 4 H ≤ U₄ := by
    rcases hLow with h | h
    · simpa only [H, h, V, U₄] using And.intro (hAll k l).1.1 (hAll k l).2.1
    · simpa only [H, h, V, U₄] using And.intro (hAll k l).1.2 (hAll k l).2.2
  have hTu : ‖T u‖ ≤ B * ‖H.toLp 4 volume‖ * U₄ := by
    refine (hT u).1.trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_right hBo (norm_nonneg _)) hu₄
      (highDerivativeLp4Sum_nonneg _) (mul_nonneg hB₀ (norm_nonneg _))
  have hTw : ‖Tstar w‖ ≤ B * ‖H.toLp 4 volume‖ * U₄ := by
    refine (hT w).2.trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_right hBo (norm_nonneg _)) hw₄
      (highDerivativeLp4Sum_nonneg _) (mul_nonneg hB₀ (norm_nonneg _))
  refine ⟨?_, P.mixedWavePair_cutoff_recovery m H u w⟩
  change ‖Complex.I * weakConstantWaveCommutatorPair m (P.fullForward H) u w‖ ≤ _
  rw [hForward]
  rw [← ENNReal.toReal_rpow] at hSource
  refine correction_energy_le_patch_envelope ℓ e V B _ N ‖H.toLp 4 volume‖
    U₂ U₄ (schwartzGradientNorm 4 H) D L hℓ he hV hB
    (norm_nonneg _) hU₂ hU₄ ENNReal.toReal_nonneg hSource hLowBudget.1 le_rfl le_rfl
    hLowBudget.2 le_rfl hL.le ?_
  have hg (v : SchwartzMap E ℂ) (p : ℝ≥0∞) : 0 ≤ schwartzGradientNorm p v :=
    ENNReal.toReal_nonneg
  have hDH := mul_nonneg hD (hg H 4)
  have hLH : 0 ≤ (L : ℝ) * ‖H.toLp 4 volume‖ := mul_nonneg L.coe_nonneg (norm_nonneg _)
  calc
    _ ≤ _ := hEnergy m u w
    _ ≤ N * (B * ‖H.toLp 4 volume‖ * U₄) + (B * ‖H.toLp 4 volume‖ * U₄) * N +
        Cweak * M *
          (D * schwartzGradientNorm 4 H * (U₂ * U₄ + U₂ * U₄) +
            (L : ℝ) * ‖H.toLp 4 volume‖ * U₂ * U₄) := by
      have hgu : schwartzGradientNorm 4 u ≤ U₄ := (hAll i j).2.1
      have hgw : schwartzGradientNorm 4 w ≤ U₄ := (hAll a b).2.1
      have hguw := mul_le_mul hw₂ hgu (hg u 4) hU₂
      have hgwu := mul_le_mul hu₂ hgw (hg w 4) hU₂
      refine add_le_add (add_le_add
        (mul_le_mul (sourceBound a b) hTu (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul hTw (sourceBound i j) (norm_nonneg _) (by positivity))) ?_
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCweak hM)
      refine add_le_add (mul_le_mul_of_nonneg_left (add_le_add hguw hgwu) hDH) ?_
      calc
        _ = ((L : ℝ) * ‖H.toLp 4 volume‖) *
            (schwartzGradientNorm 2 w * schwartzGradientNorm 4 u) := by ring
        _ ≤ ((L : ℝ) * ‖H.toLp 4 volume‖) * (U₂ * U₄) := mul_le_mul_of_nonneg_left hguw hLH
        _ = _ := by ring
    _ = 2 * N * (B * ‖H.toLp 4 volume‖ * U₄) +
        (2 * Cweak * M) * (D * U₂ * schwartzGradientNorm 4 H * U₄) +
        (Cweak * M) * ((L : ℝ) * U₂ * ‖H.toLp 4 volume‖ * U₄) := by ring
    _ ≤ _ := by
      rw [mul_add, ← add_assoc]
      exact add_le_add
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hBw
          (mul_nonneg (mul_nonneg (mul_nonneg hD hU₂) (hg H 4)) hU₄)))
        (mul_le_mul_of_nonneg_right hW₀
          (mul_nonneg (mul_nonneg (mul_nonneg L.coe_nonneg hU₂) (norm_nonneg _)) hU₄))

end Burnett.C03
