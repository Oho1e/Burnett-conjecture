import Burnett.Analysis.TransportPatches.ActualThinConeLp
import Burnett.Analysis.TransportPatches.WideGradientVectorL3
import Burnett.Analysis.GaugeProjection.ProjectedSchwartzIdentities

/-! Upgrade the exact complement using the C03 bound of the same projected gradient. -/
set_option autoImplicit false
set_option maxRecDepth 5100
set_option maxHeartbeats 6900000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix projectionFullSchwartz projectionMatrixDerivative
  projectionFullSchwartz_coordinateDerivative)
open Burnett.C03 (ProjectedPatchLpBounds)
open scoped ENNReal Topology

open private actualThinConeComplement_gradient_eq from Burnett.Analysis.TransportPatches.ActualThinConeLp
open private finiteLp_eLpNorm_eq eLpNorm'_two_eq_norm from Burnett.Analysis.TransportPatches.WidePatchErrorInterpolation

/-- The actual complement has all its L³ rows strongly zero. The finite-p
input is exactly the first derivative of the original C03 projection. -/
theorem thinComplement_strong3_of_projectedPatchLp (p : ℝ) (hp : 3 < p)
    (m : Tensor2) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (M : ℝ) (hM : 0 ≤ M)
    (hScalar : ∀ (f : ComplexL2 E), MemLp (f : E → ℂ) (ENNReal.ofReal p) volume →
      let F := fourierMultiplier (thinComplementScalar m hη i o) f
      MemLp (F : E → ℂ) (ENNReal.ofReal p) volume ∧
      (eLpNorm (F : E → ℂ) (ENNReal.ofReal p) volume).toReal ≤
        M * (eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume).toReal)
    (z : ℕ → ProjectionSchwartzMatrix) (P : Set E) (Cp : ℝ) (val : ℕ → ℝ)
    (hPatch : ∀ᶠ n in atTop, ProjectedPatchLpBounds p (z n) P (val n) Cp) :
    let T := actualThinConeComplementMultiplier m hη i o
    let f (n : ℕ) (a : Index × OrderedPair) := multiplierCoordinateDerivative T (z n) a.1 a.2
    Tendsto (fun n => WithLp.toLp 2 (f n)) atTop (𝓝 0) →
    (∀ n a, MemLp (f n a : E → ℂ) 3 volume) ∧
      ∀ a : Index × OrderedPair,
        Tendsto (fun n => (eLpNorm' (f n a : E → ℂ) 3 volume).toReal) atTop (𝓝 0) := by
  intro T f hL2
  have hp₀ : 0 < p := by linarith
  let Pp := ENNReal.ofReal p
  let endP := Cp * ((volume : Measure E) P ^ (1 / p)).toReal
  let u (n : ℕ) (a : Index × OrderedPair) := projectionMatrixDerivative a.1 (projectionFullSchwartz (z n)) a.2.1 a.2.2
  have hAction (n : ℕ) (a : Index × OrderedPair) :
      f n a = fourierMultiplier (thinComplementScalar m hη i o) ((u n a).toLp 2 volume) := by
    change multiplierCoordinateDerivative T (z n) a.1 a.2 = _
    rw [actualThinConeComplement_gradient_eq, projectionFullSchwartz_coordinateDerivative]
  have hP (n : ℕ) (a : Index × OrderedPair) : MemLp (f n a : E → ℂ) Pp volume ∧
      (eLpNorm (f n a : E → ℂ) Pp volume).toReal ≤ M * (eLpNorm (u n a : E → ℂ) Pp volume).toReal := by
    let w := (u n a).toLp 2 volume
    have hEq : (w : E → ℂ) =ᵐ[volume] (u n a : E → ℂ) := (u n a).coeFn_toLp 2 volume
    have hMem : MemLp (w : E → ℂ) Pp volume := (memLp_congr_ae hEq).2 ((u n a).memLp Pp volume)
    have h := hScalar w hMem
    change MemLp (fourierMultiplier (thinComplementScalar m hη i o) w : E → ℂ) Pp volume ∧ _ at h
    rw [eLpNorm_congr_ae hEq] at h
    rw [hAction]
    exact h
  refine ⟨fun n a => memLp_three_of_complexL2_and_finiteP p hp _ (hP n a).1, ?_⟩
  intro a
  have h₂ : Tendsto (fun n => f n a) atTop (𝓝 0) := by
    have hEval := (PiLp.continuous_apply (p := 2) (β := fun _ : Index × OrderedPair => ComplexL2 E) a).tendsto 0
    simpa only [PiLp.toLp_apply, PiLp.zero_apply, Function.comp_def] using hEval.comp hL2
  have hFin₂ (n : ℕ) : eLpNorm' (f n a : E → ℂ) 2 volume < ⊤ := by
    rw [← finiteLp_eLpNorm_eq 2 (by norm_num), show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact Lp.eLpNorm_lt_top _
  have hFinₚ (n : ℕ) : eLpNorm' (f n a : E → ℂ) p volume < ⊤ := by
    rw [← finiteLp_eLpNorm_eq p hp₀]
    exact (hP n a).1.eLpNorm_lt_top
  have hNorm₂ : Tendsto (fun n => (eLpNorm' (f n a : E → ℂ) 2 volume).toReal) atTop (𝓝 0) := by
    simp only [eLpNorm'_two_eq_norm]
    simpa only [Function.comp_def, norm_zero] using (continuous_norm.tendsto (0 : ComplexL2 E)).comp h₂
  refine frozenError_strong3_of_strong2 hp (fun n => (f n a : E → ℂ))
    (fun n => Lp.aestronglyMeasurable _) hFin₂ hFinₚ hNorm₂ (M * endP) ?_
  intro ε hε
  filter_upwards [hPatch] with n hn
  have hC03 : (eLpNorm (u n a : E → ℂ) Pp volume).toReal ≤ endP := ((hn a.2.1 a.2.2).2 a.1).1
  rw [← finiteLp_eLpNorm_eq p hp₀]
  exact ((hP n a).2.trans (mul_le_mul_of_nonneg_left hC03 hM)).trans (le_add_of_nonneg_right hε.le)

end Burnett.C02
