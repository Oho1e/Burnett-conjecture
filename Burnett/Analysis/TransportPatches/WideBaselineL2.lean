import Burnett.Analysis.TransportPatches.ActualWideInfraredMultipliers
import Burnett.Analysis.GaugeProjection.ProjectedFiniteLp

/-! The patch-volume bound for the original projected gradient in the exact Hilbert norm. -/

set_option autoImplicit false
set_option maxRecDepth 5200
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix projectionMatrixLpNorm projectionMatrixDerivative projectionFullSchwartz
  gaugeProjectionComponent_toLp_eq_multiplier exists_projectionFullSchwartz_finiteLp_bounds)
open scoped BigOperators ENNReal Topology

open private entry_eLpNorm_le_projectionMatrixLpNorm from Burnett.Analysis.GaugeProjection.ProjectedFiniteLp

/-- The ordered projected L² field agrees with the original Schwartz
realization of the fixed regularized gauge projector. -/
theorem originalProjectedMatrixMultiplier_output_eq_schwartz
    (z : ProjectionSchwartzMatrix) (k : OrderedPair) :
    originalProjectedMatrixMultiplier.output (fun i => (z i.1 i.2).toLp 2 volume) k =
      (projectionFullSchwartz z k.1 k.2).toLp 2 volume := by
  rw [originalProjectedMatrixMultiplier_output]
  symm
  change schwartzLpMap (projectionFullSchwartz z k.1 k.2) = _
  simp only [projectionFullSchwartz, map_sum, originalOrderedProjectedField, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact gaugeProjectionComponent_toLp_eq_multiplier k.1 k.2 a b (z a b)

/-- This applies to the original coordinate derivative before any screen
or phase multiplier is used. -/
theorem originalProjectedMatrixMultiplier_derivative_eq_schwartz
    (z : ProjectionSchwartzMatrix) (d : Index) (k : OrderedPair) :
    multiplierCoordinateDerivative originalProjectedMatrixMultiplier z d k =
      (projectionFullSchwartz (projectionMatrixDerivative d z) k.1 k.2).toLp 2 volume :=
  originalProjectedMatrixMultiplier_output_eq_schwartz (projectionMatrixDerivative d z) k

theorem exists_originalProjectedMatrixMultiplier_L2_volume :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (z : ℕ → ProjectionSchwartzMatrix) (P : Set E) (C : ℝ), IsCompact P → 0 ≤ C →
      (∀ᶠ n in atTop, ∀ b : Index, projectionMatrixLpNorm 2 (projectionMatrixDerivative b (z n)) ≤
        ENNReal.ofReal C * (volume : Measure E) P ^ (1 / 2 : ℝ)) →
      ∀ᶠ n in atTop, ‖WithLp.toLp 2 (fun a : Index × OrderedPair =>
        multiplierCoordinateDerivative originalProjectedMatrixMultiplier (z n) a.1 a.2)‖ ≤
        D * C * ((volume : Measure E) P).toReal ^ (1 / 2 : ℝ) := by
  obtain ⟨A, hA, hProj⟩ := exists_projectionFullSchwartz_finiteLp_bounds 2 (by norm_num)
  refine ⟨8 * A.toReal, mul_nonneg (by norm_num) ENNReal.toReal_nonneg, ?_⟩
  intro z P C hP hC hRaw
  let vol := (volume : Measure E) P
  have hPow : vol ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hP.measure_lt_top.ne
  let V := A.toReal * C * vol.toReal ^ (1 / 2 : ℝ)
  have hV : 0 ≤ V := mul_nonneg (mul_nonneg ENNReal.toReal_nonneg hC) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  filter_upwards [hRaw] with n hn
  have hComponent (b : Index) (k : OrderedPair) :
      ‖multiplierCoordinateDerivative originalProjectedMatrixMultiplier (z n) b k‖ ≤ V := by
    let v := projectionMatrixDerivative b (z n)
    let f := projectionFullSchwartz v k.1 k.2
    have h0 : eLpNorm (f : E → ℂ) (ENNReal.ofReal 2) volume ≤
        A * (ENNReal.ofReal C * vol ^ (1 / 2 : ℝ)) :=
      (entry_eLpNorm_le_projectionMatrixLpNorm 2 (projectionFullSchwartz v) k.1 k.2).trans
        (((hProj v).1).trans (mul_le_mul_left' (hn b) A))
    have hTop : A * (ENNReal.ofReal C * vol ^ (1 / 2 : ℝ)) ≠ ⊤ :=
      (ENNReal.mul_lt_top hA (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hPow)).ne
    have h := ENNReal.toReal_mono hTop h0
    rw [originalProjectedMatrixMultiplier_derivative_eq_schwartz, Lp.norm_def, eLpNorm_congr_ae (f.coeFn_toLp 2 volume)]
    simpa only [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hC, V, mul_assoc] using h
  change _ ≤ 8 * A.toReal * C * vol.toReal ^ (1 / 2 : ℝ)
  rw [show 8 * A.toReal * C * vol.toReal ^ (1 / 2 : ℝ) = 8 * V by dsimp only [V]; ring]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hV)).1
  rw [multiplierCoordinateDerivative_norm_sq]
  calc
    _ ≤ ∑ _b : Index, ∑ _k : OrderedPair, V^2 := Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun k _ =>
      (sq_le_sq₀ (norm_nonneg _) hV).2 (hComponent b k)))
    _ = (8 * V)^2 := by
      change (∑ _b : Fin 4, ∑ _k : Fin 4 × Fin 4, V^2) = _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

end Burnett.C02
