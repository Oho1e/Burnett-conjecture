import Burnett.Analysis.GaugeProjection.ProjectedFiniteLp

set_option autoImplicit false
set_option maxRecDepth 4400
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.C03

open Set MeasureTheory Burnett.P01 Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.A02.FrequencySplit (E radianFourier)
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative
  exists_fixedInfraredSchwartz_Lp_bound)
open scoped ENNReal BigOperators

open private radianEval radianFourierSchwartz_injective from
  Burnett.Analysis.GaugeProjection.ProjectedSchwartzIdentities
open private entry_eLpNorm_le_projectionMatrixLpNorm from
  Burnett.Analysis.GaugeProjection.ProjectedFiniteLp

/-- The actual complementary high-pass gauge field on the same original input. -/
def projectedGaugeComplement (z : ProjectionSchwartzMatrix) : ProjectionSchwartzMatrix :=
  fun i j => projectionInfraredAction (z i j) - projectionFullSchwartz z i j

theorem projectedGaugeComplement_radianFourier
    (z : ProjectionSchwartzMatrix) (i j : Index) (ξ : E) :
    radianFourier (projectedGaugeComplement z i j) ξ =
      (gaugeProjectionInfrared ‖ξ‖ : ℂ) *
        (radianFourier (z i j) ξ -
          ∑ a : Index, ∑ b : Index,
            (gaugeProjectionSymbol i j a b ξ : ℂ) * radianFourier (z a b) ξ) := by
  change radianEval ξ (projectionInfraredAction (z i j) - projectionFullSchwartz z i j) = _
  rw [map_sub]
  change radianFourier (projectionInfraredAction (z i j)) ξ -
    radianFourier (projectionFullSchwartz z i j) ξ = _
  rw [radianFourier_projectionInfraredAction, projectionFullSchwartz_radianFourier,
    regularizedComplexGaugeProjection_apply]
  simp only [regularizedGaugeProjectionSymbol, Complex.ofReal_mul, mul_sub, Finset.mul_sum, mul_assoc]

private theorem coordinateDerivative_projectionInfraredAction (a : Index) (f : SchwartzMap E ℂ) :
    coordinateDerivative a (projectionInfraredAction f) =
      projectionInfraredAction (coordinateDerivative a f) := by
  apply radianFourierSchwartz_injective
  funext ξ
  change radianFourier (coordinateDerivative a (projectionInfraredAction f)) ξ =
    radianFourier (projectionInfraredAction (coordinateDerivative a f)) ξ
  rw [radianFourier_coordinateDerivative, radianFourier_projectionInfraredAction,
    radianFourier_projectionInfraredAction, radianFourier_coordinateDerivative]
  ring

theorem projectionMatrixDerivative_projectedGaugeComplement
    (a : Index) (z : ProjectionSchwartzMatrix) :
    projectionMatrixDerivative a (projectedGaugeComplement z) =
      projectedGaugeComplement (projectionMatrixDerivative a z) := by
  funext i j
  change coordinateDerivative a (projectionInfraredAction (z i j) - projectionFullSchwartz z i j) = _
  rw [show coordinateDerivative a (projectionInfraredAction (z i j) - projectionFullSchwartz z i j) =
      coordinateDerivative a (projectionInfraredAction (z i j)) -
        coordinateDerivative a (projectionFullSchwartz z i j) from
    (SchwartzMap.pderivCLM ℂ (EuclideanSpace.single a (1 : ℝ))).map_sub _ _,
    coordinateDerivative_projectionInfraredAction]
  change projectionInfraredAction (coordinateDerivative a (z i j)) -
    projectionMatrixDerivative a (projectionFullSchwartz z) i j = _
  rw [← projectionFullSchwartz_coordinateDerivative]
  rfl

/-- A common finite-exponent bound for each actual physical and gauge
entry and their coordinate derivatives. The operator preserves projection tails. -/
theorem exists_projectionPhysicalGauge_entryLp_bounds (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ z : ProjectionSchwartzMatrix, ∀ i j : Index,
        (eLpNorm (projectionFullSchwartz z i j : E → ℂ) (ENNReal.ofReal p) volume ≤
          C * projectionMatrixLpNorm p z ∧
        eLpNorm (projectedGaugeComplement z i j : E → ℂ) (ENNReal.ofReal p) volume ≤
          C * projectionMatrixLpNorm p z) ∧
        ∀ a : Index,
          eLpNorm (projectionMatrixDerivative a (projectionFullSchwartz z) i j : E → ℂ)
            (ENNReal.ofReal p) volume ≤ C * projectionMatrixLpNorm p (projectionMatrixDerivative a z) ∧
          eLpNorm (projectionMatrixDerivative a (projectedGaugeComplement z) i j : E → ℂ)
            (ENNReal.ofReal p) volume ≤ C * projectionMatrixLpNorm p (projectionMatrixDerivative a z) := by
  obtain ⟨H, hH, hHigh⟩ := exists_fixedInfraredSchwartz_Lp_bound gaugeProjectionInfrared
    gaugeProjectionInfrared_contDiff 1 2 zero_lt_one
    (fun _ hs => gaugeProjectionInfrared_zero hs) (fun _ hs => gaugeProjectionInfrared_one hs) p hp
  obtain ⟨P, hP, hPhysical⟩ := exists_projectionFullSchwartz_finiteLp_bounds p hp
  have hp₁ : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hPair (z : ProjectionSchwartzMatrix) (i j : Index) :
      eLpNorm (projectionFullSchwartz z i j : E → ℂ) (ENNReal.ofReal p) volume ≤
        (H + P) * projectionMatrixLpNorm p z ∧
      eLpNorm (projectedGaugeComplement z i j : E → ℂ) (ENNReal.ofReal p) volume ≤
        (H + P) * projectionMatrixLpNorm p z := by
    have hPhys := (entry_eLpNorm_le_projectionMatrixLpNorm p (projectionFullSchwartz z) i j).trans
      (hPhysical z).1
    have hHi := (hHigh (z i j)).trans <|
      mul_le_mul_left' (entry_eLpNorm_le_projectionMatrixLpNorm p z i j) H
    refine ⟨hPhys.trans (mul_le_mul_right' (le_add_of_nonneg_left bot_le) _), ?_⟩
    change eLpNorm ((projectionInfraredAction (z i j) : E → ℂ) -
      (projectionFullSchwartz z i j : E → ℂ)) (ENNReal.ofReal p) volume ≤ _
    calc
      _ ≤ _ := eLpNorm_sub_le (projectionInfraredAction (z i j)).continuous.aestronglyMeasurable
        (projectionFullSchwartz z i j).continuous.aestronglyMeasurable hp₁
      _ ≤ H * projectionMatrixLpNorm p z + P * projectionMatrixLpNorm p z := add_le_add hHi hPhys
      _ = _ := by rw [add_mul]
  refine ⟨H + P, ENNReal.add_lt_top.mpr ⟨hH, hP⟩, fun z i j => ⟨hPair z i j, ?_⟩⟩
  intro a
  rw [← projectionFullSchwartz_coordinateDerivative, projectionMatrixDerivative_projectedGaugeComplement]
  exact hPair (projectionMatrixDerivative a z) i j

end Burnett.C03
