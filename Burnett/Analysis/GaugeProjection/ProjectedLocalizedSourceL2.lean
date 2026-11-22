import Burnett.Analysis.GaugeProjection.ProjectedSchwartzIdentities
import Burnett.Analysis.GaugeProjection.LocalizedVacuumSourceBound
import Burnett.Analysis.GaugeProjection.MatrixProjectionRealization

set_option autoImplicit false
set_option maxHeartbeats 3600000

noncomputable section

namespace Burnett.P01

open MeasureTheory Set
open Burnett.A02.FrequencySplit (E)
open Burnett.A07 (coordinateDerivative)
open scoped ENNReal

/-- The actual source on the symmetrized gradient plus a remainder becomes
exactly the projection of that remainder in physical \(L^2\). -/
theorem projectionFullL2_source_eq_remainder
    (Q R : ProjectionSchwartzMatrix) (V : Fin 4 → SchwartzMap E ℂ)
    (hQ : ∀ a b x, Q a b x = coordinateDerivative a (V b) x +
      coordinateDerivative b (V a) x + R a b x) :
    projectionFullL2 (projectionMatrixToL2 Q) =
      projectionFullL2 (projectionMatrixToL2 R) := by
  let S : ProjectionSchwartzMatrix := fun a b =>
    coordinateDerivative a (V b) + coordinateDerivative b (V a)
  have h : Q = S + R := by
    funext a b
    ext x
    exact hQ a b x
  rw [projectionFullL2_eq_schwartz, projectionFullL2_eq_schwartz, h,
    projectionFullSchwartz_add]
  have hz : projectionFullSchwartz S = 0 := projectionFullSchwartz_symmetrizedGradient_eq_zero V
  rw [hz, zero_add]

/-- A common compactly supported majorant yields a uniform physical \(L^2\)
bound for the projected exact wave source. The coefficient-dependent
symmetrized gradient is removed before taking the norm. -/
theorem norm_projectionFullL2_localized_source_le
    (Q R : ProjectionSchwartzMatrix) (V : Fin 4 → SchwartzMap E ℂ)
    (hQ : ∀ a b x, Q a b x = coordinateDerivative a (V b) x +
      coordinateDerivative b (V a) x + R a b x)
    (K : Set E) (hK : IsCompact K) (C : ℝ)
    (hR : ∀ a b x, ‖R a b x‖ ≤ K.indicator (fun _ => C) x) :
    ‖projectionFullL2 (projectionMatrixToL2 Q)‖ ≤
      ‖projectionFullL2‖ * (eLpNorm (K.indicator (fun _ => C)) 2 volume).toReal := by
  let F := K.indicator (fun _ => C)
  have hF : MemLp F 2 (volume : Measure E) :=
    memLp_indicator_const 2 hK.isClosed.measurableSet C (Or.inr hK.measure_lt_top.ne)
  have hn : ‖projectionMatrixToL2 R‖ ≤ (eLpNorm F 2 volume).toReal := by
    apply (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).2
    intro a
    apply (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).2
    intro b
    change ‖(R a b).toLp 2 volume‖ ≤ _
    rw [SchwartzMap.toLp, Lp.norm_toLp]
    exact ENNReal.toReal_mono hF.2.ne (eLpNorm_mono_real (hR a b))
  rw [projectionFullL2_source_eq_remainder Q R V hQ]
  exact (projectionFullL2.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left hn (norm_nonneg _))

end Burnett.P01
