import Burnett.Analysis.GaugeProjection.ProjectedDefectActualComponents
import Burnett.Analysis.GaugeProjection.ProjectedSchwartzIdentities
import Burnett.Analysis.Microlocal.PhysicalDensity

/-! The fixed infrared regularization changes the homogeneous projected derivative by a strongly vanishing term. -/
set_option autoImplicit false
set_option maxRecDepth 3800
set_option maxHeartbeats 4100000

noncomputable section
namespace Burnett.P01

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.A02.FrequencySplit (E tau radianFourier_scaled)
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative)
open Burnett.Microlocal.AngularCommutator (symbolDifference fourierMultiplier_symbolDifference)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped BigOperators FourierTransform Topology

open private regularizedProjectionComponentSymbol_eq_off_ball
  from Burnett.Analysis.GaugeProjection.ProjectedDefectActualComponents

private theorem tau_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

/-- A multiplier supported in a fixed frequency ball, acting on an actual
coordinate derivative, is bounded by the undifferentiated (L^2) norm. -/
theorem norm_fourierMultiplier_coordinateDerivative_le_of_frequency_ball
    (m : BoundedSymbol E) (R : ℝ) (hR : 0 ≤ R)
    (hm : ∀ ξ, ξ ∉ Metric.closedBall (0 : E) R → m ξ = 0)
    (d : Fin 4) (z : SchwartzMap E ℂ) :
    ‖fourierMultiplier m ((coordinateDerivative d z).toLp 2 volume)‖ ≤
      m.bound * (tau * R) * ‖z.toLp 2 volume‖ := by
  rw [fourierMultiplier_apply, LinearIsometryEquiv.norm_map,
    ← (fourierL2Equiv (V := E)).norm_map (z.toLp 2 volume)]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [symbolL2_ae m (fourierL2Equiv ((coordinateDerivative d z).toLp 2 volume)),
    fourierL2Equiv_schwartz_ae (coordinateDerivative d z), fourierL2Equiv_schwartz_ae z] with ξ hM hD hZ
  rw [hM, hD, hZ]
  have hd := radianFourier_coordinateDerivative d z (tau • ξ)
  simp only [radianFourier_scaled] at hd
  change ‖m ξ * 𝓕 (coordinateDerivative d z : E → ℂ) ξ‖ ≤ m.bound * (tau * R) * ‖𝓕 (z : E → ℂ) ξ‖
  rw [hd]
  by_cases hξ : ξ ∈ Metric.closedBall (0 : E) R
  · have hCoord : ‖ξ d‖ ≤ R := (PiLp.norm_apply_le ξ d).trans (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hξ)
    have hFreq : ‖(tau • ξ) d‖ ≤ tau * R := by
      change ‖tau * ξ d‖ ≤ tau * R
      rw [norm_mul, Real.norm_of_nonneg tau_pos.le]
      exact mul_le_mul_of_nonneg_left hCoord tau_pos.le
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    rw [← mul_assoc ‖m ξ‖]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (m.norm_le ξ) hFreq
      (norm_nonneg ((tau • ξ) d)) m.bound_nonneg) (norm_nonneg (𝓕 (z : E → ℂ) ξ))
  · rw [hm ξ hξ, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg m.bound_nonneg (mul_nonneg tau_pos.le hR)) (norm_nonneg _)

/-- The homogeneous Fourier projection used in the paper's strong criterion,
on the actual (L^2) derivatives of its compactly supported input. -/
def homogeneousProjectedCoordinateDerivative (w : ProjectionSchwartzMatrix) (d : Fin 4)
    (k : OrderedPair) : ComplexL2 E :=
  ∑ i : OrderedPair, fourierMultiplier (principalProjectionComponentSymbol k.1 k.2 i.1 i.2)
    ((coordinateDerivative d (w i.1 i.2)).toLp 2 volume)

theorem homogeneousProjectedCoordinateDerivative_sub_regularized_tendsto_zero
    (w : ℕ → ProjectionSchwartzMatrix)
    (h : ∀ i j, Tendsto (fun n => (w n i j).toLp 2 volume) atTop (𝓝 0))
    (d : Fin 4) (k : OrderedPair) :
    Tendsto (fun n => homogeneousProjectedCoordinateDerivative (w n) d k -
      (coordinateDerivative d (projectionFullSchwartz (w n) k.1 k.2)).toLp 2 volume) atTop (𝓝 0) := by
  let D (i : OrderedPair) := symbolDifference (principalProjectionComponentSymbol k.1 k.2 i.1 i.2)
    (regularizedProjectionComponentSymbol k.1 k.2 i.1 i.2)
  let R : ℝ := 2 / tau
  have hR : 0 ≤ R := div_nonneg (by norm_num) tau_pos.le
  have hD (i : OrderedPair) (ξ : E) (hξ : ξ ∉ Metric.closedBall (0 : E) R) : D i ξ = 0 := by
    change principalProjectionComponentSymbol k.1 k.2 i.1 i.2 ξ -
      regularizedProjectionComponentSymbol k.1 k.2 i.1 i.2 ξ = 0
    rw [regularizedProjectionComponentSymbol_eq_off_ball _ _ _ _ _ hξ, sub_self]
  have he (i : OrderedPair) : Tendsto (fun n => fourierMultiplier (D i)
      ((coordinateDerivative d (w n i.1 i.2)).toLp 2 volume)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn := (h i.1 i.2).norm.const_mul ((D i).bound * (tau * R))
    simp only [norm_zero, mul_zero] at hn
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n =>
      norm_fourierMultiplier_coordinateDerivative_le_of_frequency_ball (D i) R hR (hD i) d (w n i.1 i.2)) hn
  have hSum := tendsto_finset_sum (Finset.univ : Finset OrderedPair) (fun i _ => he i)
  simp only [Finset.sum_const_zero] at hSum
  refine hSum.congr (fun n => ?_)
  have hProj : (coordinateDerivative d (projectionFullSchwartz (w n) k.1 k.2)).toLp 2 volume =
      ∑ i : OrderedPair, fourierMultiplier (regularizedProjectionComponentSymbol k.1 k.2 i.1 i.2)
        ((coordinateDerivative d (w n i.1 i.2)).toLp 2 volume) := by
    have hComm := congrFun (congrFun (projectionFullSchwartz_coordinateDerivative d (w n)) k.1) k.2
    change projectionFullSchwartz (fun i j => coordinateDerivative d (w n i j)) k.1 k.2 =
      coordinateDerivative d (projectionFullSchwartz (w n) k.1 k.2) at hComm
    rw [← hComm]
    change schwartzLpMap (projectionFullSchwartz (fun i j => coordinateDerivative d (w n i j)) k.1 k.2) = _
    simp only [projectionFullSchwartz, map_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      gaugeProjectionComponent_toLp_eq_multiplier k.1 k.2 i j (coordinateDerivative d (w n i j))))
  rw [hProj, homogeneousProjectedCoordinateDerivative, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => fourierMultiplier_symbolDifference _ _ _)

end Burnett.P01
