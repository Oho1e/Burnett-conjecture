import Burnett.Analysis.GaugeProjection.HodgePhysicalAction
import Burnett.Analysis.GaugeProjection.ProjectedSchwartzIdentities
import Burnett.Analysis.GaugeProjection.InfraredConvolution

set_option autoImplicit false
set_option maxHeartbeats 2900000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter
open Burnett.A02.FrequencySplit
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative)
open Burnett.Fourier
open scoped BigOperators FourierTransform ContDiff

abbrev HodgeL2Field := Fin 4 → ComplexL2 E
abbrev ProjectionL2Matrix := Fin 4 → HodgeL2Field

/-- Evaluation in the two fixed matrix coordinates. -/
def projectionL2Entry (i j : Fin 4) : ProjectionL2Matrix →L[ℂ] ComplexL2 E :=
  (ContinuousLinearMap.proj j : HodgeL2Field →L[ℂ] ComplexL2 E).comp
    (ContinuousLinearMap.proj i : ProjectionL2Matrix →L[ℂ] HodgeL2Field)

@[simp] theorem projectionL2Entry_apply (i j : Fin 4) (w : ProjectionL2Matrix) :
    projectionL2Entry i j w = w i j := rfl

def projectionMatrixToL2 (w : ProjectionSchwartzMatrix) : ProjectionL2Matrix :=
  fun i j => (w i j).toLp 2 volume

private def hodgeEntryL2Symbol (i j : Fin 4) : BoundedSymbol E :=
  Classical.choose (mikhlin_bounded_symbol (directionProjectionEntry i j)
    (directionProjectionEntry_contDiffOn i j) (directionProjectionEntry_scale i j))

private theorem hodgeEntryL2Symbol_eq (i j : Fin 4) (ξ : E) :
    hodgeEntryL2Symbol i j ξ = (directionProjectionEntry i j ξ : ℂ) :=
  Classical.choose_spec (mikhlin_bounded_symbol (directionProjectionEntry i j)
    (directionProjectionEntry_contDiffOn i j) (directionProjectionEntry_scale i j)) ξ

def hodgeVectorL2Action : HodgeL2Field →L[ℂ] HodgeL2Field :=
  ContinuousLinearMap.pi fun i =>
    ∑ j, (fourierMultiplier (hodgeEntryL2Symbol i j)).comp (ContinuousLinearMap.proj j)

theorem hodgeVectorL2Action_apply (w : HodgeL2Field) (i : Fin 4) :
    hodgeVectorL2Action w i = ∑ j, fourierMultiplier (hodgeEntryL2Symbol i j) (w j) := by
  simp only [hodgeVectorL2Action, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

private theorem lp_fin_sum_ae (u : Fin 4 → ComplexL2 E) :
    ((∑ j, u j : ComplexL2 E) : E → ℂ) =ᵐ[volume] fun x => ∑ j, u j x := by
  classical
  generalize (Finset.univ : Finset (Fin 4)) = s
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using (Lp.coeFn_zero ℂ 2 (volume : Measure E))
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (u j) (∑ k ∈ s, u k), ih] with x hx hs
    simp only [Pi.add_apply] at hx
    rw [hx, hs]

theorem hodgeVectorL2Action_schwartz_ae (w : HodgeSchwartzField) (i : Fin 4) :
    (hodgeVectorL2Action (fun j => (w j).toLp 2 volume) i : E → ℂ) =ᵐ[volume]
      hodgeTransverseAction w i := by
  let u (j : Fin 4) := fourierMultiplier (hodgeEntryL2Symbol i j) ((w j).toLp 2 volume)
  have hu (j : Fin 4) : (u j : E → ℂ) =ᵐ[volume] radianAction (directionProjectionEntry i j) (w j) :=
    mikhlin_action_test _ _ (hodgeEntryL2Symbol_eq i j) (directionProjectionEntry_scale i j) (w j)
  rw [hodgeVectorL2Action_apply]
  filter_upwards [lp_fin_sum_ae u, ae_all_iff.mpr hu] with x hx hy
  exact hx.trans (Finset.sum_congr rfl fun j _ => hy j)

theorem hodgeVectorL2Action_schwartz_eq (w A : HodgeSchwartzField)
    (hA : ∀ ξ, hodgeSpectrum A ξ = hodgeTransverse ξ (hodgeSpectrum w ξ)) (i : Fin 4) :
    hodgeVectorL2Action (fun j => (w j).toLp 2 volume) i = (A i).toLp 2 volume := by
  apply Lp.ext
  have h := hodgeVectorL2Action_schwartz_ae w i
  rw [hodgeTransverseAction_eq_of_spectrum w A hA i] at h
  exact h.trans ((A i).coeFn_toLp 2 volume).symm

private theorem tau_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

theorem hodgeVectorL2Action_fourier (w : HodgeL2Field) (i : Fin 4) :
    (fourierL2Equiv (hodgeVectorL2Action w i) : E → ℂ) =ᵐ[volume] fun ν =>
      ∑ j, (directionProjectionEntry i j (tau • ν) : ℂ) * fourierL2Equiv (w j) ν := by
  let v (j : Fin 4) := symbolL2 (hodgeEntryL2Symbol i j) (fourierL2Equiv (w j))
  have hv := ae_all_iff.mpr fun j : Fin 4 => symbolL2_ae (hodgeEntryL2Symbol i j) (fourierL2Equiv (w j))
  simp only [hodgeVectorL2Action_apply, map_sum, fourier_fourierMultiplier]
  filter_upwards [lp_fin_sum_ae v, hv] with ν hν h
  refine hν.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [h j, hodgeEntryL2Symbol_eq, directionProjectionEntry_scale i j tau tau_pos]

/-- The two coordinate slots of the same Euclidean matrix projection. -/
def projectionRightL2 : ProjectionL2Matrix →L[ℂ] ProjectionL2Matrix :=
  ContinuousLinearMap.pi fun i => hodgeVectorL2Action.comp (ContinuousLinearMap.proj i)

def projectionLeftL2 : ProjectionL2Matrix →L[ℂ] ProjectionL2Matrix :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    ∑ k, (fourierMultiplier (hodgeEntryL2Symbol i k)).comp (projectionL2Entry k j)

theorem projectionRightL2_apply (w : ProjectionL2Matrix) (i j : Fin 4) :
    projectionRightL2 w i j = hodgeVectorL2Action (w i) j := rfl

theorem projectionLeftL2_apply (w : ProjectionL2Matrix) (i j : Fin 4) :
    projectionLeftL2 w i j = hodgeVectorL2Action (fun k => w k j) i := by
  simp only [projectionLeftL2, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, projectionL2Entry_apply, hodgeVectorL2Action_apply]

private def projectionInfraredL2Symbol : BoundedSymbol E :=
  { toFun := fun ν => (gaugeProjectionInfrared ‖tau • ν‖ : ℂ)
    measurable := by
      apply Continuous.aestronglyMeasurable
      exact Complex.continuous_ofReal.comp (gaugeProjectionInfrared_contDiff.continuous.comp
        (continuous_const.smul continuous_id).norm)
    bound := 1
    bound_nonneg := zero_le_one
    norm_le := fun ν => by
      rw [Complex.norm_real, Real.norm_of_nonneg]
      · exact Real.smoothTransition.le_one _
      · exact Real.smoothTransition.nonneg _ }

def projectionInfraredL2Scalar : ComplexL2 E →L[ℂ] ComplexL2 E :=
  fourierMultiplier projectionInfraredL2Symbol

def projectionInfraredL2 : ProjectionL2Matrix →L[ℂ] ProjectionL2Matrix :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    projectionInfraredL2Scalar.comp (projectionL2Entry i j)

theorem projectionInfraredL2_apply (w : ProjectionL2Matrix) (i j : Fin 4) :
    projectionInfraredL2 w i j = projectionInfraredL2Scalar (w i j) := rfl

theorem projectionInfraredL2Scalar_schwartz (w : SchwartzMap E ℂ) :
    projectionInfraredL2Scalar (w.toLp 2 volume) = (projectionInfraredAction w).toLp 2 volume := by
  apply fourierL2Equiv.injective
  unfold projectionInfraredL2Scalar
  rw [fourier_fourierMultiplier]
  apply Lp.ext
  filter_upwards [symbolL2_ae projectionInfraredL2Symbol (fourierL2Equiv (w.toLp 2 volume)),
    fourierL2Equiv_schwartz_ae w, fourierL2Equiv_schwartz_ae (projectionInfraredAction w)] with ν ha hf hg
  rw [ha, hf, hg, ← radianFourier_scaled, ← radianFourier_scaled,
    radianFourier_projectionInfraredAction]
  rfl

theorem projectionInfraredL2Scalar_fourier (w : ComplexL2 E) :
    (fourierL2Equiv (projectionInfraredL2Scalar w) : E → ℂ) =ᵐ[volume]
      fun ν => (gaugeProjectionInfrared ‖tau • ν‖ : ℂ) * fourierL2Equiv w ν := by
  unfold projectionInfraredL2Scalar
  rw [fourier_fourierMultiplier]
  exact symbolL2_ae _ _

end Burnett.P01
