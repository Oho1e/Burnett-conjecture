import Burnett.Analysis.GaugeProjection.MatrixProjectionSlots

set_option autoImplicit false
set_option maxHeartbeats 2700000

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter
open Burnett.Fourier
open Burnett.A02.FrequencySplit
open Burnett.A07 (coordinateDerivative)
open scoped BigOperators FourierTransform

/-- The actual full matrix multiplier, factored into the two Hodge slots and the
original fixed infrared factor, on the complete physical \(L^2\) space. -/
def projectionFullL2 : ProjectionL2Matrix →L[ℂ] ProjectionL2Matrix :=
  projectionInfraredL2.comp (projectionLeftL2.comp projectionRightL2)

private theorem directionProjectionEntry_swap (i j : Fin 4) (ξ : E) :
    directionProjectionEntry i j ξ = directionProjectionEntry j i ξ := by
  have h := congrArg (fun P : Components => P j i)
    (directionProjection_transpose (fun k => ξ k))
  exact h

private theorem projectionFullSchwartz_fourier (w : ProjectionSchwartzMatrix) (i j : Fin 4) (ν : E) :
    𝓕 (projectionFullSchwartz w i j : E → ℂ) ν =
      ∑ a, ∑ b, (regularizedGaugeProjectionSymbol i j a b (tau • ν) : ℂ) * 𝓕 (w a b : E → ℂ) ν := by
  let e : SchwartzMap E ℂ →+ ℂ :=
    { toFun := fun v => (SchwartzMap.fourierTransformCLM ℂ v) ν
      map_zero' := by simp only [map_zero, SchwartzMap.zero_apply]
      map_add' := fun _ _ => by simp only [map_add, SchwartzMap.add_apply] }
  change e (∑ a, ∑ b, gaugeProjectionSchwartzComponent i j a b (w a b)) = _
  simp_rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change 𝓕 (gaugeProjectionSchwartzComponent i j a b (w a b) : E → ℂ) ν = _
  rw [← radianFourier_scaled, gaugeProjectionSchwartzComponent_radianFourier, radianFourier_scaled]

/-- The two-slot factorization on actual \(L^2\) agrees with the original
Schwartz projection with its four scalar indices. -/
theorem projectionFullL2_eq_schwartz (w : ProjectionSchwartzMatrix) :
    projectionFullL2 (projectionMatrixToL2 w) = projectionMatrixToL2 (projectionFullSchwartz w) := by
  funext i j
  apply fourierL2Equiv.injective
  let v := projectionMatrixToL2 w
  let r := projectionRightL2 v
  let q := projectionLeftL2 r
  change fourierL2Equiv (projectionInfraredL2Scalar (q i j)) =
    fourierL2Equiv ((projectionFullSchwartz w i j).toLp 2 volume)
  have hJ := projectionInfraredL2Scalar_fourier (q i j)
  have hL := hodgeVectorL2Action_fourier (fun k => r k j) i
  rw [← projectionLeftL2_apply] at hL
  have hR := ae_all_iff.mpr fun a : Fin 4 => hodgeVectorL2Action_fourier (v a) j
  have hW := ae_all_iff.mpr fun a : Fin 4 => ae_all_iff.mpr fun b : Fin 4 => fourierL2Equiv_schwartz_ae (w a b)
  apply Lp.ext
  filter_upwards [hJ, hL, hR, hW, fourierL2Equiv_schwartz_ae (projectionFullSchwartz w i j)] with ν hj hl hr hw h
  rw [hj, h, projectionFullSchwartz_fourier]
  change _ * fourierL2Equiv (projectionLeftL2 r i j) ν = _
  rw [hl, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [show r a j = hodgeVectorL2Action (v a) j from projectionRightL2_apply v a j, hr a]
  simp only [Finset.mul_sum, regularizedGaugeProjectionSymbol, gaugeProjectionSymbol, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [directionProjectionEntry_swap j b]
  change _ * (_ * (_ * fourierL2Equiv ((w a b).toLp 2 volume) ν)) = _
  rw [hw a b]
  ring

/-- A bounded Schwartz function acts by ordinary multiplication on physical \(L^2\). -/
def projectionCoefficientL2Symbol (f : SchwartzMap E ℂ) : BoundedSymbol E :=
  { toFun := f
    measurable := f.continuous.aestronglyMeasurable
    bound := SchwartzMap.seminorm ℝ 0 0 f
    bound_nonneg := apply_nonneg _ _
    norm_le := f.norm_le_seminorm ℝ }

def projectionMultiplyL2Scalar (f : SchwartzMap E ℂ) : ComplexL2 E →L[ℂ] ComplexL2 E :=
  symbolCLM (projectionCoefficientL2Symbol f)

def projectionMultiplyL2 (f : SchwartzMap E ℂ) : ProjectionL2Matrix →L[ℂ] ProjectionL2Matrix :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (projectionMultiplyL2Scalar f).comp (projectionL2Entry i j)

theorem projectionMultiplyL2_apply (f : SchwartzMap E ℂ) (w : ProjectionL2Matrix) (i j : Fin 4) :
    projectionMultiplyL2 f w i j = projectionMultiplyL2Scalar f (w i j) := rfl

theorem projectionMultiplyL2Scalar_ae (f : SchwartzMap E ℂ) (w : ComplexL2 E) :
    (projectionMultiplyL2Scalar f w : E → ℂ) =ᵐ[volume] fun x => f x * w x :=
  symbolL2_ae (projectionCoefficientL2Symbol f) w

theorem projectionMultiplyL2Scalar_schwartz (f w : SchwartzMap E ℂ) :
    projectionMultiplyL2Scalar f (w.toLp 2 volume) = (hodgeProduct f w).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [projectionMultiplyL2Scalar_ae f (w.toLp 2 volume),
    w.coeFn_toLp 2 volume, (hodgeProduct f w).coeFn_toLp 2 volume] with x hx hw hp
  rw [hx, hw, hp, hodgeProduct_apply]

theorem projectionMultiplyL2_schwartz (f : SchwartzMap E ℂ) (w : ProjectionSchwartzMatrix) :
    projectionMultiplyL2 f (projectionMatrixToL2 w) =
      projectionMatrixToL2 (fun i j => hodgeProduct f (w i j)) := by
  funext i j
  rw [projectionMultiplyL2_apply]
  exact projectionMultiplyL2Scalar_schwartz f (w i j)

end Burnett.P01
