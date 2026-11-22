import Burnett.Analysis.GaugeProjection.MatrixSlotCommutators
import Burnett.Analysis.GaugeProjection.HodgeAnnularCore

set_option autoImplicit false
set_option maxHeartbeats 3400000

noncomputable section

namespace Burnett.P01

open MeasureTheory
open Burnett.A02.FrequencySplit (E radianFourier)
open Burnett.A07 (coordinateDerivative)
open Burnett.Fourier
open scoped NNReal

/-- Both component indices have their radian spectrum in the same given set. -/
def projectionMatrixSpectrumIn (w : ProjectionSchwartzMatrix) (K : Set E) : Prop :=
  ∀ i j, tsupport (radianFourier (w i j : E → ℂ)) ⊆ K

private theorem hodgeSpectrum_support (w A : HodgeSchwartzField) (K : Set E) (hK : IsClosed K)
    (hw : ∀ j, tsupport (radianFourier (w j : E → ℂ)) ⊆ K)
    (hA : ∀ ξ, hodgeSpectrum A ξ = hodgeTransverse ξ (hodgeSpectrum w ξ)) :
    ∀ j, tsupport (radianFourier (A j : E → ℂ)) ⊆ K := by
  intro j
  apply closure_minimal _ hK
  intro ξ hξ
  by_contra hn
  have hz : hodgeSpectrum w ξ = 0 := by
    funext k
    exact not_not.mp (fun hp => hn (hw k (subset_tsupport _ hp)))
  have hm := hA ξ
  rw [hz, map_zero] at hm
  exact hξ (congrFun hm j)

private theorem exists_twoSchwartz_hodgeSlots (w : ProjectionSchwartzMatrix) (K : Set E)
    (hK : IsCompact K) (h0 : (0 : E) ∉ K) (hw : projectionMatrixSpectrumIn w K) :
    ∃ r q : ProjectionSchwartzMatrix,
      (∀ i ξ, hodgeSpectrum (r i) ξ = hodgeTransverse ξ (hodgeSpectrum (w i) ξ)) ∧
      (∀ j ξ, hodgeSpectrum (fun i => q i j) ξ = hodgeTransverse ξ (hodgeSpectrum (fun i => r i j) ξ)) := by
  have hR (i : Fin 4) := exists_hodgeTransverseSchwartz_of_compactSpectrum (w i) K hK h0 (hw i)
  choose r hr _ using hR
  have hKr := fun i => hodgeSpectrum_support (w i) (r i) K hK.isClosed (hw i) (hr i)
  have hQ (j : Fin 4) := exists_hodgeTransverseSchwartz_of_compactSpectrum (fun i => r i j)
    K hK h0 (fun i => hKr i j)
  choose q hq _ using hQ
  exact ⟨r, fun i j => q j i, hr, hq⟩

private theorem hodgeVectorL2Action_schwartz_derivative (b : Fin 4) (w A : HodgeSchwartzField)
    (hA : ∀ ξ, hodgeSpectrum A ξ = hodgeTransverse ξ (hodgeSpectrum w ξ)) (i : Fin 4) :
    hodgeVectorL2Action (fun j => (coordinateDerivative b (w j)).toLp 2 volume) i =
      (coordinateDerivative b (A i)).toLp 2 volume := by
  apply Lp.ext
  have h := hodgeVectorL2Action_schwartz_ae (fun j => coordinateDerivative b (w j)) i
  rw [hodgeTransverseAction_derivative b w A hA] at h
  exact h.trans ((coordinateDerivative b (A i)).coeFn_toLp 2 volume).symm

/-- The actual \(L^2\) matrix commutator applied to the original coordinate derivative. -/
def projectionFullCommutatorL2 (b : Fin 4) (f : SchwartzMap E ℂ) (w : ProjectionSchwartzMatrix) :
    ProjectionL2Matrix :=
  let d := projectionMatrixToL2 (projectionMatrixDerivative b w)
  projectionFullL2 (projectionMultiplyL2 f d) - projectionMultiplyL2 f (projectionFullL2 d)

/-- On Schwartz functions the commutator uses the original full projection,
its original derivative slot, and multiplication by the same coefficient. -/
theorem projectionFullCommutatorL2_eq_actual (b : Fin 4) (f : SchwartzMap E ℂ)
    (w : ProjectionSchwartzMatrix) :
    projectionFullCommutatorL2 b f w =
      projectionMatrixToL2 (fun i j =>
        projectionFullSchwartz (fun a c => hodgeProduct f (coordinateDerivative b (w a c))) i j -
        hodgeProduct f (projectionFullSchwartz (projectionMatrixDerivative b w) i j)) := by
  dsimp only [projectionFullCommutatorL2]
  rw [projectionMultiplyL2_schwartz, projectionFullL2_eq_schwartz, projectionFullL2_eq_schwartz,
    projectionMultiplyL2_schwartz]
  funext i j
  change _ - _ = (schwartzLpMap (V := E)) (_ - _)
  exact (map_sub (schwartzLpMap (V := E)) _ _).symm

/-- The differentiated commutator of the original real even matrix multiplier.
On the annular Schwartz core the constant is independent of the spectral set,
the derivative coordinate, the coefficient, and the field. -/
theorem exists_projectionFullCommutatorL2_bound_on_annularCore :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : Fin 4) (f : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L (f : E → ℂ) →
      ∀ (w : ProjectionSchwartzMatrix) (K : Set E), IsCompact K → (0 : E) ∉ K →
        projectionMatrixSpectrumIn w K →
          ‖projectionFullCommutatorL2 b f w‖ ≤ C * (L : ℝ) * ‖projectionMatrixToL2 w‖ := by
  obtain ⟨H, hH, HB⟩ := exists_hodgeVectorL2_commutator_bound
  let R := projectionRightL2
  let P := projectionLeftL2
  let J := projectionInfraredL2
  let M₀ := projectionInfraredCommutatorConstant
  let C := ‖J‖ * ‖P‖ * H + ‖J‖ * H * ‖R‖ + M₀ * ‖P‖ * ‖R‖
  have hM₀ : 0 ≤ M₀ := projectionInfraredCommutatorConstant_nonneg
  refine ⟨C, by unfold C; positivity, fun b f L hf w K hK h0 hSp => ?_⟩
  obtain ⟨r,q,hr,hq⟩ := exists_twoSchwartz_hodgeSlots w K hK h0 hSp
  let M := projectionMultiplyL2 f
  let W := projectionMatrixToL2 w
  let d := projectionMatrixToL2 (projectionMatrixDerivative b w)
  have eR : R W = projectionMatrixToL2 r := by
    funext i j
    rw [show R W i j = hodgeVectorL2Action (W i) j from projectionRightL2_apply W i j]
    exact hodgeVectorL2Action_schwartz_eq (w i) (r i) (hr i) j
  have eP : P (projectionMatrixToL2 r) = projectionMatrixToL2 q := by
    funext i j
    exact (projectionLeftL2_apply _ i j).trans
      (hodgeVectorL2Action_schwartz_eq (fun a => r a j) (fun a => q a j) (hq j) i)
  have eRd : R d = projectionMatrixToL2 (projectionMatrixDerivative b r) := by
    funext i j
    exact (projectionRightL2_apply d i j).trans
      (hodgeVectorL2Action_schwartz_derivative b (w i) (r i) (hr i) j)
  have ePd : P (R d) = projectionMatrixToL2 (projectionMatrixDerivative b q) := by
    rw [eRd]
    funext i j
    exact (projectionLeftL2_apply _ i j).trans
      (hodgeVectorL2Action_schwartz_derivative b (fun a => r a j) (fun a => q a j) (hq j) i)
  let X := R (M d) - M (R d)
  let Y := P (M (R d)) - M (P (R d))
  let Z := J (M (P (R d))) - M (J (P (R d)))
  have hX : ‖X‖ ≤ H * (L : ℝ) * ‖W‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro j
    have hj := HB b f (w i) (r i) (hr i) L hf j
    change ‖projectionRightL2 (projectionMultiplyL2 f d) i j -
      projectionMultiplyL2 f (projectionRightL2 d) i j‖ ≤ _
    simp only [projectionRightL2_apply, projectionMultiplyL2_apply] at *
    exact hj.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm W i) (by positivity))
  have hY : ‖Y‖ ≤ H * (L : ℝ) * ‖projectionMatrixToL2 r‖ := by
    have hcol (j : Fin 4) : ‖fun a => projectionMatrixToL2 r a j‖ ≤ ‖projectionMatrixToL2 r‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a =>
        (norm_le_pi_norm (projectionMatrixToL2 r a) j).trans
          (norm_le_pi_norm (projectionMatrixToL2 r) a)
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro j
    have hi := HB b f (fun a => r a j) (fun a => q a j) (hq j) L hf i
    change ‖P (M (R d)) i j - M (P (R d)) i j‖ ≤ _
    rw [eRd]
    simp only [P,M, projectionLeftL2_apply, projectionMultiplyL2_apply]
    exact hi.trans (mul_le_mul_of_nonneg_left (hcol j) (by positivity))
  have hZ : ‖Z‖ ≤ M₀ * (L : ℝ) * ‖projectionMatrixToL2 q‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro j
    change ‖J (M (P (R d))) i j - M (J (P (R d))) i j‖ ≤ _
    rw [ePd]
    simp only [J,M, projectionInfraredL2_apply, projectionMultiplyL2_apply]
    exact (projectionInfraredL2_commutator_bound b f (q i j) L hf).trans
      (mul_le_mul_of_nonneg_left
        ((norm_le_pi_norm (projectionMatrixToL2 q i) j).trans
          (norm_le_pi_norm (projectionMatrixToL2 q) i)) (by positivity))
  have hR : ‖projectionMatrixToL2 r‖ ≤ ‖R‖ * ‖W‖ := eR ▸ R.le_opNorm W
  have hP : ‖projectionMatrixToL2 q‖ ≤ ‖P‖ * (‖R‖ * ‖W‖) := by
    rw [← eP]
    exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left hR (norm_nonneg _))
  have hdec : projectionFullCommutatorL2 b f w = J (P X) + J Y + Z := by
    unfold projectionFullCommutatorL2 projectionFullL2 X Y Z R P J M d
    simp only [ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [hdec]
  calc
    _ ≤ ‖J (P X)‖ + ‖J Y‖ + ‖Z‖ := (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ ‖J‖ * (‖P‖ * ‖X‖) + ‖J‖ * ‖Y‖ + ‖Z‖ := by
      exact add_le_add_right (add_le_add
        ((J.le_opNorm _).trans (mul_le_mul_of_nonneg_left (P.le_opNorm _) (norm_nonneg _)))
        (J.le_opNorm _)) _
    _ ≤ ‖J‖ * (‖P‖ * (H * (L : ℝ) * ‖W‖)) +
        ‖J‖ * (H * (L : ℝ) * (‖R‖ * ‖W‖)) +
        M₀ * (L : ℝ) * (‖P‖ * (‖R‖ * ‖W‖)) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hX (norm_nonneg _)) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left
          (hY.trans (mul_le_mul_of_nonneg_left hR (by positivity))) (norm_nonneg _)))
        (hZ.trans (mul_le_mul_of_nonneg_left hP (by positivity)))
    _ = _ := by unfold C W; ring

end Burnett.P01
