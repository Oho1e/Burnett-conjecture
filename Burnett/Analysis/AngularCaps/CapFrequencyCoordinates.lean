import Burnett.Analysis.AngularCaps.LinearFourierChange
import Burnett.Analysis.AngularCaps.ActualEnlargedCapJets
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section

namespace Burnett.Analysis.CapFourier

open Burnett.Analysis.ProjectiveNullCaps

private def packCoordinates (u : NullFrequencyCoordinates) : Space :=
  WithLp.toLp 2 ![u.1, u.2.1, u.2.2 0, u.2.2 1]

private def unpackCoordinates (x : Space) : NullFrequencyCoordinates :=
  (x 0, x 1, WithLp.toLp 2 ![x 2, x 3])

/-- The fixed coordinate order is the two null components followed by the
two Euclidean screen components. -/
def frequencyCoordinates : Space ≃L[ℝ] NullFrequencyCoordinates :=
  ({
    toFun := unpackCoordinates
    invFun := packCoordinates
    left_inv := by
      intro x
      ext i
      fin_cases i <;> rfl
    right_inv := by
      intro u
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · ext i
          fin_cases i <;> rfl
    map_add' := by
      intro x y
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · ext i
          fin_cases i <;> rfl
    map_smul' := by
      intro a x
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · ext i
          fin_cases i <;> rfl
  } : Space ≃ₗ[ℝ] NullFrequencyCoordinates).toContinuousLinearEquiv

def parabolicDilationEquiv {δ : ℝ} (hδ : δ ≠ 0) :
    NullFrequencyCoordinates ≃L[ℝ] NullFrequencyCoordinates :=
  ({
    toFun := parabolicDilation δ
    invFun := parabolicRescale δ
    left_inv := parabolicRescale_dilation hδ
    right_inv := parabolicDilation_rescale hδ
    map_add' := by
      intro x y
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · simp [parabolicDilation,mul_add]
        · simp [parabolicDilation,smul_add]
    map_smul' := parabolicDilation_smul δ
  } : NullFrequencyCoordinates ≃ₗ[ℝ] NullFrequencyCoordinates).toContinuousLinearEquiv

def capFrameFrequencyEquiv {m : Form} {w : Vec} (F : NullCapChart m w) : Space ≃L[ℝ] Space :=
  frequencyCoordinates.trans F.toFrequency

def capFrequencyEquiv {m : Form} {w : Vec} (F : NullCapChart m w) {δ : ℝ} (hδ : δ ≠ 0) :
    Space ≃L[ℝ] Space :=
  (frequencyCoordinates.trans (parabolicDilationEquiv hδ)).trans F.toFrequency

theorem capFrequencyEquiv_apply {m : Form} {w : Vec} (F : NullCapChart m w) {δ : ℝ}
    (hδ : δ ≠ 0) (x : Space) :
    capFrequencyEquiv F hδ x = chartScaledFrequency F δ (frequencyCoordinates x) := rfl

private def spatialDilation {δ : ℝ} (hδ : δ ≠ 0) : Space ≃L[ℝ] Space :=
  (frequencyCoordinates.trans (parabolicDilationEquiv hδ)).trans frequencyCoordinates.symm

private def diagonalWeights (δ : ℝ) : Fin 4 → ℝ := ![1,δ^2,δ,δ]

private theorem spatialDilation_det {δ : ℝ} (hδ : δ ≠ 0) :
    (spatialDilation hδ).toContinuousLinearMap.det = δ^4 := by
  let e : Space ≃ₗ[ℝ] (Fin 4 → ℝ) := WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)
  let D := Matrix.toLin' (Matrix.diagonal (diagonalWeights δ))
  have he : (spatialDilation hδ).toLinearEquiv.toLinearMap =
      e.symm.toLinearMap ∘ₗ D ∘ₗ e.toLinearMap := by
    ext x i
    change packCoordinates (parabolicDilation δ (unpackCoordinates x)) i =
      (Matrix.toLin' (Matrix.diagonal (diagonalWeights δ)) (fun j => x j)) i
    rw [Matrix.toLin'_apply,Matrix.mulVec_diagonal]
    fin_cases i <;> simp [packCoordinates,unpackCoordinates,parabolicDilation,diagonalWeights]
  change LinearMap.det (spatialDilation hδ).toLinearEquiv.toLinearMap = _
  rw [he,show e.toLinearMap = e.symm.symm.toLinearMap from rfl,LinearMap.det_conj]
  dsimp only [D]
  rw [← LinearMap.det_toMatrix',LinearMap.toMatrix'_toLin',Matrix.det_diagonal,Fin.prod_univ_four]
  simp [diagonalWeights]
  ring

/-- The manuscript's four-dimensional parabolic dilation has weights
1, δ², δ, δ. The remaining Jacobian is that of the chosen null chart. -/
theorem linearJacobian_capFrequencyEquiv {m : Form} {w : Vec} (F : NullCapChart m w)
    {δ : ℝ} (hδ : δ ≠ 0) :
    linearJacobian (capFrequencyEquiv F hδ) = δ^4 * linearJacobian (capFrameFrequencyEquiv F) := by
  have he : (capFrequencyEquiv F hδ).toLinearEquiv.toLinearMap =
      (capFrameFrequencyEquiv F).toLinearEquiv.toLinearMap ∘ₗ
        (spatialDilation hδ).toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro x
    change F.toFrequency (parabolicDilation δ (frequencyCoordinates x)) =
      F.toFrequency (frequencyCoordinates
        (frequencyCoordinates.symm (parabolicDilation δ (frequencyCoordinates x))))
    rw [frequencyCoordinates.apply_symm_apply]
  change |LinearMap.det (capFrequencyEquiv F hδ).toLinearEquiv.toLinearMap| =
    δ^4 * |LinearMap.det (capFrameFrequencyEquiv F).toLinearEquiv.toLinearMap|
  rw [he,LinearMap.det_comp,show LinearMap.det (spatialDilation hδ).toLinearEquiv.toLinearMap =
      δ^4 from spatialDilation_det hδ,abs_mul,abs_of_nonneg (by positivity : 0 ≤ δ^4),mul_comm]

end Burnett.Analysis.CapFourier
