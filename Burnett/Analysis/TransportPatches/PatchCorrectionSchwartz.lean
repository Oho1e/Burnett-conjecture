import Burnett.Analysis.TransportPatches.CorrectionCoefficientCutoff
import Burnett.Analysis.GaugeProjection.ProjectedChartRepresentatives
import Burnett.Analysis.GaugeProjection.IntrinsicChartProjectedNorms
import Burnett.Analysis.LocalWeakDerivative

set_option autoImplicit false
set_option maxRecDepth 3800
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.C03

open Function Set Burnett.RicciSymbol Burnett.P01 Burnett.Geometry
open ConnectionDifference InverseField SmoothMetricConnection
open scoped ContDiff

open private projectedChartInverse_symmetric from
  Burnett.Analysis.GaugeProjection.ProjectedChartRepresentatives

/-- Both correction energies can use Schwartz entries for the original
variable part of the scalar patch coefficient, with its actual global bounds. -/
theorem exists_patchCorrectionSchwartz
    (U : Set CoordinateSpace) (hU : IsOpen U)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hSupp : tsupport χ ⊆ U)
    (g : CoordinateSpace → Tensor2) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) U)
    (hND : ∀ x ∈ U, Matrix.det (g x) ≠ 0) (hSym : ∀ x ∈ U, IsSymmetricTensor (g x))
    (m : Tensor2) (hm : IsSymmetricTensor m)
    (M D : ℝ) (hD : 0 ≤ D)
    (hBound : ∀ x, ‖correctionCoefficientPart χ (matrixInverse ∘ g) m x‖ ≤ M)
    (hJet : ∀ x, ‖coordinateJet (correctionCoefficientPart χ (matrixInverse ∘ g) m) x‖ ≤ D) :
    ∃ d : Index → Index → SchwartzMap CoordinateSpace ℝ,
      (∀ i j x, d i j x = correctionCoefficientPart χ (matrixInverse ∘ g) m x i j) ∧
      (∀ i j, d i j = d j i) ∧
      (∀ i j x, |d i j x| ≤ M) ∧
      ∀ i j x, ‖fderiv ℝ (d i j : CoordinateSpace → ℝ) x‖ ≤ 4 * D := by
  let d₀ := correctionCoefficientPart χ (matrixInverse ∘ g) m
  have hSmooth (i j : Index) : ContDiff ℝ ∞ (fun x => d₀ x i j) :=
    Burnett.Analysis.LocalWeakDerivative.contDiff_test_mul_local hU hχ hSupp
      ((contDiffOn_matrixInverse g U hg hND i j).sub contDiffOn_const)
  have hZero (x : CoordinateSpace) (hx : x ∉ tsupport χ) : d₀ x = 0 := by
    simp [d₀, correctionCoefficientPart, image_eq_zero_of_notMem_tsupport hx]
  have hCompact (i j : Index) : HasCompactSupport (fun x => d₀ x i j) := by
    apply hc.mono'
    intro x hx
    by_contra hxχ
    exact hx (congrArg (fun d : Tensor2 => d i j) (hZero x hxχ))
  let d (i j : Index) := (hCompact i j).toSchwartzMap (hSmooth i j)
  refine ⟨d, fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro i j
    ext x
    change d₀ x i j = d₀ x j i
    by_cases hx : x ∈ tsupport χ
    · have hIn : IsSymmetricTensor (matrixInverse (g x)) :=
        projectedChartInverse_symmetric g x (hSym x (hSupp hx))
      change χ x * (matrixInverse (g x) i j - m i j) =
        χ x * (matrixInverse (g x) j i - m j i)
      rw [hIn i j, hm i j]
    · simp only [hZero x hx, Pi.zero_apply]
  · intro i j x
    change ‖d₀ x i j‖ ≤ M
    exact ((norm_le_pi_norm (d₀ x i) j).trans (norm_le_pi_norm (d₀ x) i)).trans (hBound x)
  · intro i j x
    change ‖fderiv ℝ (fun x => d₀ x i j) x‖ ≤ 4 * D
    apply coordinate_opNorm_le _ _ hD
    intro a
    change ‖coordinateJet d₀ x a i j‖ ≤ D
    exact ((norm_le_pi_norm (coordinateJet d₀ x a i) j).trans
      ((norm_le_pi_norm (coordinateJet d₀ x a) i).trans
        (norm_le_pi_norm (coordinateJet d₀ x) a))).trans (hJet x)

end Burnett.C03
