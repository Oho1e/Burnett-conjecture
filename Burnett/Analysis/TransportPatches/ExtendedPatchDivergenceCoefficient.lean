import Burnett.Analysis.TransportPatches.CorrectionCoefficientCutoff
import Burnett.Analysis.GaugeProjection.IntrinsicChartProjectedNorms
import Burnett.Analysis.GaugeProjection.ProjectedDivergenceDefinitions
import Burnett.Analysis.LocalWeakDerivative

/-! The extension entering the actual projected divergence is smooth on
the whole coordinate space and carries the first-jet patch bound. -/
set_option autoImplicit false
set_option maxRecDepth 3800
set_option maxHeartbeats 3200000

noncomputable section

namespace Burnett.C03

open Set Function Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference InverseField SmoothMetricConnection
open Burnett.P01 (SmoothCoordinateComponents coordinate_opNorm_le ProjectedSourceCoefficients)
open scoped ContDiff NNReal Topology

/-- The finite patch inverse extension is globally smooth, with a
Lipschitz bound controlled by the actual first coordinate jet. -/
theorem patch_inverse_smooth_lipschitz
    (U : Set CoordinateSpace) (hU : IsOpen U)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hSupp : tsupport χ ⊆ U)
    (g : CoordinateSpace → Tensor2) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) U)
    (hND : ∀ x ∈ U, Matrix.det (g x) ≠ 0) (m : Tensor2) (D : ℝ) (hD : 0 ≤ D)
    (hJet : ∀ x, ‖coordinateJet (correctionCoefficientPart χ (matrixInverse ∘ g) m) x‖ ≤ D) :
    let a (x : CoordinateSpace) := m + correctionCoefficientPart χ (matrixInverse ∘ g) m x
    SmoothCoordinateComponents a ∧
      ∀ i j, LipschitzWith (Real.toNNReal (4 * D)) (fun x => a x i j) := by
  let d := correctionCoefficientPart χ (matrixInverse ∘ g) m
  let a (i j : Index) (x : CoordinateSpace) := (m + d x) i j
  have hSmoothD : SmoothCoordinateComponents d := by
    intro i j
    exact Burnett.Analysis.LocalWeakDerivative.contDiff_test_mul_local hU hχ hSupp
      ((contDiffOn_matrixInverse g U hg hND i j).sub contDiffOn_const)
  have hSmooth (i j : Index) : ContDiff ℝ ∞ (a i j) := contDiff_const.add (hSmoothD i j)
  let slope := Real.toNNReal (4 * D)
  have hLip (i j : Index) : LipschitzWith slope (a i j) := by
    apply lipschitzWith_of_nnnorm_fderiv_le ((hSmooth i j).differentiable (by simp))
    intro x
    change ‖fderiv ℝ (a i j) x‖ ≤ (Real.toNNReal (4 * D) : ℝ)
    rw [Real.coe_toNNReal', max_eq_left (by positivity : 0 ≤ 4 * D)]
    have he : fderiv ℝ (a i j) x = fderiv ℝ (fun x => d x i j) x :=
      (((hSmoothD i j).differentiable (by simp) x).hasFDerivAt.const_add (m i j)).fderiv
    rw [he]
    apply coordinate_opNorm_le _ _ hD
    intro b
    change ‖coordinateJet d x b i j‖ ≤ D
    exact ((norm_le_pi_norm (coordinateJet d x b i) j).trans
      ((norm_le_pi_norm (coordinateJet d x b) i).trans
        (norm_le_pi_norm (coordinateJet d x) b))).trans (hJet x)
  exact ⟨hSmooth, hLip⟩

/-- The true finite patch inverse extension yields the exact coefficient
record consumed by the whole-space Fourier projection. -/
theorem exists_patch_projectedSourceCoefficients
    (U : Set CoordinateSpace) (hU : IsOpen U)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hSupp : tsupport χ ⊆ U)
    (g : CoordinateSpace → Tensor2) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) U)
    (hND : ∀ x ∈ U, Matrix.det (g x) ≠ 0) (m : Tensor2) (D : ℝ) (hD : 0 ≤ D)
    (hJet : ∀ x, ‖coordinateJet (correctionCoefficientPart χ (matrixInverse ∘ g) m) x‖ ≤ D) :
    ∃ A : ProjectedSourceCoefficients,
      (∀ i j x, A.entry i j x = ((m + correctionCoefficientPart χ
        (matrixInverse ∘ g) m x) i j : ℝ)) ∧
      (A.slope : ℝ) = 4 * D := by
  let a (x : CoordinateSpace) := m + correctionCoefficientPart χ (matrixInverse ∘ g) m x
  let L := Real.toNNReal (4 * D)
  obtain ⟨hSmooth, hLip⟩ := patch_inverse_smooth_lipschitz U hU χ hχ hSupp g hg hND m D hD hJet
  refine ⟨ProjectedSourceCoefficients.ofReal (fun i j x => a x i j) hSmooth L hLip, fun _ _ _ => rfl, ?_⟩
  change (Real.toNNReal (4 * D) : ℝ) = 4 * D
  rw [Real.coe_toNNReal', max_eq_left (by positivity : 0 ≤ 4 * D)]

end Burnett.C03
