import Burnett.Analysis.TransportPatches.OriginalInverseJetControl
import Mathlib.Analysis.Calculus.MeanValue

/-! The global scalar coefficient used in both C03 corrections. The
patch's outer cutoff confines the varying part, while the extension
equals the original inverse near the localized field. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.C03

open Filter Set Metric Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference InverseField InversePerturbation SmoothMetricConnection
open scoped ContDiff Topology BigOperators

/-- The actual varying part of the coefficient after extension to the
full coordinate space. -/
def correctionCoefficientPart (χ : CoordinateSpace → ℝ) (A : CoordinateSpace → Tensor2)
    (m : Tensor2) (x : CoordinateSpace) : Tensor2 :=
  χ x • (A x - m)

/-- The extended coefficient is the original coefficient everywhere on
the plateau, so it agrees as a germ at each supported field point. -/
theorem correctionCoefficient_eq_on_plateau (χ : CoordinateSpace → ℝ)
    (A : CoordinateSpace → Tensor2) (m : Tensor2) {S : Set CoordinateSpace}
    (hχ : ∀ y ∈ S, χ y = 1) (hS : IsOpen S) {x : CoordinateSpace} (hx : x ∈ S) :
    (fun y => m + correctionCoefficientPart χ A m y) =ᶠ[𝓝 x] A := by
  filter_upwards [hS.mem_nhds hx] with y hy
  rw [correctionCoefficientPart, hχ y hy, one_smul]
  abel

/-- The coefficient and its first derivative are bounded on the whole
space, with explicit cutoff and patch scales. -/
theorem correctionCoefficientPart_norm_and_jet_le
    (K : Set CoordinateSpace) (χ : CoordinateSpace → ℝ) (hχ : Differentiable ℝ χ)
    (hSupp : tsupport χ ⊆ K) (A : CoordinateSpace → Tensor2) (m : Tensor2)
    (G J W : ℝ) (hG : 0 ≤ G) (hJ : 0 ≤ J) (hW : 0 ≤ W)
    (hDiff : ∀ x ∈ K, DifferentiableComponentsAt A x)
    (hCut : ∀ x ∈ K, ‖χ x‖ ≤ 1 ∧ ‖fderiv ℝ χ x‖ ≤ W)
    (hA : ∀ x ∈ K, ‖A x - m‖ ≤ G ∧ ‖coordinateJet A x‖ ≤ J) :
    ∀ x, ‖correctionCoefficientPart χ A m x‖ ≤ G ∧
      ‖coordinateJet (correctionCoefficientPart χ A m) x‖ ≤ J + G * W := by
  intro x
  by_cases hx : x ∈ K
  · constructor
    · rw [correctionCoefficientPart, norm_smul, ← one_mul G]
      exact mul_le_mul (hCut x hx).1 (hA x hx).1 (norm_nonneg _) zero_le_one
    · rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro d
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro j
      let v := EuclideanSpace.single d (1 : ℝ)
      have h₁ := (hχ x).hasFDerivAt
      have h₂ := ((hDiff x hx) i j).hasFDerivAt.sub_const (m i j)
      have hF := (h₁.fun_mul h₂).fderiv
      change ‖fderiv ℝ (fun y => χ y * (A y i j - m i j)) x v‖ ≤ _
      rw [hF]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have hDv : ‖fderiv ℝ χ x v‖ ≤ W := by
        have h := (fderiv ℝ χ x).le_opNorm v
        rw [show ‖v‖ = 1 by simp [v, EuclideanSpace.norm_single], mul_one] at h
        exact h.trans (hCut x hx).2
      have hDA : ‖fderiv ℝ (fun y => A y i j) x v‖ ≤ J := by
        change ‖coordinateJet A x d i j‖ ≤ J
        exact ((norm_le_pi_norm (coordinateJet A x d i) j).trans
          ((norm_le_pi_norm (coordinateJet A x d) i).trans
            (norm_le_pi_norm (coordinateJet A x) d))).trans (hA x hx).2
      have hDiffNorm : ‖A x i j - m i j‖ ≤ G :=
        ((norm_le_pi_norm ((A x - m) i) j).trans
          (norm_le_pi_norm (A x - m) i)).trans (hA x hx).1
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul]
      simpa only [one_mul] using add_le_add
        (mul_le_mul (hCut x hx).1 hDA (norm_nonneg _) zero_le_one)
        (mul_le_mul hDiffNorm hDv (norm_nonneg _) hG)
  · have hxSupp : x ∉ tsupport χ := fun h => hx (hSupp h)
    have hN : ∀ᶠ y in 𝓝 x, y ∉ tsupport χ :=
      isClosed_closure.isOpen_compl.mem_nhds hxSupp
    have hZero : coordinateJet (correctionCoefficientPart χ A m) x = 0 := by
      funext d i j
      have hGerm : (fun y => correctionCoefficientPart χ A m y i j) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hN] with y hy
        simp [correctionCoefficientPart, image_eq_zero_of_notMem_tsupport hy]
      simp only [coordinateJet, hGerm.fderiv_eq, fderiv_const_apply,
        ContinuousLinearMap.zero_apply, Pi.zero_apply]
    rw [hZero, correctionCoefficientPart, image_eq_zero_of_notMem_tsupport hxSupp, zero_smul,
      norm_zero, norm_zero]
    exact ⟨hG, by positivity⟩

end Burnett.C03
