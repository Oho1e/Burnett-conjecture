import Burnett.Analysis.GaugeProjection.LocalizedVacuumSource
import Burnett.Analysis.GaugeProjection.ProjectedSourceInverseJet
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false
set_option maxHeartbeats 5600000

noncomputable section

namespace Burnett.P01

open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.CurvatureDifference
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology

/-- The variable values used by the local source. Its only second metric jet
belongs to the fixed background. -/
abbrev LocalizedSourceJets :=
  Tensor2 × FirstJet × FirstJet × Tensor2 × FirstJet × SecondMetricJet

def localizedSourceJets (inv g g₀ : CoordinateSpace → Tensor2) (x : CoordinateSpace) :
    LocalizedSourceJets :=
  (inv x, coordinateJet g x, coordinateJet inv x, g x - g₀ x,
    coordinateJet g x - coordinateJet g₀ x, coordinateSecondMetricJet g₀ x)

private def sourceRemainderOnJets (χ : CoordinateSpace → ℝ) (i j : Index)
    (q : CoordinateSpace × LocalizedSourceJets) : ℝ :=
  let x := q.1
  let (A, D, DI, h, Dh, D₂) := q.2
  χ x * (projectedSourceFirstJetRemainder A D DI i j - ∑ a, ∑ b, A a b * D₂ a b i j) +
    (∑ a, ∑ b, A a b * (scalarPartial (scalarPartial χ b) a x * h i j +
      scalarPartial χ b x * Dh a i j + scalarPartial χ a x * Dh b i j)) -
    (scalarPartial χ i x * loweredGaugeCovector A D j +
      scalarPartial χ j x * loweredGaugeCovector A D i)

private theorem scalarPartial_smooth (f : CoordinateSpace → ℝ) (a : Index)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (scalarPartial f a) := by
  unfold scalarPartial
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem scalarPartial_tsupport_subset (f : CoordinateSpace → ℝ) (a : Index) :
    tsupport (scalarPartial f a) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply support_fderiv_subset ℝ
  intro hz
  apply hx
  simp [scalarPartial, hz]

private theorem loweredGaugeCovector_expanded (A : Tensor2) (D : FirstJet) (j : Index) :
    loweredGaugeCovector A D j = (∑ a, ∑ b, A a b * D a b j) -
      (∑ a, ∑ b, A a b * D j a b) / 2 := rfl

private theorem sourceRemainderOnJets_continuous (χ : CoordinateSpace → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (i j : Index) : Continuous (sourceRemainderOnJets χ i j) := by
  have hFirst (a : Index) : Continuous (scalarPartial χ a) :=
    (scalarPartial_smooth χ a hχ).continuous
  have hSecond (a b : Index) : Continuous (scalarPartial (scalarPartial χ b) a) :=
    (scalarPartial_smooth _ a (scalarPartial_smooth χ b hχ)).continuous
  have hCut := hχ.continuous
  unfold sourceRemainderOnJets projectedSourceFirstJetRemainder firstJetRicciRemainder
    ricci christoffel koszul
  dsimp only
  simp only [loweredGaugeCovector_expanded]
  fun_prop

private theorem sourceRemainderOnJets_eq (inv g g₀ : CoordinateSpace → Tensor2)
    (χ : CoordinateSpace → ℝ) (i j : Index) (x : CoordinateSpace)
    (hg : DifferentiableComponentsAt g x) (hg₀ : DifferentiableComponentsAt g₀ x) :
    sourceRemainderOnJets χ i j (x, localizedSourceJets inv g g₀ x) =
      localizedVacuumSourceRemainder inv g g₀ χ x i j := by
  have h (a : Index) :
      scalarPartial (fun y => g y i j - g₀ y i j) a x =
        coordinateJet g x a i j - coordinateJet g₀ x a i j := by
    simp only [scalarPartial, coordinateJet,
      fderiv_fun_sub (hg i j) (hg₀ i j), ContinuousLinearMap.sub_apply]
  unfold sourceRemainderOnJets localizedSourceJets localizedVacuumSourceRemainder
    localizedWaveError coordinateGaugeCovector scalarWaveAt
  simp only [h, Pi.sub_apply]
  rfl

private theorem sourceRemainderOnJets_eq_zero_off (χ : CoordinateSpace → ℝ)
    (i j : Index) (q : CoordinateSpace × LocalizedSourceJets)
    (hx : q.1 ∉ tsupport χ) : sourceRemainderOnJets χ i j q = 0 := by
  have hCut : χ q.1 = 0 := image_eq_zero_of_notMem_tsupport hx
  have hFirst (a : Index) : scalarPartial χ a q.1 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (scalarPartial_tsupport_subset χ a h))
  have hSecond (a b : Index) : scalarPartial (scalarPartial χ b) a q.1 = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hx (scalarPartial_tsupport_subset χ b
        (scalarPartial_tsupport_subset (scalarPartial χ b) a h)))
  simp [sourceRemainderOnJets, hCut, hFirst, hSecond]

/-- One compactly supported bounded function dominates the exact remainder
throughout the sequence. Only the indicated first metric jets, the inverse
metric data and the fixed background derivatives enter the bound. -/
theorem exists_localizedVacuumSourceRemainder_majorant
    (inv g : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (χ : CoordinateSpace → ℝ) (i j : Index) (B : ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hg : ∀ n x, DifferentiableComponentsAt (g n) x)
    (hg₀ : ∀ x, DifferentiableComponentsAt g₀ x)
    (hBound : ∀ n x, x ∈ tsupport χ → ‖localizedSourceJets (inv n) (g n) g₀ x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, ‖localizedVacuumSourceRemainder (inv n) (g n) g₀ χ x i j‖ ≤
      (tsupport χ).indicator (fun _ => C) x := by
  let K : Set (CoordinateSpace × LocalizedSourceJets) :=
    tsupport χ ×ˢ Metric.closedBall 0 B
  have hK : IsCompact K := hχc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (sourceRemainderOnJets_continuous χ hχ i j).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun n x => ?_⟩
  rw [← sourceRemainderOnJets_eq _ _ _ _ _ _ _ (hg n x) (hg₀ x)]
  by_cases hx : x ∈ tsupport χ
  · have hMem : (x, localizedSourceJets (inv n) (g n) g₀ x) ∈ K :=
      ⟨hx, by simpa only [Metric.mem_closedBall, dist_zero_right] using hBound n x hx⟩
    rw [Set.indicator_of_mem hx]
    exact (hC _ hMem).trans (le_max_left _ _)
  · rw [sourceRemainderOnJets_eq_zero_off χ i j _ hx, norm_zero, Set.indicator_of_notMem hx]

/-- The first derivative of the inverse metric is controlled by the same
bounded inverse metric and first metric derivative. -/
theorem norm_coordinateJet_inverse_le
    (g inv : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (hg : DifferentiableComponentsAt g x) (hi : DifferentiableComponentsAt inv x)
    (hLeft : ∀ᶠ y in 𝓝 x, ∀ a b, (∑ k, inv y a k * g y k b) = if a = b then 1 else 0)
    (hRight : ∀ a b, (∑ k, g x a k * inv x k b) = if a = b then 1 else 0) :
    ‖coordinateJet inv x‖ ≤ 16 * ‖inv x‖ ^ 2 * ‖coordinateJet g x‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro a
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro b
  have h := congrFun (congrFun (coordinateJet_inverse_eq_neg g inv x hg hi hLeft hRight i) a) b
  simp only [Matrix.of_apply, Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul] at h
  rw [h, norm_neg]
  calc
    _ ≤ ∑ k : Index, ∑ l : Index, ‖inv x a l * coordinateJet g x i l k * inv x k b‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _ : Index, ∑ _ : Index, ‖inv x‖ ^ 2 * ‖coordinateJet g x‖ := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      have hA : ‖inv x a l‖ ≤ ‖inv x‖ := (norm_le_pi_norm (inv x a) l).trans (norm_le_pi_norm _ a)
      have hB : ‖inv x k b‖ ≤ ‖inv x‖ := (norm_le_pi_norm (inv x k) b).trans (norm_le_pi_norm _ k)
      have hD : ‖coordinateJet g x i l k‖ ≤ ‖coordinateJet g x‖ :=
        ((norm_le_pi_norm (coordinateJet g x i l) k).trans (norm_le_pi_norm _ l)).trans
          (norm_le_pi_norm _ i)
      rw [norm_mul, norm_mul]
      calc
        _ ≤ ‖inv x‖ * ‖coordinateJet g x‖ * ‖inv x‖ := by gcongr
        _ = _ := by ring
    _ = _ := by simp [Index]; ring

end Burnett.P01
