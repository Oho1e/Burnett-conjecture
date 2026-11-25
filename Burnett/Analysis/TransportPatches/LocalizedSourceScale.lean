import Burnett.Analysis.GaugeProjection.WholeSpaceProjectedVacuumSource
import Burnett.Geometry.InversePerturbation

/-! Quantitative scale losses of the actual P01 localized vacuum source
used in the C03 patch budget. -/
set_option autoImplicit false
set_option maxRecDepth 3600
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.C03

open Burnett.P01 Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.InversePerturbation
open scoped BigOperators

/-- Two cutoff derivatives multiply the undifferentiated field, and a
single cutoff derivative multiplies each first derivative. -/
theorem norm_localizedWaveError_le
    (A : Tensor2) (χ f : CoordinateSpace → ℝ) (x : CoordinateSpace)
    (B D e C₁ C₂ : ℝ) (hB : 0 ≤ B) (hA : ‖A‖ ≤ B)
    (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂) (hVal : ‖f x‖ ≤ e)
    (hD : ∀ a, ‖scalarPartial f a x‖ ≤ D)
    (hCut₁ : ∀ a, ‖scalarPartial χ a x‖ ≤ C₁)
    (hCut₂ : ∀ a b, ‖scalarPartial (scalarPartial χ b) a x‖ ≤ C₂) :
    ‖localizedWaveError A χ f x‖ ≤ 16 * B * (C₂ * e + 2 * C₁ * D) := by
  let t (a b : Index) := A a b * (scalarPartial (scalarPartial χ b) a x * f x +
    scalarPartial χ b x * scalarPartial f a x + scalarPartial χ a x * scalarPartial f b x)
  have hTerm (a b : Index) : ‖t a b‖ ≤ B * (C₂ * e + 2 * C₁ * D) := by
    have hInner :
        ‖scalarPartial (scalarPartial χ b) a x * f x +
          scalarPartial χ b x * scalarPartial f a x + scalarPartial χ a x * scalarPartial f b x‖ ≤
        C₂ * e + 2 * C₁ * D := by
      refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl |>.trans ?_)
      simp only [norm_mul]
      calc
        _ ≤ C₂ * e + C₁ * D + C₁ * D := add_le_add
          (add_le_add (mul_le_mul (hCut₂ a b) hVal (norm_nonneg _) h₂)
            (mul_le_mul (hCut₁ b) (hD a) (norm_nonneg _) h₁))
          (mul_le_mul (hCut₁ a) (hD b) (norm_nonneg _) h₁)
        _ = _ := by ring
    change ‖A a b * _‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul ((show ‖A a b‖ ≤ ‖A‖ by
      simpa only [Real.norm_eq_abs] using abs_entry_le_norm A a b).trans hA)
      hInner (norm_nonneg _) hB
  change ‖∑ a, ∑ b, t a b‖ ≤ _
  calc
    _ ≤ ∑ a, ∑ b, ‖t a b‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _ : Index, ∑ _ : Index, B * (C₂ * e + 2 * C₁ * D) :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hTerm a b
    _ = _ := by simp; ring

/-- A single estimate for the actual differentiated-cutoff source
remainder. The remaining zero-cutoff-derivative term and gauge term are
the original jet functions at the same coordinate point. -/
theorem norm_localizedVacuumSourceRemainder_le
    (inv g g₀ : CoordinateSpace → Tensor2) (χ : CoordinateSpace → ℝ)
    (x : CoordinateSpace) (i j : Index)
    (B D e Q G C₀ C₁ C₂ : ℝ)
    (hB : 0 ≤ B) (hA : ‖inv x‖ ≤ B) (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂)
    (hVal : ‖g x i j - g₀ x i j‖ ≤ e)
    (hD : ∀ a, ‖scalarPartial (fun y => g y i j - g₀ y i j) a x‖ ≤ D)
    (hCut₀ : ‖χ x‖ ≤ C₀)
    (hCut₁ : ∀ a, ‖scalarPartial χ a x‖ ≤ C₁)
    (hCut₂ : ∀ a b, ‖scalarPartial (scalarPartial χ b) a x‖ ≤ C₂)
    (hQ : ‖projectedSourceFirstJetRemainder (inv x) (coordinateJet g x) (coordinateJet inv x) i j -
        scalarWaveAt (inv x) (fun y => g₀ y i j) x‖ ≤ Q)
    (hG : ∀ a, ‖coordinateGaugeCovector inv g x a‖ ≤ G) :
    ‖localizedVacuumSourceRemainder inv g g₀ χ x i j‖ ≤
      C₀ * Q + 16 * B * (C₂ * e + 2 * C₁ * D) + 2 * C₁ * G := by
  unfold localizedVacuumSourceRemainder
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans ?_
  simp only [norm_mul]
  rw [show 2 * C₁ * G = C₁ * G + C₁ * G by ring]
  exact add_le_add (add_le_add (mul_le_mul hCut₀ hQ (norm_nonneg _) h₀)
      (norm_localizedWaveError_le (inv x) χ (fun y => g y i j - g₀ y i j) x
        B D e C₁ C₂ hB hA h₁ h₂ hVal hD hCut₁ hCut₂))
    (add_le_add (mul_le_mul (hCut₁ i) (hG j) (norm_nonneg _) h₁)
      (mul_le_mul (hCut₁ j) (hG i) (norm_nonneg _) h₁))

end Burnett.C03
