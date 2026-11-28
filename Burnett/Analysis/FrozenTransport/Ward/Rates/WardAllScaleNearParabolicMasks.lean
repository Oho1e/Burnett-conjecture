import Burnett.Analysis.AngularCaps.ParabolicProfileSmoothness
import Burnett.Analysis.AngularCaps.ProjectiveWedgeCaps
import Burnett.Analysis.AngularCaps.WedgeTriad

set_option autoImplicit false
set_option maxRecDepth 6200
set_option maxHeartbeats 4900000

noncomputable section

namespace Burnett.C02

open Set Burnett.Analysis.ProjectiveNullCaps
open scoped ContDiff

def wardParabolicAngularNearWeight (ϑ : ℝ → ℝ) (F : NullCoordinateMap) (δ : ℝ)
    (u v w : NullFrequencyCoordinates) : ℝ :=
  ϑ (parabolicWedgeRatio F δ u v) * ϑ (parabolicWedgeRatio F δ u w)

theorem wardParabolicAngularNearWeight_contDiffOn {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (V : Set X)
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (F : X → NullCoordinateMap) (δ : X → ℝ)
    (u v w : X → NullFrequencyCoordinates)
    (hF : ContDiffOn ℝ ∞ F V) (hδ : ContDiffOn ℝ ∞ δ V)
    (hu : ContDiffOn ℝ ∞ u V) (hv : ContDiffOn ℝ ∞ v V) (hw : ContDiffOn ℝ ∞ w V)
    (hNZ : ∀ x ∈ V, F x (parabolicDilation (δ x) (u x)) ≠ 0 ∧
      F x (parabolicDilation (δ x) (v x)) ≠ 0 ∧ F x (parabolicDilation (δ x) (w x)) ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => wardParabolicAngularNearWeight ϑ (F x) (δ x) (u x) (v x) (w x)) V := by
  have hq := parabolicWedgeRatio_contDiffOn hF hδ hu hv (fun x hx => ⟨(hNZ x hx).1,(hNZ x hx).2.1⟩)
  have hr := parabolicWedgeRatio_contDiffOn hF hδ hu hw (fun x hx => ⟨(hNZ x hx).1,(hNZ x hx).2.2⟩)
  exact (hϑ.comp_contDiffOn hq).mul (hϑ.comp_contDiffOn hr)

/-- The actual near angular cutoff on the first low slot retains its
two scaled wedge ratios and extends through zero cap width. -/
theorem wardParabolicAngularNearWeight_eq_actual (ϑ : ℝ → ℝ) (F : NullCoordinateMap)
    (δ : ℝ) (hδ : δ ≠ 0) (u v w : NullFrequencyCoordinates) :
    wardParabolicAngularNearWeight ϑ F δ u v w =
      angularNearWeight ϑ δ (F (parabolicDilation δ u)) (F (parabolicDilation δ v))
        (F (parabolicDilation δ w)) := by
  unfold wardParabolicAngularNearWeight angularNearWeight
  rw [projectiveWedgeSq_parabolic_div F hδ, projectiveWedgeSq_parabolic_div F hδ]

theorem wardParabolicAngularNearWeight_eq_scaled_low (ϑ : ℝ → ℝ) (F : NullCoordinateMap)
    (δ : ℝ) (hδ : δ ≠ 0) (ρ : ℝ) (hρ : ρ ≠ 0) (u v w : NullFrequencyCoordinates) :
    wardParabolicAngularNearWeight ϑ F δ u v w =
      angularNearWeight ϑ δ (ρ • F (parabolicDilation δ u)) (F (parabolicDilation δ v))
        (-(F (parabolicDilation δ w))) := by
  rw [wardParabolicAngularNearWeight_eq_actual ϑ F δ hδ u v w]
  unfold angularNearWeight
  rw [projectiveWedgeSq_smul_left ρ hρ, projectiveWedgeSq_smul_left ρ hρ, projectiveWedgeSq_neg_right]

def wardParabolicLowSlotWeight (ϑ : ℝ → ℝ) (F : NullCoordinateMap) (δ κ ρ : ℝ)
    (u v w : NullFrequencyCoordinates) : ℝ :=
  ϑ ((ρ^2 * ‖F (parabolicDilation δ u)‖^2) /
    (κ^2 * (‖F (parabolicDilation δ v)‖^2 + ‖F (parabolicDilation δ w)‖^2)))

/-- The actual radial cutoff written without any division by the low
frequency. This expression includes the zero radial ratio. -/
theorem wardParabolicLowSlotWeight_eq_actual (ϑ : ℝ → ℝ) (F : NullCoordinateMap)
    (δ κ ρ : ℝ) (u v w : NullFrequencyCoordinates) :
    wardParabolicLowSlotWeight ϑ F δ κ ρ u v w =
      lowSlotWeight ϑ κ (ρ • F (parabolicDilation δ u))
        (F (parabolicDilation δ v)) (F (parabolicDilation δ w)) := by
  unfold wardParabolicLowSlotWeight lowSlotWeight
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem wardParabolicLowSlotWeight_contDiffOn {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (V : Set X)
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (F : X → NullCoordinateMap) (δ κ ρ : X → ℝ)
    (u v w : X → NullFrequencyCoordinates)
    (hF : ContDiffOn ℝ ∞ F V) (hδ : ContDiffOn ℝ ∞ δ V)
    (hκ : ContDiffOn ℝ ∞ κ V) (hρ : ContDiffOn ℝ ∞ ρ V)
    (hu : ContDiffOn ℝ ∞ u V) (hv : ContDiffOn ℝ ∞ v V) (hw : ContDiffOn ℝ ∞ w V)
    (hNZ : ∀ x ∈ V, κ x ≠ 0 ∧ F x (parabolicDilation (δ x) (v x)) ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => wardParabolicLowSlotWeight ϑ (F x) (δ x) (κ x) (ρ x) (u x) (v x) (w x)) V := by
  have D (z : X → NullFrequencyCoordinates) (hz : ContDiffOn ℝ ∞ z V) :
      ContDiffOn ℝ ∞ (fun x => ‖F x (parabolicDilation (δ x) (z x))‖^2) V :=
    (hF.clm_apply (parabolicDilation_contDiffOn hδ hz)).norm_sq ℝ
  refine hϑ.comp_contDiffOn (((hρ.pow 2).mul (D u hu)).div
    ((hκ.pow 2).mul ((D v hv).add (D w hw))) (fun x hx => ?_))
  exact mul_ne_zero (pow_ne_zero _ (hNZ x hx).1)
    (ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (hNZ x hx).2)) (sq_nonneg _)))

end Burnett.C02
