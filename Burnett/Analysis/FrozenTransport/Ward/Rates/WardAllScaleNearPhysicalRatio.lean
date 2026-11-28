import Burnett.Analysis.AngularCaps.ParabolicProfileSmoothness

set_option autoImplicit false
set_option maxRecDepth 6400
set_option maxHeartbeats 4900000

noncomputable section

namespace Burnett.C02

open Set Burnett.Analysis.ProjectiveNullCaps
open scoped ContDiff

/-- Convert the physical ratio used by A05 to the radial ratio in the
common parabolic coordinates while retaining both Euclidean norms. -/
def wardParabolicRatioOfPhysical (F : NullCoordinateMap) (δ : ℝ)
    (u v : NullFrequencyCoordinates) (ρ : ℝ) : ℝ :=
  ρ * ‖F (parabolicDilation δ v)‖ / ‖F (parabolicDilation δ u)‖

theorem wardParabolicRatioOfPhysical_eq (F : NullCoordinateMap) (δ : ℝ)
    (u v : NullFrequencyCoordinates) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hu : F (parabolicDilation δ u) ≠ 0) (hv : F (parabolicDilation δ v) ≠ 0) :
    wardParabolicRatioOfPhysical F δ u v
        (‖ρ • F (parabolicDilation δ u)‖ / ‖F (parabolicDilation δ v)‖) = ρ := by
  unfold wardParabolicRatioOfPhysical
  rw [norm_smul, Real.norm_of_nonneg hρ, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv),
    mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hu)]

theorem wardParabolicRatioOfPhysical_contDiffOn {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (V : Set X)
    (F : X → NullCoordinateMap) (δ ρ : X → ℝ) (u v : X → NullFrequencyCoordinates)
    (hF : ContDiffOn ℝ ∞ F V) (hδ : ContDiffOn ℝ ∞ δ V) (hρ : ContDiffOn ℝ ∞ ρ V)
    (hu : ContDiffOn ℝ ∞ u V) (hv : ContDiffOn ℝ ∞ v V)
    (hNZ : ∀ x ∈ V, F x (parabolicDilation (δ x) (u x)) ≠ 0 ∧ F x (parabolicDilation (δ x) (v x)) ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => wardParabolicRatioOfPhysical (F x) (δ x) (u x) (v x) (ρ x)) V := by
  have hU := (hF.clm_apply (parabolicDilation_contDiffOn hδ hu)).norm ℝ (fun x hx => (hNZ x hx).1)
  have hV := (hF.clm_apply (parabolicDilation_contDiffOn hδ hv)).norm ℝ (fun x hx => (hNZ x hx).2)
  exact (hρ.mul hV).div hU (fun x hx => norm_ne_zero_iff.mpr (hNZ x hx).1)

end Burnett.C02
