import Burnett.Analysis.PrincipalEnergy.Freezing.NestedPatchCutoffs
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedCoefficientDifference

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Set Filter Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal Topology

/-- The same fixed real profile supplies the two cutoff windows and the
actual localized coefficient differences at their corresponding scales. -/
theorem exists_nested_localized_coefficient_difference (R : ℝ) (hR : 0 ≤ R) :
    ∃ (χ : E → ℝ) (K : ℝ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ 0 ≤ K ∧
      (∀ (c : E) (s : ℝ), 0 < s →
        let θ : E → ℝ := fun x => χ (s⁻¹ • (x - c))
        ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
        (∀ x ∈ closedBall c ((R + 1) * s), θ x = 1) ∧
        tsupport θ ⊆ ball c ((R + 2) * s) ∧
        (∀ x ∈ ball c ((R + 1) * s), θ =ᶠ[𝓝 x] 1) ∧
        (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧
        (∀ x, ‖θ x‖ ≤ 1 ∧ ‖fderiv ℝ θ x‖ ≤ K / s ∧
          ‖iteratedFDeriv ℝ 0 θ x‖ ≤ 1 ∧ ‖iteratedFDeriv ℝ 1 θ x‖ ≤ K / s ∧
          ‖iteratedFDeriv ℝ 2 θ x‖ ≤ K / s ^ 2) ∧
        ∀ (C : E → ℝ), ContDiff ℝ ∞ C → ∀ (L : ℝ), 0 ≤ L →
          (∀ x ∈ closedBall c ((R + 2) * s), ‖fderiv ℝ C x‖ ≤ L) →
          let d := localizedCoefficientDifference θ C c
          ContDiff ℝ ∞ d ∧ HasCompactSupport d ∧ tsupport d ⊆ tsupport θ ∧
          (∀ x ∈ closedBall c ((R + 1) * s), d x = C x - C c) ∧
          (∀ x, ‖d x‖ ≤ L * ((R + 2) * s) ∧
            ‖fderiv ℝ d x‖ ≤ (1 + (R + 2) * K) * L) ∧
          eLpNorm d ⊤ volume ≤ ENNReal.ofReal (L * ((R + 2) * s)) ∧
          eLpNorm (fderiv ℝ d) ⊤ volume ≤ ENNReal.ofReal ((1 + (R + 2) * K) * L)) ∧
      ∀ (c : E) (ℓ : ℝ), 0 < ℓ →
        let θ : E → ℝ := fun x => χ (ℓ⁻¹ • (x - c))
        let Θ : E → ℝ := fun x => χ ((2 * ℓ)⁻¹ • (x - c))
        (∀ x ∈ closedBall c (R * ℓ), θ =ᶠ[𝓝 x] 1) ∧
        (∀ x ∈ tsupport θ, Θ =ᶠ[𝓝 x] 1) ∧
        ∀ (C : E → ℝ),
          let d := localizedCoefficientDifference θ C c
          let dOuter := localizedCoefficientDifference Θ C c
          θ * dOuter = d ∧
          (∀ x ∈ closedBall c (R * ℓ), d =ᶠ[𝓝 x] fun y => C y - C c) ∧
          (∀ x ∈ tsupport θ, dOuter =ᶠ[𝓝 x] fun y => C y - C c) := by
  obtain ⟨χ, K, hχ, hχc, hK, scaled, nested⟩ := exists_nested_patch_cutoffs R hR
  refine ⟨χ, K, hχ, hχc, hK, ?_, ?_⟩
  · intro c s hs θ
    obtain ⟨hθ, hθc, oneOnPlateau, support, nearPlateau, range, jets⟩ := scaled c s hs
    refine ⟨hθ, hθc, oneOnPlateau, support, nearPlateau, range, jets, ?_⟩
    intro C hC L hL hGrad d
    have hRadius : 0 ≤ R + 2 := by linarith
    have hSupport : tsupport d ⊆ tsupport θ := tsupport_mul_subset_left
    have hSmooth : ContDiff ℝ ∞ d := hθ.mul (hC.sub contDiff_const)
    have hCompact : HasCompactSupport d := hθc.of_isClosed_subset isClosed_closure hSupport
    have hPoint := localized_coefficient_difference_bounds θ C hθ hC c (R + 2) s L K
      hRadius hs hL hK (support.trans ball_subset_closedBall)
      (fun x => (jets x).1) (fun x => (jets x).2.1) hGrad
    have hNorms := localized_coefficient_difference_Linfty θ C hθ hC c (R + 2) s L K
      hRadius hs hL hK (support.trans ball_subset_closedBall)
      (fun x => (jets x).1) (fun x => (jets x).2.1) hGrad
    exact ⟨hSmooth, hCompact, hSupport,
      fun x hx => localized_coefficient_difference_on_core θ C c x (oneOnPlateau x hx),
      hPoint, hNorms.1, hNorms.2⟩
  · intro c ℓ hℓ θ Θ
    obtain ⟨nearInner, nearOuter⟩ := nested c ℓ hℓ
    refine ⟨nearInner, nearOuter, ?_⟩
    intro C d dOuter
    have nearInnerDiff (x : E) (hx : x ∈ closedBall c (R * ℓ)) :
        d =ᶠ[𝓝 x] fun y => C y - C c :=
      (nearInner x hx).mono fun y hy => localized_coefficient_difference_on_core θ C c y hy
    have nearOuterDiff (x : E) (hx : x ∈ tsupport θ) :
        dOuter =ᶠ[𝓝 x] fun y => C y - C c :=
      (nearOuter x hx).mono fun y hy => localized_coefficient_difference_on_core Θ C c y hy
    refine ⟨?_, nearInnerDiff, nearOuterDiff⟩
    funext x
    change θ x * dOuter x = θ x * (C x - C c)
    by_cases hx : x ∈ tsupport θ
    · rw [(nearOuterDiff x hx).eq_of_nhds]
    · rw [show θ x = 0 from image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

end Burnett.A03
