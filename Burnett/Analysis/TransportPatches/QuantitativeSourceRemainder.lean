import Burnett.Analysis.TransportPatches.SourceJetConstants
import Burnett.Analysis.GaugeProjection.ProjectedVacuumSourceOnChart

/-! The real localized vacuum remainder has the C03 scale bound with
constants depending on the common jet region and fixed cutoff profiles. -/
set_option autoImplicit false
set_option maxRecDepth 3800
set_option maxHeartbeats 4400000

noncomputable section

namespace Burnett.C03

open Set Burnett.P01 Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped ContDiff

/-- The scale-explicit bound on the true remainder after extraction of the
symmetrized gauge derivative. The two-cutoff loss multiplies the actual
original metric difference. -/
theorem exists_localizedSourceRemainder_scale_bound
    (B C₀ C₁ C₂ : ℝ) (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ χ : CoordinateSpace → ℝ,
      ∀ x, ‖χ x‖ ≤ C₀ →
      (∀ a, ‖scalarPartial χ a x‖ ≤ C₁ * ℓ⁻¹) →
      (∀ a b, ‖scalarPartial (scalarPartial χ b) a x‖ ≤ C₂ * (ℓ⁻¹)^2) →
      ∀ inv g g₀ : CoordinateSpace → Tensor2,
        DifferentiableComponentsAt g x → DifferentiableComponentsAt g₀ x →
        ‖localizedSourceJets inv g g₀ x‖ ≤ B →
        ∀ e : ℝ, 0 ≤ e → ‖g x - g₀ x‖ ≤ e → ∀ i j,
          ‖localizedVacuumSourceRemainder inv g g₀ χ x i j‖ ≤
            C * (1 + ℓ⁻¹ + (ℓ⁻¹)^2 * e) := by
  obtain ⟨R, hR₀, hR⟩ := exists_uncutSource_uniform_bound B
  let M := max 0 B
  let s₀ := C₀ * R
  let s₁ := 32 * M ^ 2 * C₁ + 2 * C₁ * R
  let s₂ := 16 * M * C₂
  let C := s₀ + s₁ + s₂
  have hM : 0 ≤ M := le_max_left _ _
  have hs₀ : 0 ≤ s₀ := by dsimp [s₀]; positivity
  have hs₁ : 0 ≤ s₁ := by dsimp [s₁]; positivity
  have hs₂ : 0 ≤ s₂ := by dsimp [s₂]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ℓ hℓ χ x hCut₀ hCut₁ hCut₂ inv g g₀ hg hg₀ hBound e he hError i j
  have hP : ‖localizedSourceJets inv g g₀ x‖ ≤ M := hBound.trans (le_max_right _ _)
  have hA : ‖inv x‖ ≤ M := (norm_fst_le _).trans hP
  have hDiffJet : ‖coordinateJet g x - coordinateJet g₀ x‖ ≤ M := by
    exact (norm_fst_le (localizedSourceJets inv g g₀ x).2.2.2.2).trans
      ((norm_snd_le _).trans ((norm_snd_le _).trans ((norm_snd_le _).trans
        ((norm_snd_le _).trans hP))))
  have hVal : ‖g x i j - g₀ x i j‖ ≤ e :=
    ((norm_le_pi_norm ((g x - g₀ x) i) j).trans
      (norm_le_pi_norm (g x - g₀ x) i)).trans hError
  have hDy (a : Index) : ‖scalarPartial (fun y => g y i j - g₀ y i j) a x‖ ≤ M := by
    simp only [scalarPartial, fderiv_fun_sub (hg i j) (hg₀ i j), ContinuousLinearMap.sub_apply]
    let T := coordinateJet g x - coordinateJet g₀ x
    change ‖T a i j‖ ≤ M
    exact ((norm_le_pi_norm (T a i) j).trans ((norm_le_pi_norm (T a) i).trans
      (norm_le_pi_norm T a))).trans hDiffJet
  have hInv : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
  have hε : 0 ≤ (ℓ⁻¹)^2 * e := mul_nonneg (sq_nonneg _) he
  calc
    _ ≤ C₀ * R + 16 * M * ((C₂ * (ℓ⁻¹)^2) * e + 2 * (C₁ * ℓ⁻¹) * M) +
        2 * (C₁ * ℓ⁻¹) * R :=
      norm_localizedVacuumSourceRemainder_le inv g g₀ χ x i j M M e R R C₀
        (C₁ * ℓ⁻¹) (C₂ * (ℓ⁻¹)^2) hM hA h₀ (mul_nonneg h₁ hInv)
        (mul_nonneg h₂ (sq_nonneg _)) hVal hDy hCut₀ hCut₁ hCut₂
        ((hR inv g g₀ x hBound).1 i j) (hR inv g g₀ x hBound).2
    _ = s₀ + s₁ * ℓ⁻¹ + s₂ * ((ℓ⁻¹)^2 * e) := by
      dsimp [s₀, s₁, s₂]
      ring
    _ ≤ C + C * ℓ⁻¹ + C * ((ℓ⁻¹)^2 * e) := by
      dsimp [C]
      gcongr <;> linarith
    _ = _ := by ring

end Burnett.C03
