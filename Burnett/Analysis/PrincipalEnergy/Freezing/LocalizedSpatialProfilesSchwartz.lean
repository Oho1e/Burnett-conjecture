import Burnett.Analysis.PrincipalEnergy.Freezing.WeightedSpatialProfileSums
import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedCubicEnergyDerivative

set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section

namespace Burnett.A03

open Metric Set MeasureTheory Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff ComplexConjugate ENNReal RealInnerProductSpace

/-- Index the two actual physical spatial profiles by their real phase. -/
def localizedRealSpatialModeProfile (P : ℝ) (k : Index → ℤ) (ρ : CoordinateSpace → ℝ)
    (c : CoordinateSpace) (ℓ : ℝ) (j : Fin 2) : CoordinateSpace → ℝ :=
  if j = 0 then localizedSpatialCosineProfile P k ρ c ℓ else localizedSpatialSineProfile P k ρ c ℓ

private theorem scaled_cutoff_support
    (P : ℝ) (ρ : CoordinateSpace → ℝ) (hρ : tsupport ρ ⊆ ball (0 : CoordinateSpace) P)
    (c : CoordinateSpace) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    HasCompactSupport (fun x : CoordinateSpace => ρ (ℓ⁻¹ • (x - c))) := by
  apply (isCompact_closedBall c (P * ℓ)).of_isClosed_subset isClosed_closure
  refine closure_minimal ?_ isClosed_closedBall
  intro x hx
  have h : ℓ⁻¹ • (x - c) ∈ ball (0 : CoordinateSpace) P := hρ (subset_closure hx)
  have scale : ‖ℓ⁻¹ • (x - c)‖ = dist x c / ℓ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le), dist_eq_norm, div_eq_inv_mul]
  rw [mem_ball, dist_zero_right, scale] at h
  exact mem_closedBall.mpr ((div_le_iff₀ hℓ).mp h.le)

private theorem real_spatial_mode_smooth_compact
    (P : ℝ) (k : Index → ℤ) (ρ : CoordinateSpace → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hSupport : tsupport ρ ⊆ ball (0 : CoordinateSpace) P) (c : CoordinateSpace)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (j : Fin 2) :
    let f := localizedRealSpatialModeProfile P k ρ c ℓ j
    ContDiff ℝ ∞ f ∧ HasCompactSupport f := by
  intro f
  let θ (x : CoordinateSpace) := ℓ⁻¹ • (x - c)
  have hθ : ContDiff ℝ ∞ θ := (contDiff_id.sub contDiff_const).const_smul ℓ⁻¹
  have hPhase : ContDiff ℝ ∞ (spatialModePhase P k) := by
    let L : CoordinateSpace →L[ℝ] ℝ := (2 * Real.pi) • innerSL ℝ (spatialModeFrequency P k)
    have eq : (L : CoordinateSpace → ℝ) = spatialModePhase P k := by
      funext y
      unfold L spatialModePhase
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply, real_inner_comm]
    rw [← eq]
    exact L.contDiff
  have hCut := scaled_cutoff_support P ρ hSupport c ℓ hℓ
  by_cases hj : j = 0
  · change ContDiff ℝ ∞ (localizedRealSpatialModeProfile P k ρ c ℓ j) ∧
      HasCompactSupport (localizedRealSpatialModeProfile P k ρ c ℓ j)
    rw [localizedRealSpatialModeProfile, if_pos hj]
    exact ⟨(hρ.comp hθ).mul ((Real.contDiff_cos.comp hPhase).comp hθ), hCut.mul_right⟩
  · change ContDiff ℝ ∞ (localizedRealSpatialModeProfile P k ρ c ℓ j) ∧
      HasCompactSupport (localizedRealSpatialModeProfile P k ρ c ℓ j)
    rw [localizedRealSpatialModeProfile, if_neg hj]
    exact ⟨(hρ.comp hθ).mul ((Real.contDiff_sin.comp hPhase).comp hθ), hCut.mul_right⟩

/-- The same compactly supported spatial profile, viewed as a real-valued
Schwartz multiplier with complex codomain. -/
def localizedRealSpatialModeSchwartz
    (P : ℝ) (k : Index → ℤ) (ρ : CoordinateSpace → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hSupport : tsupport ρ ⊆ ball (0 : CoordinateSpace) P) (c : CoordinateSpace)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (j : Fin 2) : SchwartzMap CoordinateSpace ℂ :=
  let h := real_spatial_mode_smooth_compact P k ρ hρ hSupport c ℓ hℓ j
  (h.2.comp_left (g := Complex.ofReal) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp h.1)

theorem localized_real_spatial_mode_schwartz_apply
    (P : ℝ) (k : Index → ℤ) (ρ : CoordinateSpace → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hSupport : tsupport ρ ⊆ ball (0 : CoordinateSpace) P) (c : CoordinateSpace)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (j : Fin 2) (x : CoordinateSpace) :
    localizedRealSpatialModeSchwartz P k ρ hρ hSupport c ℓ hℓ j x =
      (localizedRealSpatialModeProfile P k ρ c ℓ j x : ℂ) := rfl

/-- Leading profile factors use the same actual jet norm before and after
embedding the real test multiplier in the complex Schwartz space. -/
theorem localized_real_spatial_mode_schwartz_Linfinity
    (P : ℝ) (k : Index → ℤ) (ρ : CoordinateSpace → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hSupport : tsupport ρ ⊆ ball (0 : CoordinateSpace) P) (c : CoordinateSpace)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (j : Fin 2) (r : ℕ) :
    let f := localizedRealSpatialModeSchwartz P k ρ hρ hSupport c ℓ hℓ j
    (eLpNorm (iteratedFDeriv ℝ r (f : CoordinateSpace → ℂ)) ⊤ volume).toReal =
      spatialProfileJetLInfinity r (localizedRealSpatialModeProfile P k ρ c ℓ j) := by
  intro f
  rw [spatialProfileJetLInfinity, eLpNorm_exponent_top]
  congr 1
  rw [← eLpNorm_exponent_top, ← eLpNorm_exponent_top]
  apply eLpNorm_congr_norm_ae
  apply Filter.Eventually.of_forall
  intro x
  have h := real_spatial_mode_smooth_compact P k ρ hρ hSupport c ℓ hℓ j
  exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left h.1.contDiffAt (by exact_mod_cast le_top)

end Burnett.A03
