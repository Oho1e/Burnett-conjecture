import Burnett.Analysis.PrincipalEnergy.Commutator.LocalOscillationRamp

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Set Metric Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff

/-- A single fixed scalar Schwartz cutoff supplies the oscillation split at
every centre and radius. The derivative constant refers only to this cutoff. -/
theorem exists_standardOscillationCutoff :
    ∃ (χ : SchwartzMap E ℂ) (D : ℝ), 0 ≤ D ∧ HasCompactSupport (χ : E → ℂ) ∧
      tsupport (χ : E → ℂ) ⊆ closedBall 0 2 ∧
      (∀ y : E, ‖y‖ ≤ 1 → χ y = 1) ∧ (∀ y : E, ‖χ y‖ ≤ 1) ∧
      (∀ y : E, ‖1-χ y‖ ≤ 1) ∧ (∀ y : E, ‖fderiv ℝ (χ : E → ℂ) y‖ ≤ D) := by
  let b : ContDiffBump (0 : E) := ⟨1,2,by norm_num,by norm_num⟩
  let q (y : E) : ℂ := (b y : ℂ)
  have hComp : HasCompactSupport q := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hSmooth : ContDiff ℝ ∞ q := Complex.ofRealCLM.contDiff.comp b.contDiff
  let χ := hComp.toSchwartzMap hSmooth
  have hAs (y : E) : χ y = (b y : ℂ) := rfl
  have hDerivative : Continuous (fderiv ℝ q) := hSmooth.continuous_fderiv (by simp)
  obtain ⟨x,hM⟩ := hDerivative.norm.exists_forall_ge_of_hasCompactSupport ((hComp.fderiv ℝ).norm)
  refine ⟨χ,‖fderiv ℝ q x‖,norm_nonneg _,hComp,?_,?_,?_,?_,?_⟩
  · apply closure_minimal _ isClosed_closedBall
    intro y hy
    by_contra hz
    have hd : 2 ≤ dist y (0 : E) := (not_le.mp (by simpa only [mem_closedBall] using hz)).le
    exact hy (by rw [hAs,b.zero_of_le_dist hd,Complex.ofReal_zero])
  · intro y hy
    have hm : y ∈ closedBall (0:E) b.rIn := by simpa only [mem_closedBall,dist_zero_right,b] using hy
    rw [hAs,b.one_of_mem_closedBall hm,Complex.ofReal_one]
  · intro y
    rw [hAs,Complex.norm_real,Real.norm_of_nonneg b.nonneg]
    exact b.le_one
  · intro y
    rw [hAs,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.mpr b.le_one)]
    linarith only [b.nonneg (x := y)]
  · exact hM

end Burnett.Analysis.FirstOrderDyadic
