import Burnett.Analysis.PrincipalEnergy.Paraproduct.ParaproductMassEstimates
import Burnett.Analysis.PrincipalEnergy.Paraproduct.ActualParaproductResolution

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Burnett.Analysis.FirstOrderDyadic
open scoped Topology ContDiff

/-- The expanding tests used for the actual commutator are honest Schwartz
inputs at every finite cutoff radius. -/
def expandingTestSchwartz (χ : SchwartzMap Space ℂ) (hχ : HasCompactSupport (χ : Space → ℂ))
    (n : ℕ) : SchwartzMap Space ℂ := by
  let R : ℝ := (n:ℝ)+1
  have hR : 0<R := by unfold R; positivity
  let e : Space ≃ₜ Space := Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne')
  have hc : HasCompactSupport (fun x : Space => χ (R⁻¹ • x)) := hχ.comp_homeomorph e
  have hSmooth : ContDiff ℝ ∞ (χ : Space → ℂ) := χ.smooth _
  exact hc.toSchwartzMap (hSmooth.comp (contDiff_const.smul contDiff_id))

@[simp] theorem expandingTestSchwartz_apply (χ : SchwartzMap Space ℂ)
    (hχ : HasCompactSupport (χ : Space → ℂ)) (n : ℕ) (x : Space) :
    expandingTestSchwartz χ hχ n x = expandingInput χ ((n:ℝ)+1) x := rfl

private theorem wavelet_window_eq_mass_of_local_one (φ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (s : ℝ) (hs : 0<s) (x : Space) {f : Space → ℂ}
    (hLoc : ∀ y, ‖x-y‖≤s → f y=1) :
    compactWaveletAction φ s f x = ∫ z, φ z := by
  rw [← compactWaveletAction_one φ s hs x]
  unfold compactWaveletAction
  apply congrArg (fun g : Space → ℂ => ∫ y, g y)
  funext y
  by_cases hy : ‖x-y‖≤s
  · rw [hLoc y hy]
  · have hT : 1<‖s⁻¹ • (x-y)‖ := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le),← div_eq_inv_mul]
      exact (lt_div_iff₀ hs).mpr (by simpa only [one_mul] using lt_of_not_ge hy)
    simp only [compactWaveletKernel,hφ _ hT,smul_zero,zero_mul]

/-- Averaging the expanding constant test is uniformly bounded at all
scales and becomes exactly one at every fixed point and fixed scale. -/
theorem compactWaveletAction_expandingInput_profile (φ : SchwartzMap Space ℂ)
    (hφ : ∀ z, 1<‖z‖ → φ z=0) (hφ₁ : (∫ z, φ z)=1) (χ : SchwartzMap Space ℂ)
    (hχ₁ : ∀ x : Space, ‖x‖≤1 → χ x=1) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : ℝ), 0<s → ∀ x : Space,
      (∀ n : ℕ, ‖compactWaveletAction φ s (expandingInput χ ((n:ℝ)+1)) x‖≤C) ∧
      (fun n : ℕ => compactWaveletAction φ s (expandingInput χ ((n:ℝ)+1)) x)
        =ᶠ[atTop] fun _ => 1 := by
  let K := SchwartzMap.seminorm ℝ 0 0 χ
  let V := ∫ z : Space, ‖φ z‖
  refine ⟨K*V,mul_nonneg (apply_nonneg _ _) (integral_nonneg fun _ => norm_nonneg _),?_⟩
  intro s hs x
  refine ⟨fun n => compactWaveletAction_norm_le_L1Mass_mul φ s hs
    (fun y => SchwartzMap.norm_le_seminorm ℝ χ (((n:ℝ)+1)⁻¹ • y)) x,?_⟩
  obtain ⟨N,hN⟩ := exists_nat_ge (‖x‖+s)
  filter_upwards [eventually_ge_atTop N] with n hn
  let R : ℝ := (n:ℝ)+1
  have hR : 0<R := by unfold R; positivity
  have hCast : (N:ℝ)≤n := by exact_mod_cast hn
  rw [← hφ₁]
  apply wavelet_window_eq_mass_of_local_one φ hφ s hs x
  intro y hy
  have hSmall : ‖y‖≤R := by
    have hY := norm_add_le (y-x) x
    rw [sub_add_cancel,norm_sub_rev] at hY
    unfold R
    linarith
  have hScale : ‖R⁻¹ • y‖≤1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR.le),← div_eq_inv_mul]
    exact (div_le_one hR).mpr hSmall
  exact hχ₁ _ hScale

end Burnett.Analysis.CarlesonEmbedding
