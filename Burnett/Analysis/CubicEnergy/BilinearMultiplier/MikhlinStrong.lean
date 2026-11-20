import Burnett.Analysis.CubicEnergy.JointMultiplier.MikhlinPartition
import Burnett.Analysis.Microlocal.AngularCommutator.FrequencyKernel

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Filter Burnett.Fourier
open scoped Topology ContDiff ENNReal

theorem mikhlin_bounded_symbol (m : E → ℝ) (hm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ ξ, m (t • ξ) = m ξ) :
    ∃ M : BoundedSymbol E, ∀ ξ, M ξ = (m ξ : ℂ) := by
  obtain ⟨C,_,b⟩ := degreeZero_derivative_bounds m hm hh 0
  let D := max C ‖m 0‖
  have bound (ξ : E) : ‖(m ξ : ℂ)‖ ≤ D := by
    rw [Complex.norm_real]
    by_cases h : ξ=0
    · simpa only [h] using le_max_right C ‖m 0‖
    · exact (by simpa using b ξ h : ‖m ξ‖ ≤ C).trans (le_max_left _ _)
  have hsm : ContDiffOn ℝ ∞ (fun ξ => (m ξ : ℂ)) ({0}ᶜ : Set E) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hm
  exact ⟨⟨_, (Burnett.Microlocal.AngularCommutator.measurable_of_angular_smooth _ hsm).aestronglyMeasurable,
    D,(norm_nonneg _).trans (le_max_right _ _),bound⟩, fun _ => rfl⟩

/-- L² convergence for uniformly bounded symbols which stabilize almost everywhere,
including their inverse Fourier transforms. -/
theorem mikhlin_strong_L2 (M : BoundedSymbol E) (A : ℕ → BoundedSymbol E)
    (D : ℝ) (hd : ∀ n ξ, ‖A n ξ‖ ≤ D)
    (he : ∀ᵐ ξ ∂(volume : Measure E), ∀ᶠ n : ℕ in atTop, A n ξ = M ξ) (f : ComplexL2 E) :
    Tendsto (fun n => fourierMultiplier (A n) f) atTop (𝓝 (fourierMultiplier M f)) := by
  let F := fourierL2Equiv f
  let g := fun (n : ℕ) (ξ : E) => ‖(A n ξ - M ξ)*F ξ‖^2
  have hi : Integrable (fun ξ => ‖F ξ‖^2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)
  have conv : Tendsto (fun n => ∫ ξ, g n ξ) atTop (𝓝 0) := by
    have lim := tendsto_integral_of_dominated_convergence (μ := (volume : Measure E))
      (F := g) (f := fun _ => (0:ℝ)) (fun ξ => (D+M.bound)^2 * ‖F ξ‖^2)
      (fun n => ((((A n).measurable.sub M.measurable).mul (Lp.aestronglyMeasurable F)).norm.pow 2))
      (hi.const_mul _) (fun n => Eventually.of_forall fun ξ => ?_)
      (he.mono fun ξ h => tendsto_const_nhds.congr' (h.mono fun n hn => by simp [g,hn]))
    · simpa only [integral_zero] using lim
    · have b := (norm_sub_le (A n ξ) (M ξ)).trans (add_le_add (hd n ξ) (M.norm_le ξ))
      simp only [g,Real.norm_of_nonneg (sq_nonneg _),norm_mul,mul_pow]
      exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans b)).mpr b)
        (sq_nonneg _)
  have eq (n : ℕ) : ‖symbolL2 (A n) F - symbolL2 M F‖^2 = ∫ ξ, g n ξ := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (symbolL2 (A n) F) (symbolL2 M F),symbolL2_ae (A n) F,symbolL2_ae M F] with ξ hs h₁ h₂
    simp only [hs,Pi.sub_apply,h₁,h₂,g,sub_mul]
  have sub : Tendsto (fun n => symbolL2 (A n) F - symbolL2 M F) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h : Tendsto (fun n => ‖symbolL2 (A n) F - symbolL2 M F‖^2) atTop (𝓝 0) := by simpa only [eq] using conv
    simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using h.sqrt
  have lim := tendsto_sub_nhds_zero_iff.mp sub
  exact fourierL2Equiv.symm.continuous.continuousAt.tendsto.comp lim

end Burnett.A02.FrequencySplit
