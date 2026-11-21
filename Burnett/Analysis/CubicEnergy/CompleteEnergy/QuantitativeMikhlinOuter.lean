import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeMikhlin
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualOuter

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Metric Burnett.Fourier
open scoped ContDiff ENNReal FourierTransform

/-- The Mikhlin coefficient for the outer multiplier is linear in its sphere
jet, while the smooth joint symbol is fixed independently. The expression
remains the actual product-frequency integral on exact integrable spectra. -/
theorem joint_spectral_bilinear_outer_sphere_bound (p s r : ℝ) (hp : 1 < p) (hs : 1 < s)
    (hr : 1 < r) (he : r⁻¹ = p⁻¹ + s⁻¹)
    (m : Joint → ℝ) (hm : ContDiffOn ℝ ∞ m {y | y ≠ 0})
    (hmh : ∀ t : ℝ, 0 < t → ∀ y, m (t • y) = m y) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (c : E → ℝ), ContDiffOn ℝ ∞ c {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ ξ, c (t • ξ) = c ξ) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n c ξ‖ ≤ D) →
      ∀ (F G : E → ℂ), ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0} → ContDiffOn ℝ ∞ G {ξ | ξ ≠ 0} →
        Integrable F → Integrable G →
        MemLp (𝓕⁻ F) (ENNReal.ofReal p) volume → MemLp (𝓕⁻ G) (ENNReal.ofReal s) volume →
        MemLp (jointSpectralBilinear (fun y => c (y.1 + y.2) * m y) F G) (ENNReal.ofReal r) volume ∧
          eLpNorm (jointSpectralBilinear (fun y => c (y.1 + y.2) * m y) F G) (ENNReal.ofReal r) volume ≤
            C * ENNReal.ofReal D *
              (eLpNorm (𝓕⁻ F) (ENNReal.ofReal p) volume * eLpNorm (𝓕⁻ G) (ENNReal.ofReal s) volume) := by
  obtain ⟨mm,d,hd⟩ := homogeneous_joint_symbol_measurable_bounded m hm hmh
  obtain ⟨K,hK,bilinear⟩ := joint_bilinear_bound p s r hp hs hr he m hm hmh
  obtain ⟨L,hL,outer⟩ := homogeneous_multiplier_intersection_sphere_bound r hr
  refine ⟨L*K, ENNReal.mul_lt_top hL hK, ?_⟩
  intro c hc hch D hD jet
  obtain ⟨M,hM⟩ := mikhlin_bounded_symbol c hc hch
  have mc : Measurable c := measurable_of_continuousOn_compl_singleton 0 hc.continuousOn
  let a := fun y : Joint => c (y.1 + y.2) * m y
  have ma : Measurable a := (mc.comp (measurable_fst.add measurable_snd)).mul mm
  have bA (y : Joint) : ‖a y‖ ≤ M.bound * d := by
    change ‖c (y.1 + y.2) * m y‖ ≤ M.bound * d
    rw [norm_mul]
    have h := M.norm_le (y.1+y.2)
    rw [hM,Complex.norm_real] at h
    exact mul_le_mul h (hd y) (norm_nonneg _) M.bound_nonneg
  have fin : (L*K)*ENNReal.ofReal D < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top hL hK) ENNReal.ofReal_lt_top
  refine joint_spectral_bilinear_of_schwartz_bound hp hs a ma bA fin ?_
  intro f g
  obtain ⟨mem,bnd⟩ := bilinear f g
  obtain ⟨h₂,ae⟩ := jointBilinear_fourierMultiplier_output m mm hd c mc M hM f g
  obtain ⟨ret,bd⟩ := outer c hc hch D hD jet M hM (jointBilinear m f g) h₂ mem
  refine ⟨ret.ae_eq ae, ?_⟩
  rw [← eLpNorm_congr_ae ae]
  exact (bd.trans (mul_le_mul_left' bnd _)).trans_eq (by ring)

end Burnett.A02.FrequencySplit
