import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualInputs
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualSpectrum
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinApplications

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.CenteredMaximal
open Burnett.Analysis.DyadicSquare (rescaleSymbol)
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.ShiftedFourierWindow (shifted_window_physical)
open Burnett.Analysis.SignedFourierWindow

open MeasureTheory Burnett.Fourier
open scoped ContDiff ENNReal FourierTransform

/-- Apply the genuine linear Mikhlin operator to the actual Schwartz-input
joint multiplier. Its Fourier realization multiplies at the sum frequency. -/
theorem joint_bilinear_outer_schwartz_bound (r : ℝ) (hr : 1 < r)
    (c : E → ℝ) (hc : ContDiffOn ℝ ∞ c {ξ | ξ ≠ 0})
    (hch : ∀ t : ℝ, 0 < t → ∀ ξ, c (t • ξ) = c ξ) :
    ∃ L : ℝ≥0∞, L < ⊤ ∧ ∃ D : ℝ, (∀ ξ, ‖c ξ‖ ≤ D) ∧
      ∀ (m : Joint → ℝ), Measurable m →
        ∀ (d : ℝ), (∀ y, ‖m y‖ ≤ d) → ∀ (f g : SchwartzMap E ℂ),
          MemLp (jointBilinear m f g) (ENNReal.ofReal r) volume →
          MemLp (jointBilinear (fun y => c (y.1 + y.2) * m y) f g) (ENNReal.ofReal r) volume ∧
            eLpNorm (jointBilinear (fun y => c (y.1 + y.2) * m y) f g) (ENNReal.ofReal r) volume ≤
              L * eLpNorm (jointBilinear m f g) (ENNReal.ofReal r) volume := by
  let P := ENNReal.ofReal r
  letI : Fact (1 ≤ P) := ⟨by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr.le⟩
  obtain ⟨M, S, C, hM, hS, agree, _⟩ := homogeneous_multiplier_all_Lp c hc hch r hr
  have mc : Measurable c := measurable_of_continuousOn_compl_singleton 0 hc.continuousOn
  refine ⟨ENNReal.ofReal (max C 0), ENNReal.ofReal_lt_top, M.bound, ?_, ?_⟩
  · intro ξ
    simpa only [hM, Complex.norm_real] using M.norm_le ξ
  intro m hm d hd f g hfg
  let u := jointBilinear m f g
  obtain ⟨h₂, ae⟩ := jointBilinear_fourierMultiplier_output m hm hd c mc M hM f g
  let v := hfg.toLp u
  have he : (S v : E → ℂ) =ᵐ[volume] jointBilinear (fun y => c (y.1 + y.2) * m y) f g :=
    (agree u h₂ hfg).trans ae
  have hR : ‖S v‖ ≤ max C 0 * ‖v‖ :=
    (hS v).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _))
  have hE : ‖S v‖ₑ ≤ ENNReal.ofReal (max C 0) * ‖v‖ₑ := by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (le_max_right C 0)]
    exact ENNReal.ofReal_le_ofReal hR
  refine ⟨(Lp.memLp (S v)).ae_eq he, ?_⟩
  rw [← eLpNorm_congr_ae he, ← Lp.enorm_def, ← Lp.enorm_toLp hfg]
  exact hE

/-- Keep the linear multiplier outside the joint multiplier in the Schwartz
estimate, then transfer the bound to the same actual product-frequency
integral for inputs with exact integrable spectra. -/
theorem joint_spectral_bilinear_outer_bound (p s r : ℝ) (hp : 1 < p) (hs : 1 < s) (hr : 1 < r)
    (he : r⁻¹ = p⁻¹ + s⁻¹)
    (m : Joint → ℝ) (hm : ContDiffOn ℝ ∞ m {y | y ≠ 0})
    (hmh : ∀ t : ℝ, 0 < t → ∀ y, m (t • y) = m y)
    (c : E → ℝ) (hc : ContDiffOn ℝ ∞ c {ξ | ξ ≠ 0})
    (hch : ∀ t : ℝ, 0 < t → ∀ ξ, c (t • ξ) = c ξ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (F G : E → ℂ),
      ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0} → ContDiffOn ℝ ∞ G {ξ | ξ ≠ 0} →
      Integrable F → Integrable G →
      MemLp (𝓕⁻ F) (ENNReal.ofReal p) volume → MemLp (𝓕⁻ G) (ENNReal.ofReal s) volume →
      MemLp (jointSpectralBilinear (fun y => c (y.1 + y.2) * m y) F G) (ENNReal.ofReal r) volume ∧
        eLpNorm (jointSpectralBilinear (fun y => c (y.1 + y.2) * m y) F G) (ENNReal.ofReal r) volume ≤
          C * (eLpNorm (𝓕⁻ F) (ENNReal.ofReal p) volume * eLpNorm (𝓕⁻ G) (ENNReal.ofReal s) volume) := by
  obtain ⟨mm, d, hd⟩ := homogeneous_joint_symbol_measurable_bounded m hm hmh
  obtain ⟨K, hK, bilinear⟩ := joint_bilinear_bound p s r hp hs hr he m hm hmh
  obtain ⟨L, hL, D, hD, outer⟩ := joint_bilinear_outer_schwartz_bound r hr c hc hch
  have mc : Measurable c := measurable_of_continuousOn_compl_singleton 0 hc.continuousOn
  let a := fun y : Joint => c (y.1 + y.2) * m y
  have ma : Measurable a := (mc.comp (measurable_fst.add measurable_snd)).mul mm
  have bA (y : Joint) : ‖a y‖ ≤ D * d := by
    change ‖c (y.1 + y.2) * m y‖ ≤ D * d
    rw [norm_mul]
    exact mul_le_mul (hD _) (hd y) (norm_nonneg _) ((norm_nonneg (c 0)).trans (hD 0))
  have fin := ENNReal.mul_lt_top hL hK
  refine ⟨L * K, fin, joint_spectral_bilinear_of_schwartz_bound hp hs a ma bA fin ?_⟩
  intro f g
  obtain ⟨mem, bnd⟩ := bilinear f g
  obtain ⟨hmul, bd⟩ := outer m mm d hd f g mem
  exact ⟨hmul, bd.trans ((mul_le_mul_left' bnd L).trans_eq (mul_assoc _ _ _).symm)⟩

end Burnett.A02.FrequencySplit
