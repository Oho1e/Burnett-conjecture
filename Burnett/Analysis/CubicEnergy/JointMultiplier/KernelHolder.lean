import Burnett.Analysis.CubicEnergy.FourierPairing
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Group.Prod

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory
open scoped ENNReal

private theorem shifted_norm (f : SchwartzMap E ℂ) (y : E) (p : ℝ≥0∞) :
    eLpNorm (fun x => f (x-y)) p volume = eLpNorm (f : E → ℂ) p volume := by
  simpa only [Function.comp_def,sub_eq_add_neg] using
    (eLpNorm_comp_measurePreserving (p := p) (f.continuous.aestronglyMeasurable (μ := volume))
      (measurePreserving_add_right (volume : Measure E) (-y)))

private theorem product_bound {p s r : ℝ≥0∞} [ENNReal.HolderTriple p s r] (f g : E → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    eLpNorm (fun x => f x * g x) r volume ≤ eLpNorm f p volume * eLpNorm g s volume :=
  eLpNorm_smul_le_mul_eLpNorm (φ := f) (f := g) (p := p) (q := s) (r := r)
    hg.aestronglyMeasurable hf.aestronglyMeasurable

/-- The triple integral of absolute values is uniform in the two independent translations. -/
theorem translated_triple_bound {p s r t : ℝ≥0∞} [ENNReal.HolderTriple p s r]
    [ENNReal.HolderTriple r t 1] (f v w : SchwartzMap E ℂ) (y z : E) :
    (∫⁻ x, ‖f (x-y) * v (x-z) * w x‖ₑ) ≤
      eLpNorm (f : E → ℂ) p volume * eLpNorm (v : E → ℂ) s volume * eLpNorm (w : E → ℂ) t volume := by
  let F := fun x : E => f (x-y)
  let V := fun x : E => v (x-z)
  have hF : Continuous F := f.continuous.comp (continuous_id.sub continuous_const)
  have hV : Continuous V := v.continuous.comp (continuous_id.sub continuous_const)
  rw [← eLpNorm_one_eq_lintegral_enorm]
  exact (product_bound (p := r) (s := t) (fun x => F x*V x) w (hF.mul hV) w.continuous).trans <|
    mul_le_mul_right' (by simpa only [F,V,shifted_norm] using product_bound (p := p) (s := s) (r := r) F V hF hV) _

/-- Normalized kernel at any scale. Dilations are taken in the input
translations, so the constant is the L¹ mass of one reference kernel. -/
theorem dilated_kernel_trilinear_bound {p s r t : ℝ≥0∞} [ENNReal.HolderTriple p s r]
    [ENNReal.HolderTriple r t 1] (K : Joint → ℂ) (hK : Measurable K)
    (f v w : SchwartzMap E ℂ) (scale : ℝ) :
    (∫⁻ y : Joint, ∫⁻ x, ‖K y * (f (x-scale • y.1) * v (x-scale • y.2) * w x)‖ₑ) ≤
      (∫⁻ y, ‖K y‖ₑ) * (eLpNorm (f : E → ℂ) p volume * eLpNorm (v : E → ℂ) s volume *
        eLpNorm (w : E → ℂ) t volume) := by
  rw [← lintegral_mul_const'' _ hK.enorm.aemeasurable]
  apply lintegral_mono
  intro y
  simp only [enorm_mul]
  rw [lintegral_const_mul' _ _ (by finiteness)]
  simp_rw [← enorm_mul]
  exact mul_le_mul_left' (translated_triple_bound (p := p) (s := s) (r := r) (t := t) f v w _ _) _

end Burnett.A02.FrequencySplit
