import Burnett.Counterexamples.RotatingNull.AngularHamilton
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace


noncomputable section
namespace Burnett.RotatingNullMoments.MeasureEstimates
open MeasureTheory Filter
open Burnett.RicciSymbol
open scoped ContDiff Topology BigOperators
abbrev Phase := Burnett.CubicExplicit.Space × Covector

def hamiltonValue (φ : Burnett.CubicExplicit.Space → ℝ) (p : Phase) : ℝ :=
  flatHamilton (separatedTest φ) p.1 p.2

def temporalValue (φ : Burnett.CubicExplicit.Space → ℝ) (p : Phase) : ℝ :=
  p.2 1 * p.2 2 * Burnett.CubicExplicit.D 0 φ p.1

def weightedValue (β : Burnett.CubicExplicit.Space → ℝ) (p : Phase) : ℝ :=
  (p.2 0)^2 * β p.1

theorem measurable_hamiltonValue (φ : Burnett.CubicExplicit.Space → ℝ)
    (hs : ContDiff ℝ ∞ φ) : Measurable (hamiltonValue φ) := by
  have hd (i : Index) : Measurable (fun p : Phase => Burnett.CubicExplicit.D i φ p.1) :=
    (((hs.continuous_fderiv (by simp)).clm_apply continuous_const).comp continuous_fst).measurable
  have hx (i : Index) : Measurable (fun p : Phase => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hF : Measurable oddAngular := by
    unfold oddAngular euclideanSquare
    fun_prop
  have heq : hamiltonValue φ = fun p : Phase => oddAngular p.2 *
      (-p.2 0 * Burnett.CubicExplicit.D 0 φ p.1 + p.2 1 * Burnett.CubicExplicit.D 1 φ p.1 +
        p.2 2 * Burnett.CubicExplicit.D 2 φ p.1 + p.2 3 * Burnett.CubicExplicit.D 3 φ p.1) := by
    funext p
    exact flatHamilton_separated_coordinates φ (hs.differentiable (by simp)) p.1 p.2
  rw [heq]
  exact (hF.comp measurable_snd).mul ((((hx 0).neg.mul (hd 0)).add ((hx 1).mul (hd 1))).add
    ((hx 2).mul (hd 2)) |>.add ((hx 3).mul (hd 3)))

theorem integrable_and_integral_error_bound
    (μ : Measure Phase) (φ β : Burnett.CubicExplicit.Space → ℝ) (hs : ContDiff ℝ ∞ φ)
    (hn : ∀ᵐ p ∂μ, p.2 ≠ 0 ∧ symbolNorm NullScreen.minkowskiInverse p.2 = 0)
    (hβ : ∀ x, (∑ j : Fin 3, |Burnett.CubicExplicit.D j.succ φ x|) ≤ β x)
    (ht : Integrable (temporalValue φ) μ) (hb : Integrable (weightedValue β) μ) :
    Integrable (hamiltonValue φ) μ ∧
      |(∫ p, hamiltonValue φ p ∂μ) - (∫ p, temporalValue φ p ∂μ)| ≤ ∫ p, weightedValue β p ∂μ := by
  have ha : ∀ᵐ p ∂μ, |hamiltonValue φ p - temporalValue φ p| ≤ weightedValue β p := by
    filter_upwards [hn] with p hp
    exact (flatHamilton_spatial_error_bound φ (hs.differentiable (by simp)) p.1 p.2 hp.1 hp.2).trans
      (mul_le_mul_of_nonneg_left (hβ p.1) (sq_nonneg _))
  have he : Integrable (fun p => hamiltonValue φ p - temporalValue φ p) μ :=
    hb.mono' ((measurable_hamiltonValue φ hs).aestronglyMeasurable.sub ht.aestronglyMeasurable)
      (by simpa only [Real.norm_eq_abs] using ha)
  have hh : Integrable (hamiltonValue φ) μ := (he.add ht).congr (by filter_upwards [] with p; simp)
  refine ⟨hh, ?_⟩
  rw [← integral_sub hh ht]
  calc
    _ ≤ ∫ p, ‖hamiltonValue φ p - temporalValue φ p‖ ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun p => hamiltonValue φ p - temporalValue φ p)
    _ ≤ _ := integral_mono_ae he.norm hb (by simpa only [Real.norm_eq_abs] using ha)

theorem temporal_integral_bound_of_transport
    (μ : Measure Phase) (φ β : Burnett.CubicExplicit.Space → ℝ) (hs : ContDiff ℝ ∞ φ)
    (hn : ∀ᵐ p ∂μ, p.2 ≠ 0 ∧ symbolNorm NullScreen.minkowskiInverse p.2 = 0)
    (hβ : ∀ x, (∑ j : Fin 3, |Burnett.CubicExplicit.D j.succ φ x|) ≤ β x)
    (ht : Integrable (temporalValue φ) μ) (hb : Integrable (weightedValue β) μ)
    (htransport : (∫ p, hamiltonValue φ p ∂μ) = 0) :
    |∫ p, temporalValue φ p ∂μ| ≤ ∫ p, weightedValue β p ∂μ := by
  simpa only [htransport, zero_sub, abs_neg] using
    (integrable_and_integral_error_bound μ φ β hs hn hβ ht hb).2

end Burnett.RotatingNullMoments.MeasureEstimates
