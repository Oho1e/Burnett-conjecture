import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.NormNum

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.NearDiagonal

open Set MeasureTheory Filter
open scoped Topology ENNReal

abbrev Euclidean4 := EuclideanSpace ℝ (Fin 4)

/-- The radial profile of the four-dimensional inverse-cube envelope inside a
punctured ball. -/
def inverseCubeProfile (δ : ℝ) (s : ℝ) : ℝ :=
  (Set.Ioo 0 δ).indicator (fun r => (r ^ 3)⁻¹) s

def inverseCubeEnvelope (δ : ℝ) (x : Euclidean4) : ℝ := inverseCubeProfile δ ‖x‖

theorem inverseCubeEnvelope_nonneg (δ : ℝ) (x : Euclidean4) :
    0 ≤ inverseCubeEnvelope δ x := by
  unfold inverseCubeEnvelope inverseCubeProfile
  by_cases hx : ‖x‖ ∈ Set.Ioo 0 δ
  · rw [Set.indicator_of_mem hx]
    positivity
  · rw [Set.indicator_of_notMem hx]

theorem inverseCubeEnvelope_apply_inside (δ : ℝ) (x : Euclidean4)
    (hPos : 0 < ‖x‖) (hNear : ‖x‖ < δ) :
    inverseCubeEnvelope δ x = (‖x‖ ^ 3)⁻¹ := by
  unfold inverseCubeEnvelope inverseCubeProfile
  rw [Set.indicator_of_mem (show ‖x‖ ∈ Set.Ioo 0 δ from ⟨hPos, hNear⟩)]

private theorem weighted_profile_eq_indicator (δ : ℝ) (r : ℝ) :
    r ^ 3 • inverseCubeProfile δ r = (Set.Ioo 0 δ).indicator (fun _ => (1 : ℝ)) r := by
  by_cases hr : r ∈ Set.Ioo 0 δ
  · rw [inverseCubeProfile, Set.indicator_of_mem hr, Set.indicator_of_mem hr, smul_eq_mul,
      mul_inv_cancel₀ (pow_ne_zero _ hr.1.ne')]
  · rw [inverseCubeProfile, Set.indicator_of_notMem hr, Set.indicator_of_notMem hr, smul_zero]

theorem integrable_inverseCubeEnvelope (δ : ℝ) :
    Integrable (inverseCubeEnvelope δ) (volume : Measure Euclidean4) := by
  change Integrable (inverseCubeProfile δ ∘ fun x : Euclidean4 => ‖x‖)
    (volume : Measure Euclidean4)
  apply (integrable_fun_norm_addHaar (volume : Measure Euclidean4)).mpr
  have h : Integrable ((Set.Ioo 0 δ).indicator (fun _ => (1 : ℝ))) (volume : Measure ℝ) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr
      (integrableOn_const (by simp [Real.volume_Ioo]))
  have hEq : (fun r : ℝ => r ^ (Module.finrank ℝ Euclidean4 - 1) • inverseCubeProfile δ r) =
      (Set.Ioo 0 δ).indicator (fun _ => (1 : ℝ)) := by
    funext r
    simpa only [finrank_euclideanSpace_fin, Nat.reduceSub] using weighted_profile_eq_indicator δ r
  rw [hEq]
  exact h.integrableOn

/-- The exact Lebesgue mass of the dominating radial kernel. In particular it
goes to zero linearly with the truncation radius. -/
theorem integral_inverseCubeEnvelope (δ : ℝ) (hδ : 0 ≤ δ) :
    (∫ x : Euclidean4, inverseCubeEnvelope δ x) =
      4 * (volume : Measure Euclidean4).real (Metric.ball 0 1) * δ := by
  change (∫ x : Euclidean4, inverseCubeProfile δ ‖x‖) = _
  rw [integral_fun_norm_addHaar (volume : Measure Euclidean4) (inverseCubeProfile δ)]
  have hEq : (fun r : ℝ => r ^ (Module.finrank ℝ Euclidean4 - 1) • inverseCubeProfile δ r) =
      (Set.Ioo 0 δ).indicator (fun _ => (1 : ℝ)) := by
    funext r
    simpa only [finrank_euclideanSpace_fin, Nat.reduceSub] using weighted_profile_eq_indicator δ r
  rw [hEq, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr Set.Ioo_subset_Ioi_self,
    setIntegral_const, Real.volume_real_Ioo_of_le hδ, sub_zero]
  simp only [finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul, mul_one]
  ring

private theorem inverseCubeEnvelope_even (δ : ℝ) (x : Euclidean4) :
    inverseCubeEnvelope δ (-x) = inverseCubeEnvelope δ x := by
  simp only [inverseCubeEnvelope, norm_neg]

theorem integrable_inverseCubeEnvelope_sub_right (δ : ℝ) (x : Euclidean4) :
    Integrable (fun y => inverseCubeEnvelope δ (y - x)) (volume : Measure Euclidean4) := by
  apply memLp_one_iff_integrable.mp
  exact (memLp_one_iff_integrable.mpr (integrable_inverseCubeEnvelope δ)).comp_measurePreserving
    (measurePreserving_add_right (volume : Measure Euclidean4) (-x))

theorem integrable_inverseCubeEnvelope_sub_left (δ : ℝ) (x : Euclidean4) :
    Integrable (fun y => inverseCubeEnvelope δ (x - y)) (volume : Measure Euclidean4) := by
  refine (integrable_inverseCubeEnvelope_sub_right δ x).congr (Eventually.of_forall fun y => ?_)
  change inverseCubeEnvelope δ (y - x) = inverseCubeEnvelope δ (x - y)
  rw [← inverseCubeEnvelope_even δ (x - y), neg_sub]

theorem integral_inverseCubeEnvelope_sub_right (δ : ℝ) (hδ : 0 ≤ δ) (x : Euclidean4) :
    (∫ y, inverseCubeEnvelope δ (y - x)) =
      4 * (volume : Measure Euclidean4).real (Metric.ball 0 1) * δ := by
  let e : Euclidean4 ≃ₜ Euclidean4 := Homeomorph.addRight (-x)
  exact ((measurePreserving_add_right (volume : Measure Euclidean4) (-x)).integral_comp
    e.measurableEmbedding (inverseCubeEnvelope δ)).trans (integral_inverseCubeEnvelope δ hδ)

theorem integral_inverseCubeEnvelope_sub_left (δ : ℝ) (hδ : 0 ≤ δ) (x : Euclidean4) :
    (∫ y, inverseCubeEnvelope δ (x - y)) =
      4 * (volume : Measure Euclidean4).real (Metric.ball 0 1) * δ := by
  rw [← integral_inverseCubeEnvelope_sub_right δ hδ x]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change inverseCubeEnvelope δ (x - y) = inverseCubeEnvelope δ (y - x)
    rw [← inverseCubeEnvelope_even δ (x - y), neg_sub]

end Burnett.Microlocal.NearDiagonal
