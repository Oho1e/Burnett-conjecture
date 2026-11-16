import Burnett.Analysis.IBP.CompactIBP

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace Burnett.X02.LocalizedIBP

open CompactIBP

theorem integral_localized_directional {χ φ F : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hφ : ContDiff ℝ ∞ φ)
    (hF : ContDiff ℝ ∞ F) (v : Space) :
    (∫ x, χ x * fderiv ℝ F x v * φ x) =
      (∫ x, -(fderiv ℝ χ x v * F x) * φ x) -
      (∫ x, (χ x * F x) * fderiv ℝ φ x v) := by
  have hχD := continuous_directional hχ v
  have hφD := continuous_directional hφ v
  have hA : Integrable (fun x => (fderiv ℝ χ x v * F x) * φ x) :=
    ((hχD.mul hF.continuous).mul hφ.continuous).integrable_of_hasCompactSupport
      ((hcχ.fderiv_apply ℝ v).mul_right.mul_right)
  have hB : Integrable (fun x => (χ x * F x) * fderiv ℝ φ x v) :=
    ((hχ.continuous.mul hF.continuous).mul hφD).integrable_of_hasCompactSupport
      (hcχ.mul_right.mul_right)
  have hd (x : Space) : fderiv ℝ (fun y => χ y * φ y) x v =
      fderiv ℝ χ x v * φ x + χ x * fderiv ℝ φ x v := by
    rw [fderiv_fun_mul (hχ.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have h := integral_test_directional (hχ.mul hφ) (hcχ.mul_right) hF v
  simp_rw [hd] at h
  have hlhs : (fun x => (χ x * φ x) * fderiv ℝ F x v) =
      (fun x => χ x * fderiv ℝ F x v * φ x) := by funext x; ring
  have hrhs : (fun x => (fderiv ℝ χ x v * φ x + χ x * fderiv ℝ φ x v) * F x) =
      (fun x => (fderiv ℝ χ x v * F x) * φ x + (χ x * F x) * fderiv ℝ φ x v) := by
    funext x
    ring
  rw [hlhs, hrhs, integral_add hA hB] at h
  have hneg : (fun x => -(fderiv ℝ χ x v * F x) * φ x) =
      (fun x => -((fderiv ℝ χ x v * F x) * φ x)) := by funext x; ring
  rw [hneg, integral_neg, h]
  ring

theorem integral_localized_divergence {χ φ : Space → ℝ} {F : Fin 4 → Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hφ : ContDiff ℝ ∞ φ) (hF : ∀ i, ContDiff ℝ ∞ (F i)) :
    (∫ x, χ x * (∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)) * φ x) =
      (∫ x, (-(∑ i, fderiv ℝ χ x (EuclideanSpace.single i 1) * F i x)) * φ x) -
      ∑ i, (∫ x, (χ x * F i x) * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
  let A (i : Fin 4) (x : Space) :=
    -(fderiv ℝ χ x (EuclideanSpace.single i 1) * F i x) * φ x
  let B (i : Fin 4) (x : Space) :=
    (χ x * F i x) * fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hA (i : Fin 4) : Integrable (A i) :=
    (((continuous_directional hχ _).mul (hF i).continuous).neg.mul
      hφ.continuous).integrable_of_hasCompactSupport
        (((hcχ.fderiv_apply ℝ _).mul_right).neg.mul_right)
  have hC (i : Fin 4) : Integrable
      (fun x => χ x * fderiv ℝ (F i) x (EuclideanSpace.single i 1) * φ x) :=
    ((hχ.continuous.mul (continuous_directional (hF i) _)).mul
      hφ.continuous).integrable_of_hasCompactSupport (hcχ.mul_right.mul_right)
  have hlhs (x : Space) :
      χ x * (∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)) * φ x =
      ∑ i, χ x * fderiv ℝ (F i) x (EuclideanSpace.single i 1) * φ x := by
    rw [Finset.mul_sum, Finset.sum_mul]
  have hrhs (x : Space) : ∑ i, A i x =
      (-(∑ i, fderiv ℝ χ x (EuclideanSpace.single i 1) * F i x)) * φ x := by
    dsimp only [A]
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
  calc
    _ = ∫ x, ∑ i, χ x * fderiv ℝ (F i) x (EuclideanSpace.single i 1) * φ x :=
      integral_congr_ae (Filter.Eventually.of_forall hlhs)
    _ = ∑ i, ∫ x, χ x * fderiv ℝ (F i) x (EuclideanSpace.single i 1) * φ x :=
      integral_finset_sum _ (fun i _ => hC i)
    _ = ∑ i, ((∫ x, A i x) - (∫ x, B i x)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_localized_directional hχ hcχ hφ (hF i) _
    _ = (∑ i, ∫ x, A i x) - ∑ i, ∫ x, B i x := by rw [Finset.sum_sub_distrib]
    _ = (∫ x, ∑ i, A i x) - ∑ i, ∫ x, B i x := by
      rw [integral_finset_sum _ (fun i _ => hA i)]
    _ = _ := by simp_rw [hrhs]; rfl

#print axioms integral_localized_directional
#print axioms integral_localized_divergence

end Burnett.X02.LocalizedIBP
