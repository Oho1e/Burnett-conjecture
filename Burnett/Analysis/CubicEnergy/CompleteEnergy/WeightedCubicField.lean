import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearCoefficient

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ContDiff ENNReal

/-- Multiply a compactly supported component by the actual real coefficient.
Compact support of the product permits arbitrary smooth f. -/
def scalarWeightedField (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (u : SchwartzMap E ℂ)
    (hu : HasCompactSupport (u : E → ℂ)) : SchwartzMap E ℂ :=
  (hu.mul_left (f := fun x => (f x : ℂ))).toSchwartzMap
    ((Complex.ofRealCLM.contDiff.comp hf).mul (u.smooth ⊤))

@[simp] theorem scalarWeightedField_apply (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (u : SchwartzMap E ℂ)
    (hu : HasCompactSupport (u : E → ℂ)) (x : E) :
    scalarWeightedField f hf u hu x = (f x : ℂ) * u x := rfl

private theorem scalarWeightedField_gradient (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (u : SchwartzMap E ℂ) (hu : HasCompactSupport (u : E → ℂ)) (x : E) :
    fderiv ℝ (scalarWeightedField f hf u hu : E → ℂ) x =
      f x • fderiv ℝ (u : E → ℂ) x + (fderiv ℝ f x).smulRight (u x) := by
  have eq : (scalarWeightedField f hf u hu : E → ℂ) = f • (u : E → ℂ) := by
    funext y
    rfl
  rw [eq]
  exact fderiv_smul ((hf.differentiable (by simp)) x) (u.differentiable x)

/-- The exact product rule yields the two Sobolev quantities on the coefficient
difference, using only its L∞ norm and its first derivative. -/
theorem scalarWeightedField_gradient_bound (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (u : SchwartzMap E ℂ) (hu : HasCompactSupport (u : E → ℂ)) :
    energyGradientNorm (scalarWeightedField f hf u hu) ≤
      eLpNorm f ⊤ volume * energyGradientNorm u +
        eLpNorm (fderiv ℝ f) ⊤ volume * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume := by
  let D := fderiv ℝ (u : E → ℂ)
  let df := fderiv ℝ f
  let A : E → E →L[ℝ] ℂ := f • D
  let B : E → E →L[ℝ] ℂ := fun x => (df x).smulRight (u x)
  have hD : Continuous D := (SchwartzMap.fderivCLM ℝ u).continuous
  have hdf : Continuous df := hf.continuous_fderiv (by simp)
  have hA : Continuous A := hf.continuous.smul hD
  have hB : Continuous B :=
    ((ContinuousLinearMap.smulRightL ℝ E ℂ).continuous.comp hdf).clm_apply u.continuous
  have deriv_eq : fderiv ℝ (scalarWeightedField f hf u hu : E → ℂ) = A + B :=
    funext (scalarWeightedField_gradient f hf u hu)
  unfold energyGradientNorm
  rw [deriv_eq]
  have boundA : eLpNorm A (ENNReal.ofReal 3) volume ≤
      eLpNorm f ⊤ volume * eLpNorm D (ENNReal.ofReal 3) volume :=
    eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm _ hD.aestronglyMeasurable f
  have boundB : eLpNorm B (ENNReal.ofReal 3) volume ≤
      eLpNorm df ⊤ volume * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume := by
    let N : E → ℝ := fun x => ‖df x‖
    calc
      _ ≤ eLpNorm (N • (u : E → ℂ)) (ENNReal.ofReal 3) volume := by
        apply eLpNorm_mono
        intro x
        change ‖(df x).smulRight (u x)‖ ≤ ‖‖df x‖ • u x‖
        rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
      _ ≤ _ := by
        simpa only [N, eLpNorm_norm] using eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
          (ENNReal.ofReal 3) u.continuous.aestronglyMeasurable N
  exact (eLpNorm_add_le hA.aestronglyMeasurable hB.aestronglyMeasurable (by norm_num)).trans
    (add_le_add boundA boundB)

/-- Multiplication by f enters the same real linear coefficient at every point. -/
theorem linearEnergyCoefficient_weighted_apply {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (H : J → SchwartzMap E ℂ)
    (hH : ∀ j, HasCompactSupport (H j : E → ℂ)) (k : EnergyIndex J) (x : E) :
    linearEnergyCoefficient c (fun j => scalarWeightedField f hf (H j) (hH j)) k x =
      (f x : ℂ) * linearEnergyCoefficient c H k x := by
  let ev : SchwartzMap E ℂ →+ ℂ :=
    { toFun := fun s => s x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  unfold linearEnergyCoefficient
  change ev (∑ j, c k j • scalarWeightedField f hf (H j) (hH j)) =
    (f x : ℂ) * ev (∑ j, c k j • H j)
  simp only [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (c k j : ℂ) * ((f x : ℂ) * H j x) = (f x : ℂ) * ((c k j : ℂ) * H j x)
  ring

/-- Estimate the complete polarized quasilinear pairing for the coefficient f A(H)
using the same bounded input norm and its first derivative as in the paper. -/
theorem quasilinear_weighted_coefficient_estimate (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (H u v : J → SchwartzMap E ℂ)
      (hcompact : ∀ j, HasCompactSupport (H j : E → ℂ)),
      (∀ j x, conj (H j x) = H j x) →
      ENNReal.ofReal |quasilinearSymmetricEnergy b
        (linearEnergyCoefficient c (fun j => scalarWeightedField f hf (H j) (hcompact j))) u v| ≤
        C * ((eLpNorm f ⊤ volume * fieldEnergyGradientNorm H +
          eLpNorm (fderiv ℝ f) ⊤ volume * (∑ j, eLpNorm (H j : E → ℂ) (ENNReal.ofReal 3) volume)) *
          (fieldEnergyGradientNorm u * fieldEnergyGradientNorm v)) := by
  obtain ⟨C, hC, bound⟩ := quasilinear_linear_coefficient_estimate b hb hom c hc
  refine ⟨C, hC, fun f hf H u v hCompact hReal => ?_⟩
  let W (j : J) := scalarWeightedField f hf (H j) (hCompact j)
  have realW : ∀ j x, conj (W j x) = W j x := by
    intro j x
    simp only [W, scalarWeightedField_apply, map_mul, Complex.conj_ofReal, hReal]
  have gradW : fieldEnergyGradientNorm W ≤ eLpNorm f ⊤ volume * fieldEnergyGradientNorm H +
      eLpNorm (fderiv ℝ f) ⊤ volume * (∑ j, eLpNorm (H j : E → ℂ) (ENNReal.ofReal 3) volume) := by
    unfold fieldEnergyGradientNorm
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => scalarWeightedField_gradient_bound f hf (H j) (hCompact j))
  exact (bound W u v realW).trans (mul_le_mul_left' (mul_le_mul_right' gradW _) _)

end Burnett.A02.FrequencySplit
