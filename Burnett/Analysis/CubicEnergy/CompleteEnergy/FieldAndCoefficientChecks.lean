import Burnett.Analysis.CubicEnergy.CompleteEnergy.EuclideanFieldGradient
import Burnett.Analysis.CubicEnergy.CompleteEnergy.WeightedCubicField
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FieldAndCoefficientReview
open FrequencySplit MeasureTheory Finset Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ContDiff ENNReal RealInnerProductSpace

/-- The reconstructed coordinate array uses the full real derivative. -/
theorem coordinate_array_norm_sq {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) (x : E) :
    ‖euclideanFieldGradient u x‖^2 =
      ∑ k : Fin 4 × J, ‖fderiv ℝ (u k.2 : E → ℂ) x (EuclideanSpace.single k.1 1)‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro k _
  rfl

/-- A real scalar's literal four coordinate derivatives as a Euclidean vector. -/
def scalarCoordinateGradient (f : E → ℝ) (x : E) : E :=
  WithLp.toLp 2 (fun a : Fin 4 => fderiv ℝ f x (EuclideanSpace.single a 1))

theorem scalar_coordinate_gradient_norm (f : E → ℝ) (x : E) :
    ‖scalarCoordinateGradient f x‖ = ‖fderiv ℝ f x‖ := by
  let L := fderiv ℝ f x
  let v := (InnerProductSpace.toDual ℝ E).symm L
  have eq : scalarCoordinateGradient f x = v := by
    ext a
    change L (EuclideanSpace.single a 1) = v a
    calc
      _ = inner ℝ v (EuclideanSpace.single a 1) :=
        (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single a 1) (y := L)).symm
      _ = _ := by simp [EuclideanSpace.inner_single_right]
  rw [eq]
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map L

theorem scalar_coordinate_gradient_Linfty (f : E → ℝ) :
    eLpNorm (scalarCoordinateGradient f) ⊤ volume =
      eLpNorm (fderiv ℝ f) ⊤ volume :=
  eLpNorm_congr_norm_ae (.of_forall (scalar_coordinate_gradient_norm f))

/-- The literal Euclidean norm of an undifferentiated field's array. -/
def fieldValueArray {J : Type} [Fintype J] (H : J → SchwartzMap E ℂ) (x : E) :
    EuclideanSpace ℂ J :=
  WithLp.toLp 2 (fun j => H j x)

theorem component_values_L3_le_euclidean {J : Type} [Fintype J] (H : J → SchwartzMap E ℂ) :
    (∑ j, eLpNorm (H j : E → ℂ) (ENNReal.ofReal 3) volume) ≤
      (Fintype.card J : ℝ≥0∞) * eLpNorm (fieldValueArray H) (ENNReal.ofReal 3) volume := by
  classical
  have component (j : J) :
      eLpNorm (H j : E → ℂ) (ENNReal.ofReal 3) volume ≤
        eLpNorm (fieldValueArray H) (ENNReal.ofReal 3) volume := by
    apply eLpNorm_mono
    intro x
    exact PiLp.norm_apply_le (fieldValueArray H x) j
  calc
    _ ≤ ∑ _j : J, eLpNorm (fieldValueArray H) (ENNReal.ofReal 3) volume :=
      Finset.sum_le_sum (fun j _ => component j)
    _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

theorem scalar_weighted_coordinate_product_rule (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (H : SchwartzMap E ℂ) (hH : HasCompactSupport (H : E → ℂ)) (a : Fin 4) (x : E) :
    energyPartial a (scalarWeightedField f hf H hH) x =
      f x • energyPartial a H x + scalarCoordinateGradient f x a • H x := by
  have eq : (scalarWeightedField f hf H hH : E → ℂ) = f • (H : E → ℂ) := by
    funext y
    rfl
  simp only [energyPartial,SchwartzMap.pderivCLM_apply]
  rw [eq, fderiv_smul ((hf.differentiable (by simp)) x) (H.differentiable x)]
  rfl

/-- This check expands the actual ordered pairing while leaving its field
and Fourier test inputs exactly where they occur in the manuscript. -/
theorem weighted_mixed_pairing_exact {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (b : E → ℝ) (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (H u v : J → SchwartzMap E ℂ)
    (hH : ∀ j, HasCompactSupport (H j : E → ℂ)) :
    quasilinearMixedPairing b (linearEnergyCoefficient c (fun j => scalarWeightedField f hf (H j) (hH j))) u v =
      ∑ k : EnergyIndex J, ∫ x, ((f x : ℂ) * linearEnergyCoefficient c H k x) *
        energyPartial k.1.1 (energyPartial k.1.2 (u k.2.2)) x *
        conj (radianAction b (v k.2.1) x) := by
  simp only [quasilinearMixedPairing, linearEnergyCoefficient_weighted_apply]

theorem weighted_quasilinear_diagonal_exact {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (b : E → ℝ) (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (H u : J → SchwartzMap E ℂ)
    (hH : ∀ j, HasCompactSupport (H j : E → ℂ)) :
    quasilinearSymmetricEnergy b (linearEnergyCoefficient c (fun j => scalarWeightedField f hf (H j) (hH j))) u u =
      2 * ((∑ k : EnergyIndex J, ∫ x, ((f x : ℂ) * linearEnergyCoefficient c H k x) *
        energyPartial k.1.1 (energyPartial k.1.2 (u k.2.2)) x *
        conj (radianAction b (u k.2.1) x)) : ℂ).im := by
  rw [quasilinearSymmetricEnergy_diag]
  change 2 * (quasilinearMixedPairing b _ u u).im = _
  rw [weighted_mixed_pairing_exact]

end Burnett.A02.FieldAndCoefficientReview
