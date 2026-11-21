import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearUniformCoefficient
import Burnett.Analysis.CubicEnergy.CompleteEnergy.CompleteCubicEuclidean
import Burnett.Analysis.CubicEnergy.CompleteEnergy.FieldAndCoefficientChecks

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Metric Burnett.RicciSymbol Burnett.A02.FieldAndCoefficientReview
open scoped BigOperators ComplexConjugate ContDiff ENNReal

/-- Undifferentiated fields have the Euclidean finite-dimensional Lᵖ norm
formed from their actual components. -/
theorem fieldValueArray_memLp {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ)
    (p : ℝ≥0∞) : MemLp (fieldValueArray u) p volume := by
  classical
  let W (j : J) (x : E) : EuclideanSpace ℂ J := u j x • EuclideanSpace.single j 1
  have expand : (∑ j, W j) = fieldValueArray u := by
    funext x
    rw [Finset.sum_apply]
    simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun J ℂ).sum_repr (fieldValueArray u x)
  rw [← expand]
  apply memLp_finset_sum'
  intro j _
  have hW : Continuous (W j) := (u j).continuous.smul continuous_const
  refine ((u j).memLp p volume).mono hW.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by simp [W, norm_smul]

/-- The paper's undifferentiated L³ norm, with the same Euclidean fiber metric
as the full gradient array. -/
def euclideanFieldValueL3 {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) : ℝ :=
  (eLpNorm (fieldValueArray u) (ENNReal.ofReal 3) volume).toReal

/-- The two distinct field slots of the exact weighted quasilinear energy have
the product bound with the full Euclidean field and gradient arrays. -/
theorem quasilinear_weighted_euclidean_sphere_enorm {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ) (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (H u v : J → SchwartzMap E ℂ)
        (hcompact : ∀ j, HasCompactSupport (H j : E → ℂ)),
      (∀ j x, conj (H j x) = H j x) →
      ENNReal.ofReal |quasilinearSymmetricEnergy b
        (linearEnergyCoefficient c (fun j => scalarWeightedField f hf (H j) (hcompact j))) u v| ≤
        (C * ENNReal.ofReal D) *
          (eLpNorm f ⊤ volume * euclideanFieldGradientNorm H +
           eLpNorm (scalarCoordinateGradient f) ⊤ volume * eLpNorm (fieldValueArray H) (ENNReal.ofReal 3) volume) *
          (euclideanFieldGradientNorm u * euclideanFieldGradientNorm v) := by
  obtain ⟨K,hK,bound⟩ := quasilinear_linear_coefficient_sphere_bound c hc
  let N : ℝ≥0∞ := Fintype.card J
  let M : ℝ≥0∞ := N * Fintype.card Index
  have hM : M < ⊤ := ENNReal.mul_lt_top (by simp [N]) (by simp)
  have h1 : (1 : ℝ≥0∞) ≤ (Fintype.card Index : ℝ≥0∞) := by
    change (1 : ℝ≥0∞) ≤ (Fintype.card (Fin 4) : ℝ≥0∞)
    simp
  have hNM : N ≤ M := by
    dsimp only [M]
    simpa only [mul_one] using mul_le_mul_left' h1 N
  have hM3 : M^3 < ⊤ := by
    rw [pow_succ, pow_two]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hM hM) hM
  refine ⟨K * M^3, ENNReal.mul_lt_top hK hM3, ?_⟩
  intro b hb hom D hD jet f hf H u v hcompact hReal
  let W (j : J) := scalarWeightedField f hf (H j) (hcompact j)
  let F := eLpNorm f ⊤ volume
  let dF := eLpNorm (scalarCoordinateGradient f) ⊤ volume
  let V := eLpNorm (fieldValueArray H) (ENNReal.ofReal 3) volume
  let R := F * euclideanFieldGradientNorm H + dF * V
  have realW : ∀ j x, conj (W j x) = W j x := by
    intro j x
    simp only [W, scalarWeightedField_apply, map_mul, Complex.conj_ofReal, hReal]
  have gradW : fieldEnergyGradientNorm W ≤ F * fieldEnergyGradientNorm H +
      dF * (∑ j, eLpNorm (H j : E → ℂ) (ENNReal.ofReal 3) volume) := by
    dsimp only [F, dF]
    rw [scalar_coordinate_gradient_Linfty]
    unfold fieldEnergyGradientNorm
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => scalarWeightedField_gradient_bound f hf (H j) (hcompact j))
  have gradH : fieldEnergyGradientNorm H ≤ M * euclideanFieldGradientNorm H :=
    fieldEnergyGradientNorm_le_euclidean H
  have valH : (∑ j, eLpNorm (H j : E → ℂ) (ENNReal.ofReal 3) volume) ≤ M * V :=
    (component_values_L3_le_euclidean H).trans (mul_le_mul_right' hNM V)
  have weighted : fieldEnergyGradientNorm W ≤ M * R := calc
    _ ≤ _ := gradW
    _ ≤ F * (M * euclideanFieldGradientNorm H) + dF * (M * V) :=
      add_le_add (mul_le_mul_left' gradH F) (mul_le_mul_left' valH dF)
    _ = _ := by dsimp only [R]; ring
  have gu : fieldEnergyGradientNorm u ≤ M * euclideanFieldGradientNorm u :=
    fieldEnergyGradientNorm_le_euclidean u
  have gv : fieldEnergyGradientNorm v ≤ M * euclideanFieldGradientNorm v :=
    fieldEnergyGradientNorm_le_euclidean v
  calc
    _ ≤ (K * ENNReal.ofReal D) *
        (fieldEnergyGradientNorm W * (fieldEnergyGradientNorm u * fieldEnergyGradientNorm v)) :=
      bound b hb hom D hD jet W u v realW
    _ ≤ (K * ENNReal.ofReal D) *
        ((M * R) * ((M * euclideanFieldGradientNorm u) * (M * euclideanFieldGradientNorm v))) :=
      mul_le_mul_left' (mul_le_mul' weighted (mul_le_mul' gu gv)) _
    _ = _ := by change _ = ((K * M^3) * ENNReal.ofReal D) * R * _; ring

/-- The real-norm weighted coefficient estimate of the paper. The symbol
constant is uniform over the original finite-normalized-jet sets. -/
theorem quasilinear_weighted_euclidean_sphere_bound {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ) (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (f : E → ℝ) (hf : ContDiff ℝ ∞ f), eLpNorm f ⊤ volume < ⊤ →
        eLpNorm (scalarCoordinateGradient f) ⊤ volume < ⊤ →
      ∀ (H u v : J → SchwartzMap E ℂ) (hcompact : ∀ j, HasCompactSupport (H j : E → ℂ)),
      (∀ j x, conj (H j x) = H j x) →
      |quasilinearSymmetricEnergy b
        (linearEnergyCoefficient c (fun j => scalarWeightedField f hf (H j) (hcompact j))) u v| ≤
        (C * D) * ((eLpNorm f ⊤ volume).toReal * euclideanFieldGradientL3 H +
          (eLpNorm (scalarCoordinateGradient f) ⊤ volume).toReal * euclideanFieldValueL3 H) *
          (euclideanFieldGradientL3 u * euclideanFieldGradientL3 v) := by
  obtain ⟨K,hK,est⟩ := quasilinear_weighted_euclidean_sphere_enorm c hc
  refine ⟨K.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro b hb hom D hD jet f hf hF hdF H u v hcompact hReal
  let T := quasilinearSymmetricEnergy b
    (linearEnergyCoefficient c (fun j => scalarWeightedField f hf (H j) (hcompact j))) u v
  have h1 : eLpNorm f ⊤ volume * euclideanFieldGradientNorm H < ⊤ :=
    ENNReal.mul_lt_top hF (euclideanFieldGradientNorm_lt_top H)
  have h2 : eLpNorm (scalarCoordinateGradient f) ⊤ volume *
      eLpNorm (fieldValueArray H) (ENNReal.ofReal 3) volume < ⊤ :=
    ENNReal.mul_lt_top hdF (fieldValueArray_memLp H _).eLpNorm_lt_top
  have hR : eLpNorm f ⊤ volume * euclideanFieldGradientNorm H +
      eLpNorm (scalarCoordinateGradient f) ⊤ volume * eLpNorm (fieldValueArray H) (ENNReal.ofReal 3) volume < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨h1,h2⟩
  have hP := ENNReal.mul_lt_top (euclideanFieldGradientNorm_lt_top u) (euclideanFieldGradientNorm_lt_top v)
  have hKD : K * ENNReal.ofReal D < ⊤ := ENNReal.mul_lt_top hK ENNReal.ofReal_lt_top
  have finite := ENNReal.mul_lt_top (ENNReal.mul_lt_top hKD hR) hP
  have e := ENNReal.toReal_mono finite.ne (est b hb hom D hD jet f hf H u v hcompact hReal)
  change (ENNReal.ofReal |T|).toReal ≤ _ at e
  change |T| ≤ _
  simpa only [ENNReal.toReal_ofReal (abs_nonneg T), ENNReal.toReal_ofReal hD,
    ENNReal.toReal_add h1.ne h2.ne, ENNReal.toReal_mul, euclideanFieldGradientL3,
    euclideanFieldValueL3] using e

end Burnett.A02.FrequencySplit
