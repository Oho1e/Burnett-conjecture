import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearCoefficient

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped BigOperators ENNReal

/-- The full array of coordinate derivatives with the fixed Euclidean fiber norm. -/
def euclideanFieldGradient {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) (x : E) :
    EuclideanSpace ℂ (Index × J) :=
  WithLp.toLp 2 (fun k : Index × J => energyPartial k.1 (u k.2) x)

/-- The L³ norm of the full Euclidean gradient array appearing in the paper. -/
def euclideanFieldGradientNorm {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) : ℝ≥0∞ :=
  eLpNorm (euclideanFieldGradient u) (ENNReal.ofReal 3) volume

private theorem euclidean_basis_expansion {K ι : Type*} [RCLike K] [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace K ι) : (∑ k, v k • EuclideanSpace.single k (1 : K)) = v := by
  simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
    (EuclideanSpace.basisFun ι K).sum_repr v

theorem euclideanFieldGradient_memLp {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ)
    (p : ℝ≥0∞) : MemLp (euclideanFieldGradient u) p volume := by
  classical
  let S (k : Index × J) (x : E) : EuclideanSpace ℂ (Index × J) :=
    energyPartial k.1 (u k.2) x • EuclideanSpace.single k 1
  have sum : (∑ k, S k) = euclideanFieldGradient u := by
    funext x
    rw [Finset.sum_apply]
    exact euclidean_basis_expansion (euclideanFieldGradient u x)
  rw [← sum]
  apply memLp_finset_sum'
  intro k _
  have hS : Continuous (S k) := (energyPartial k.1 (u k.2)).continuous.smul continuous_const
  refine ((energyPartial k.1 (u k.2)).memLp p volume).mono hS.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by
    simp [S, norm_smul]

private theorem component_gradient_pointwise {J : Type} [Fintype J]
    (u : J → SchwartzMap E ℂ) (j : J) (x : E) :
    ‖fderiv ℝ (u j : E → ℂ) x‖ ≤ (Fintype.card Index : ℝ) * ‖euclideanFieldGradient u x‖ := by
  classical
  let T := fderiv ℝ (u j : E → ℂ) x
  apply T.opNorm_le_bound (by positivity)
  intro v
  have expand : T v = ∑ a : Index, v a • T (EuclideanSpace.single a 1) := calc
    T v = T (∑ a : Index, v a • EuclideanSpace.single a 1) :=
      congrArg (fun y : E => T y) (euclidean_basis_expansion v).symm
    _ = _ := by simp only [map_sum, map_smul]
  rw [expand]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _a : Index, ‖euclideanFieldGradient u x‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, mul_comm]
      exact mul_le_mul (PiLp.norm_apply_le (euclideanFieldGradient u x) (a,j))
        (PiLp.norm_apply_le v a) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- The component norms used in the estimates are controlled by the actual
Euclidean gradient norm, with a fixed finite-dimensional factor. -/
theorem fieldEnergyGradientNorm_le_euclidean {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) :
    fieldEnergyGradientNorm u ≤ ((Fintype.card J : ℝ≥0∞) * Fintype.card Index) *
      euclideanFieldGradientNorm u := by
  classical
  let M := (Fintype.card Index : ℝ)
  have hM : ‖M‖ₑ = (Fintype.card Index : ℝ≥0∞) := by
    rw [Real.enorm_eq_ofReal (by positivity : 0 ≤ M)]
    simp [M]
  have component (j : J) :
      energyGradientNorm (u j) ≤ ‖M‖ₑ * euclideanFieldGradientNorm u := by
    unfold energyGradientNorm euclideanFieldGradientNorm
    rw [← eLpNorm_const_smul M]
    apply eLpNorm_mono
    intro x
    simpa only [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ M)] using
      component_gradient_pointwise u j x
  calc
    _ ≤ ∑ _j : J, ‖M‖ₑ * euclideanFieldGradientNorm u := Finset.sum_le_sum (fun j _ => component j)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hM, ← mul_assoc]

theorem euclideanFieldGradientNorm_lt_top {J : Type} [Fintype J] (u : J → SchwartzMap E ℂ) :
    euclideanFieldGradientNorm u < ⊤ := (euclideanFieldGradient_memLp u _).eLpNorm_lt_top

end Burnett.A02.FrequencySplit
