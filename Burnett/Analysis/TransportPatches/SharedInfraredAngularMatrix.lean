import Burnett.Analysis.TransportPatches.ClassicalMatrixMultiplier
import Burnett.Analysis.GaugeProjection.ProjectedDefectActualComponents

/-! Compose a real angular matrix with the original fixed regularized gauge projection. -/

set_option autoImplicit false
set_option maxRecDepth 5200
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Matrix Burnett.Fourier
open Burnett.A02.FrequencySplit (E tau mikhlin_bounded_symbol)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Microlocal.SeparablePositive (productSymbol productSymbol_apply fourierMultiplier_product)
open Burnett.P01 (regularizedProjectionComponentSymbol regularizedGaugeProjectionSymbol
  regularizedGaugeProjectionSymbol_contDiff regularizedGaugeProjectionSymbol_zero
  principalProjectionComponentSymbol_apply principalGaugeProjectionMatrix
  gaugeProjectionSymbol_contDiffOn gaugeProjectionSymbol_scale gaugeProjectionInfrared)
open scoped BigOperators ContDiff Matrix Topology

open private regularizedProjectionComponentSymbol_eq_off_ball
  from Burnett.Analysis.GaugeProjection.ProjectedDefectActualComponents

local notation "Mat" => Matrix OrderedPair OrderedPair ℂ

/-- The scalar Mikhlin hypotheses on all ordered coefficients of a real angular matrix. -/
structure RealOrderedAngularMatrix where
  matrix : E → Matrix OrderedPair OrderedPair ℝ
  smooth : ∀ k i, ContDiffOn ℝ ∞ (fun ξ => matrix ξ k i) ({0}ᶜ : Set E)
  degree : ∀ t : ℝ, 0 < t → ∀ ξ : E, matrix (t • ξ) = matrix ξ

def RealOrderedAngularMatrix.complex (S : RealOrderedAngularMatrix) (ξ : E) : Mat :=
  fun k i => (S.matrix ξ k i : ℂ)

def RealOrderedAngularMatrix.coefficient (S : RealOrderedAngularMatrix) (k i : OrderedPair) : BoundedSymbol E :=
  Classical.choose (mikhlin_bounded_symbol (fun ξ => S.matrix ξ k i) (S.smooth k i)
    (fun t ht ξ => congrFun (congrFun (S.degree t ht ξ) k) i))

theorem RealOrderedAngularMatrix.coefficient_apply (S : RealOrderedAngularMatrix)
    (k i : OrderedPair) (ξ : E) : S.coefficient k i ξ = S.complex ξ k i :=
  Classical.choose_spec (mikhlin_bounded_symbol (fun ξ => S.matrix ξ k i) (S.smooth k i)
    (fun t ht ξ => congrFun (congrFun (S.degree t ht ξ) k) i)) ξ

private def finiteSumSymbol {ι : Type*} [Fintype ι] (a : ι → BoundedSymbol E) : BoundedSymbol E where
  toFun ξ := ∑ i, a i ξ
  measurable := by
    rw [show (fun ξ => ∑ i, a i ξ) = ∑ i, (a i : E → ℂ) from funext (fun ξ => (Finset.sum_apply _ _ _).symm)]
    exact Finset.aestronglyMeasurable_sum _ (fun i _ => (a i).measurable)
  bound := ∑ i, (a i).bound
  bound_nonneg := Finset.sum_nonneg (fun i _ => (a i).bound_nonneg)
  norm_le ξ := (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => (a i).norm_le ξ))

private theorem l2FinsetSum_ae {ι : Type*} (J : Finset ι) (F : ι → ComplexL2 E) :
    ((∑ j ∈ J, F j : ComplexL2 E) : E → ℂ) =ᵐ[volume] fun ξ => ∑ j ∈ J, F j ξ := by
  classical
  induction J using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero ℂ 2 (volume : Measure E)
  | insert j J hj ih =>
      simp only [Finset.sum_insert hj]
      filter_upwards [Lp.coeFn_add (F j) (∑ i ∈ J, F i), ih] with x hx hy
      rw [hx, Pi.add_apply, hy]

private theorem fourierMultiplier_finiteSum {ι : Type*} [Fintype ι] (a : ι → BoundedSymbol E)
    (u : ComplexL2 E) :
    fourierMultiplier (finiteSumSymbol a) u = ∑ i, fourierMultiplier (a i) u := by
  apply (fourierL2Equiv (V := E)).injective
  simp only [map_sum, fourier_fourierMultiplier]
  apply Lp.ext
  let v := fourierL2Equiv u
  have he : ∀ᵐ ξ ∂(volume : Measure E), ∀ i, symbolL2 (a i) v ξ = a i ξ * v ξ :=
    ae_all_iff.mpr (fun i => symbolL2_ae (a i) v)
  filter_upwards [symbolL2_ae (finiteSumSymbol a) v, l2FinsetSum_ae Finset.univ (fun i => symbolL2 (a i) v), he]
    with ξ hAll hSum hEach
  change symbolL2 (finiteSumSymbol a) v ξ = (∑ i, symbolL2 (a i) v) ξ
  rw [hAll, hSum]
  simp only [finiteSumSymbol, Finset.sum_mul, hEach]

/-- This is the same ordered source used by the actual regularized Schwartz projection. -/
def originalOrderedProjectedField (u : OrderedPair → ComplexL2 E) (k : OrderedPair) : ComplexL2 E :=
  ∑ i : OrderedPair, fourierMultiplier (regularizedProjectionComponentSymbol k.1 k.2 i.1 i.2) (u i)

def RealOrderedAngularMatrix.output (S : RealOrderedAngularMatrix)
    (u : OrderedPair → ComplexL2 E) (k : OrderedPair) : ComplexL2 E :=
  ∑ i : OrderedPair, fourierMultiplier (S.coefficient k i) (u i)

private def RealOrderedAngularMatrix.composedFull (S : RealOrderedAngularMatrix)
    (k i : OrderedPair) : BoundedSymbol E :=
  finiteSumSymbol (fun j : OrderedPair =>
    productSymbol (S.coefficient k j) (regularizedProjectionComponentSymbol j.1 j.2 i.1 i.2))

private theorem RealOrderedAngularMatrix.composedFull_apply (S : RealOrderedAngularMatrix)
    (k i : OrderedPair) (ξ : E) :
    S.composedFull k i ξ = ∑ j : OrderedPair, S.complex ξ k j *
      (regularizedGaugeProjectionSymbol j.1 j.2 i.1 i.2 (tau • ξ) : ℂ) := by
  change (∑ j : OrderedPair, productSymbol (S.coefficient k j)
    (regularizedProjectionComponentSymbol j.1 j.2 i.1 i.2) ξ) = _
  simp only [productSymbol_apply, S.coefficient_apply]
  rfl

private theorem RealOrderedAngularMatrix.composedFull_smooth (S : RealOrderedAngularMatrix)
    (k i : OrderedPair) : ContDiff ℝ ∞ (S.composedFull k i : E → ℂ) := by
  let f : E → ℂ := S.composedFull k i
  have ht : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  change ContDiff ℝ ∞ f
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    have hNear : ∀ᶠ ξ in 𝓝 (0 : E), ‖ξ‖ < 1 / tau :=
      (continuous_norm.tendsto (0 : E)).eventually (Iio_mem_nhds (by simpa using one_div_pos.mpr ht))
    have hZero : f =ᶠ[𝓝 (0 : E)] (fun _ : E => (0 : ℂ)) := by
      filter_upwards [hNear] with ξ hξ
      have hg : ‖tau • ξ‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg ht.le, mul_comm]
        exact ((lt_div_iff₀ ht).1 hξ).le
      change S.composedFull k i ξ = 0
      simp only [S.composedFull_apply, regularizedGaugeProjectionSymbol_zero _ _ _ _ hg,
        Complex.ofReal_zero, mul_zero, Finset.sum_const_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hZero
  · have hSmooth : ContDiffAt ℝ ∞ (fun ξ : E => ∑ j : OrderedPair, S.complex ξ k j *
        (regularizedGaugeProjectionSymbol j.1 j.2 i.1 i.2 (tau • ξ) : ℂ)) ξ := by
      apply ContDiffAt.sum
      intro j _
      have hj : ContDiffOn ℝ ∞ (fun ξ : E => S.complex ξ k j) ({0}ᶜ : Set E) :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn (S.smooth k j)
      have hg : ContDiff ℝ ∞ (fun ξ : E =>
          (regularizedGaugeProjectionSymbol j.1 j.2 i.1 i.2 (tau • ξ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp ((regularizedGaugeProjectionSymbol_contDiff _ _ _ _).comp
          (contDiff_const.smul contDiff_id))
      exact (hj.contDiffAt (isOpen_compl_singleton.mem_nhds hξ)).mul hg.contDiffAt
    exact hSmooth.congr_of_eventuallyEq (Eventually.of_forall (S.composedFull_apply k i))

/-- A single common fixed infrared factor makes the composite full symbol
smooth even at zero. The principal action is the true ordered composition. -/
def RealOrderedAngularMatrix.afterOriginalProjection (S : RealOrderedAngularMatrix) :
    ClassicalMatrixMultiplier OrderedPair where
  full := S.composedFull
  principal ξ := S.complex ξ * principalGaugeProjectionMatrix ξ
  full_smooth := S.composedFull_smooth
  principal_smooth k i := by
    change ContDiffOn ℝ ∞ (fun ξ : E => ∑ j : OrderedPair,
      S.complex ξ k j * (P01.gaugeProjectionSymbol j.1 j.2 i.1 i.2 ξ : ℂ)) ({0}ᶜ : Set E)
    apply ContDiffOn.sum
    intro j _
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn (S.smooth k j)).mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (gaugeProjectionSymbol_contDiffOn _ _ _ _))
  principal_degree k i t ht ξ _ := by
    simp only [Matrix.mul_apply, RealOrderedAngularMatrix.complex, S.degree t ht ξ,
      principalGaugeProjectionMatrix, gaugeProjectionSymbol_scale _ _ _ _ t ht]
  order_minus_one k i := by
    refine ⟨2 / tau + 1, 0, le_rfl, ?_⟩
    intro ξ hξ
    have hOut : ξ ∉ Metric.closedBall 0 (2 / tau) := by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]
      exact (lt_add_of_pos_right _ zero_lt_one).trans_le hξ
    have hEq : S.composedFull k i ξ = (S.complex ξ * principalGaugeProjectionMatrix ξ) k i := by
      change (∑ j : OrderedPair, productSymbol (S.coefficient k j)
        (regularizedProjectionComponentSymbol j.1 j.2 i.1 i.2) ξ) = _
      simp only [productSymbol_apply, S.coefficient_apply, Matrix.mul_apply,
        regularizedProjectionComponentSymbol_eq_off_ball _ _ _ _ _ hOut,
        principalProjectionComponentSymbol_apply, principalGaugeProjectionMatrix]
    change (1 + ‖ξ‖) * ‖S.composedFull k i ξ - _‖ ≤ 0
    simp only [hEq, sub_self, norm_zero, mul_zero, le_refl]

/-- The full matrix is literally the same original infrared cutoff times
the ordered principal, with the repository's radian Fourier normalization. -/
theorem RealOrderedAngularMatrix.afterOriginalProjection_full (S : RealOrderedAngularMatrix)
    (k i : OrderedPair) (ξ : E) :
    S.afterOriginalProjection.full k i ξ =
      (gaugeProjectionInfrared ‖tau • ξ‖ : ℂ) * S.afterOriginalProjection.principal ξ k i := by
  have ht : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  change S.composedFull k i ξ = _ * (S.complex ξ * principalGaugeProjectionMatrix ξ) k i
  rw [S.composedFull_apply, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [regularizedGaugeProjectionSymbol, gaugeProjectionSymbol_scale _ _ _ _ tau ht, Complex.ofReal_mul]
  simp only [principalGaugeProjectionMatrix]
  ring

/-- The actual full multiplier acts on the identical infrared-regularized
ordered field, including all of its exterior support. -/
theorem RealOrderedAngularMatrix.afterOriginalProjection_output (S : RealOrderedAngularMatrix)
    (u : OrderedPair → ComplexL2 E) (k : OrderedPair) :
    S.afterOriginalProjection.output u k = S.output (originalOrderedProjectedField u) k := by
  simp only [ClassicalMatrixMultiplier.output, RealOrderedAngularMatrix.afterOriginalProjection,
    RealOrderedAngularMatrix.composedFull, fourierMultiplier_finiteSum, fourierMultiplier_product,
    RealOrderedAngularMatrix.output, originalOrderedProjectedField, map_sum]
  exact Finset.sum_comm

end Burnett.C02
