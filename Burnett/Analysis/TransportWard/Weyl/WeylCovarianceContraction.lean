import Burnett.Analysis.Microlocal.Overlap.AtlasAngularPhaseEncoding
import Burnett.Analysis.Microlocal.PhysicalDensity

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2400

noncomputable section

namespace Burnett.V03

open Function Set Burnett.RicciSymbol Burnett.Geometry ConnectionDifference ManifoldMetric MaximalChart
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity)
open scoped BigOperators ComplexConjugate ComplexOrder ContDiff Manifold Matrix MatrixOrder

/-- Contract a symbol in the independent field slots against the ordered
pair covariance. The selected entries carry exactly their actual scales. -/
def scaledOrderedCovarianceContraction {ι : Type*} [Fintype ι]
    (H : ι → ι → ℂ) (e : ι → Pair) (s : ι → ℝ) (C : Matrix Pair Pair ℂ) : ℂ :=
  ∑ i, ∑ j, H i j * ((s j : ℂ) * (s i : ℂ) * C (e j) (e i))

private theorem scaledOrderedCovarianceContraction_gram {ι : Type*} [Fintype ι]
    (H : ι → ι → ℂ) (e : ι → Pair) (s : ι → ℝ) (U : Matrix Pair Pair ℂ) :
    scaledOrderedCovarianceContraction H e s (U * Uᴴ) =
      ∑ k : Pair, ∑ i : ι, ∑ j : ι,
        H i j * ((s j : ℂ) * U (e j) k) * conj ((s i : ℂ) * U (e i) k) := by
  unfold scaledOrderedCovarianceContraction
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,RCLike.star_def,Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  simp only [map_mul,Complex.conj_ofReal]
  ring

/-- Rank-one Ricci-kernel compression lifts to the same positive
covariance. Both matrix orders and the quarter normalization are exact. -/
theorem scaledOrderedCovarianceContraction_of_kernel_compression {ι : Type*} [Fintype ι]
    (H : ι → ι → ℂ) (e : ι → Pair) (s : ι → ℝ) (C : Matrix Pair Pair ℂ) (hC : C.PosSemidef)
    (G : Tensor2) (w f : ℝ) (κ : Prop) [Decidable κ]
    (h : ∀ v : Pair → ℂ, v ∈ LinearMap.range C.mulVecLin →
      (∑ i, ∑ j, H i j * ((s j : ℂ) * v (e j)) * conj ((s i : ℂ) * v (e i))) =
        if κ then
          4 * (w : ℂ) * (f : ℂ) * ((1 / 4 : ℂ) * hermitianPhysicalPairing G (tensorOfVector v) (tensorOfVector v))
        else 0) :
    scaledOrderedCovarianceContraction H e s C =
      if κ then 4 * (w : ℂ) * (f : ℂ) * ((1 / 4 : ℂ) * physicalContraction G C) else 0 := by
  let U := densitySqrt C
  have hGram : U * Uᴴ = C := densitySqrt_mul_self hC
  have hCol (k : Pair) : U.col k ∈ LinearMap.range C.mulVecLin := by
    rw [← range_densitySqrt hC]
    refine ⟨Pi.single k 1,?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  have hTerm (k : Pair) := h (U.col k) (hCol k)
  rw [← hGram, scaledOrderedCovarianceContraction_gram, physicalContraction_gram]
  change (∑ k : Pair, ∑ i : ι, ∑ j : ι, H i j * ((s j : ℂ) * (U.col k) (e j)) *
      conj ((s i : ℂ) * (U.col k) (e i))) = _
  simp only [hTerm]
  by_cases hk : κ
  · simp only [if_pos hk,Finset.mul_sum]
  · simp only [if_neg hk,Finset.sum_const_zero]

/-- The quarter contraction of a positive ordered covariance with a
symmetric inverse metric is already real. -/
theorem physicalContraction_quarter_eq_real_of_posSemidef
    (G : Tensor2) (hG : IsSymmetricTensor G) (C : Matrix Pair Pair ℂ) (hC : C.PosSemidef) :
    (1 / 4 : ℂ) * physicalContraction G C =
      ((((1 / 4 : ℂ) * physicalContraction G C).re : ℝ) : ℂ) := by
  have hIm : (physicalContraction G C).im = 0 := by
    rw [← densitySqrt_mul_self hC,physicalContraction_gram,Complex.im_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    let v := tensorOfVector ((densitySqrt C).col j)
    change (hermitianPhysicalPairing G v v).im = 0
    have he := congrArg Complex.im (hermitianPhysicalPairing_conj_symm G v v hG)
    simp only [Complex.conj_im] at he
    linarith only [he]
  apply Complex.ext
  · exact (Complex.ofReal_re _).symm
  · rw [Complex.ofReal_im, Complex.mul_im,hIm,mul_zero,zero_add]
    norm_num

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem complexSum_coordinate_square (ξ : Covector) :
    (∑ l : Fin 4, (ξ l : ℂ) * (ξ l : ℂ)) = ((‖(WithLp.toLp 2 ξ : CoordinateSpace)‖^2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro l _
  change (ξ l : ℂ) * (ξ l : ℂ) = ((‖ξ l‖^2 : ℝ) : ℂ)
  rw [Real.norm_eq_abs,sq_abs,Complex.ofReal_pow,pow_two]

/-- The four equal derivative legs undo the angular denominator using the
actual auxiliary unit covector, with no additional radial normalization. -/
theorem atlasOrderedJetEntry_diagonal_contraction {ι : Type*} [Fintype ι]
    {r : Metric (M := M)} (c : AtlasChart M) (A : AmplitudeCovarianceDensity r)
    (p : Cosphere r) (hξ : atlasChartUnitCovector c p ≠ 0)
    (H : ι → ι → ℂ) (e : ι → Pair) (s : ι → ℝ) :
    let ξ := atlasChartUnitCovector c p
    let d : ℂ := ((‖(WithLp.toLp 2 ξ : CoordinateSpace)‖^2 : ℝ) : ℂ)
    (∑ i : ι, ∑ j : ι, ∑ l : Fin 4,
      H i j * ((s j : ℂ) * (s i : ℂ)) * d⁻¹ * atlasOrderedJetEntry c A p (l,e i) (l,e j)) =
      scaledOrderedCovarianceContraction H e s (atlasAmplitudeMatrix c A p) := by
  intro ξ d
  have hξE : (WithLp.toLp 2 ξ : CoordinateSpace) ≠ 0 := by
    intro hz
    exact hξ (congrArg WithLp.ofLp hz)
  have hd : d ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hξE))
  unfold scaledOrderedCovarianceContraction
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have hFactor :
      (∑ l : Fin 4, H i j * ((s j : ℂ) * (s i : ℂ)) * d⁻¹ *
        atlasOrderedJetEntry c A p (l,e i) (l,e j)) =
      (H i j * ((s j : ℂ) * (s i : ℂ)) * d⁻¹ * atlasAmplitudeMatrix c A p (e j) (e i)) *
        ∑ l : Fin 4, (ξ l : ℂ) * (ξ l : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    change H i j * ((s j : ℂ) * (s i : ℂ)) * d⁻¹ *
      ((ξ l : ℂ) * (ξ l : ℂ) * atlasAmplitudeMatrix c A p (e j) (e i)) = _
    ring
  rw [hFactor, complexSum_coordinate_square]
  change (_ * d⁻¹ * _) * d = _
  field_simp [hd]

end Burnett.V03
