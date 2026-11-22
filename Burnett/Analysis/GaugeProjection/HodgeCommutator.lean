import Burnett.Analysis.GaugeProjection.TransverseDerivativePotential
import Burnett.Analysis.GaugeProjection.GaugeProjectionLp

set_option autoImplicit false
set_option maxHeartbeats 2900000

noncomputable section

namespace Burnett.P01

open Matrix
open Burnett.A02.FrequencySplit (E radianFourier radianFourier_scaled tau)
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative)
open scoped BigOperators FourierTransform Matrix

private def hodgeFrequency (ξ : E) : ComplexCovector := fun j => (ξ j : ℂ)

private def hodgeTransverseMatrix (ξ : E) : ComplexComponents :=
  (directionProjection (fun j => ξ j)).map Complex.ofReal

/-- One vector slot of the same Euclidean symbol used in the matrix projection. -/
def hodgeTransverse (ξ : E) : ComplexCovector →ₗ[ℂ] ComplexCovector :=
  (hodgeTransverseMatrix ξ).mulVecLin

/-- The longitudinal complement in that vector slot. -/
def hodgeLongitudinal (ξ : E) : ComplexCovector →ₗ[ℂ] ComplexCovector :=
  LinearMap.id - hodgeTransverse ξ

theorem hodgeTransverse_apply (ξ : E) (u : ComplexCovector) (i : Fin 4) :
    hodgeTransverse ξ u i = ∑ j, (directionProjectionEntry i j ξ : ℂ) * u j := rfl

private theorem hodgeTransverse_freq (ξ : E) : hodgeTransverse ξ (hodgeFrequency ξ) = 0 := by
  let x : Covector := fun j => ξ j
  have hx : directionProjection x *ᵥ x = 0 := by
    by_cases h : x = 0
    · simp [h]
    · exact directionProjection_kills_covector h
  funext a
  have ha := congrArg Complex.ofReal (congrFun hx a)
  simpa only [hodgeTransverse_apply, directionProjectionEntry, hodgeFrequency, x,
    Matrix.mulVec, dotProduct, Pi.zero_apply, Complex.ofReal_zero, Complex.ofReal_sum,
    Complex.ofReal_mul] using ha

private theorem hodgeTransverse_dot_zero (ξ : E) (v : ComplexCovector) :
    hodgeFrequency ξ ⬝ᵥ hodgeTransverse ξ v = 0 := by
  have hP : (hodgeTransverseMatrix ξ)ᵀ = hodgeTransverseMatrix ξ := by
    rw [hodgeTransverseMatrix, ← transpose_map, directionProjection_transpose]
  change hodgeFrequency ξ ⬝ᵥ (hodgeTransverseMatrix ξ *ᵥ v) = 0
  rw [dotProduct_mulVec, ← mulVec_transpose, hP]
  change hodgeTransverse ξ (hodgeFrequency ξ) ⬝ᵥ v = 0
  rw [hodgeTransverse_freq, zero_dotProduct]

private theorem hodgeLongitudinal_rank_one (ξ : E) (v : ComplexCovector) :
    hodgeLongitudinal ξ v =
      (((((fun j : Fin 4 => ξ j) ⬝ᵥ fun j : Fin 4 => ξ j)⁻¹ : ℝ) : ℂ) *
        (hodgeFrequency ξ ⬝ᵥ v)) • hodgeFrequency ξ := by
  let x : Covector := fun j => ξ j
  let a : ℂ := (((x ⬝ᵥ x)⁻¹ : ℝ) : ℂ)
  have hmat : hodgeTransverseMatrix ξ = 1 - a • vecMulVec (hodgeFrequency ξ) (hodgeFrequency ξ) := by
    ext i j
    simp only [hodgeTransverseMatrix, directionProjection, sub_apply, Matrix.smul_apply,
      Matrix.map_apply, Complex.ofReal_sub, vecMulVec_apply, smul_eq_mul, Complex.ofReal_mul,
      hodgeFrequency, a, x, one_apply]
    congr 1
    split <;> simp
  change v - (hodgeTransverseMatrix ξ *ᵥ v) = (a * (hodgeFrequency ξ ⬝ᵥ v)) • hodgeFrequency ξ
  rw [hmat, sub_mulVec, one_mulVec, sub_sub_cancel, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul]

private theorem hodgeLongitudinal_kills (ξ : E) (v : ComplexCovector)
    (hv : hodgeFrequency ξ ⬝ᵥ v = 0) : hodgeLongitudinal ξ v = 0 := by
  rw [hodgeLongitudinal_rank_one, hv, mul_zero, zero_smul]

abbrev HodgeSchwartzField := Fin 4 → SchwartzMap E ℂ

private def radianTestEval (ξ : E) : SchwartzMap E ℂ →ₗ[ℂ] ℂ where
  toFun f := SchwartzMap.fourierTransformCLM ℂ f (tau⁻¹ • ξ)
  map_add' f g := by simp only [map_add, SchwartzMap.add_apply]
  map_smul' c f := by simp only [map_smul, SchwartzMap.smul_apply, RingHom.id_apply]

private theorem tau_ne_zero : tau ≠ 0 :=
  (mul_pos (show (0 : ℝ) < 2 by norm_num) Real.pi_pos).ne'

private theorem radianTestEval_eq (ξ : E) (f : SchwartzMap E ℂ) :
    radianTestEval ξ f = radianFourier f ξ := by
  change 𝓕 (f : E → ℂ) (tau⁻¹ • ξ) = _
  rw [← radianFourier_scaled, smul_smul, mul_inv_cancel₀ tau_ne_zero, one_smul]

private theorem eq_of_radianTestEval {f g : SchwartzMap E ℂ}
    (h : ∀ ξ, radianTestEval ξ f = radianTestEval ξ g) : f = g := by
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext x
  have hx := h (tau • x)
  change (SchwartzMap.fourierTransformCLM ℂ f) (tau⁻¹ • (tau • x)) =
    (SchwartzMap.fourierTransformCLM ℂ g) (tau⁻¹ • (tau • x)) at hx
  rwa [smul_smul, inv_mul_cancel₀ tau_ne_zero, one_smul] at hx

private theorem radianTestEval_derivative (ξ : E) (a : Fin 4) (f : SchwartzMap E ℂ) :
    radianTestEval ξ (coordinateDerivative a f) = Complex.I * (ξ a : ℂ) * radianTestEval ξ f := by
  simpa only [radianTestEval_eq] using radianFourier_coordinateDerivative a f ξ

/-- Pointwise product of the two actual Schwartz functions in the commutator. -/
def hodgeProduct (f u : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) u.hasTemperateGrowth f

@[simp] theorem hodgeProduct_apply (f u : SchwartzMap E ℂ) (x : E) :
    hodgeProduct f u x = f x * u x := rfl

private theorem hodgeProduct_add (f u v : SchwartzMap E ℂ) :
    hodgeProduct f (u + v) = hodgeProduct f u + hodgeProduct f v := by
  ext x
  simp [mul_add]

private theorem hodgeProduct_sub (f u v : SchwartzMap E ℂ) :
    hodgeProduct f (u - v) = hodgeProduct f u - hodgeProduct f v := by
  ext x
  simp [mul_sub]

private theorem hodgeProduct_sum (f : SchwartzMap E ℂ) (u : Fin 4 → SchwartzMap E ℂ) :
    hodgeProduct f (∑ j, u j) = ∑ j, hodgeProduct f (u j) := by
  have hs (g : SchwartzMap E ℂ) : hodgeProduct f g =
      SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) f.hasTemperateGrowth g := by
    ext x
    exact mul_comm _ _
  simp_rw [hs, map_sum]

private theorem coordinateDerivative_hodgeProduct (j : Fin 4) (f u : SchwartzMap E ℂ) :
    coordinateDerivative j (hodgeProduct f u) =
      hodgeProduct (coordinateDerivative j f) u + hodgeProduct f (coordinateDerivative j u) := by
  ext x
  simp only [coordinateDerivative, SchwartzMap.pderivCLM_apply, SchwartzMap.add_apply,
    hodgeProduct_apply]
  change fderiv ℝ ((f : E → ℂ) * (u : E → ℂ)) x (EuclideanSpace.single j 1) = _
  rw [fderiv_mul f.differentiableAt u.differentiableAt]
  simp [mul_comm, add_comm]

/-- First index is the divergence index and the second is the output coordinate. -/
def hodgeSkew (b : Fin 4) (A : HodgeSchwartzField) (j i : Fin 4) : SchwartzMap E ℂ :=
  (if j = b then A i else 0) - (if i = b then A j else 0)

private theorem hodgeSkew_antisymm (b : Fin 4) (A : HodgeSchwartzField) (j i : Fin 4) :
    hodgeSkew b A j i = -hodgeSkew b A i j := by
  simp [hodgeSkew, neg_sub]

private theorem hodgeSkew_divergence (b : Fin 4) (A : HodgeSchwartzField)
    (hdiv : ∑ j, coordinateDerivative j (A j) = 0) (i : Fin 4) :
    ∑ j, coordinateDerivative j (hodgeSkew b A j i) = coordinateDerivative b (A i) := by
  classical
  simp only [hodgeSkew, map_sub, Finset.sum_sub_distrib]
  have h₁ : (∑ j, coordinateDerivative j (if j = b then A i else 0)) =
      coordinateDerivative b (A i) := by
    calc
      _ = ∑ j, if j = b then coordinateDerivative j (A i) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : j = b <;> simp [h]
      _ = _ := by simp
  rw [h₁]
  by_cases h : i = b
  · simp [h, hdiv]
  · simp [h]

/-- The actual radian Fourier spectrum in the four covector coordinates. -/
def hodgeSpectrum (w : HodgeSchwartzField) (ξ : E) : ComplexCovector :=
  fun i => radianFourier (w i) ξ

private theorem radianTestEval_field (ξ : E) (w : HodgeSchwartzField) (i : Fin 4) :
    radianTestEval ξ (w i) = hodgeSpectrum w ξ i := radianTestEval_eq ξ (w i)

private theorem hodgeSpectrum_add (v w : HodgeSchwartzField) (ξ : E) :
    hodgeSpectrum (v + w) ξ = hodgeSpectrum v ξ + hodgeSpectrum w ξ := by
  ext i
  simp only [hodgeSpectrum, ← radianTestEval_eq, Pi.add_apply, map_add]

private theorem hodgeSpectrum_sub (v w : HodgeSchwartzField) (ξ : E) :
    hodgeSpectrum (v - w) ξ = hodgeSpectrum v ξ - hodgeSpectrum w ξ := by
  ext i
  simp only [hodgeSpectrum, ← radianTestEval_eq, Pi.sub_apply, map_sub]

private theorem hodgeDivergence_transverse (w A : HodgeSchwartzField)
    (hA : ∀ ξ, hodgeSpectrum A ξ = hodgeTransverse ξ (hodgeSpectrum w ξ)) :
    ∑ j, coordinateDerivative j (A j) = 0 := by
  apply eq_of_radianTestEval
  intro ξ
  simp only [map_sum, map_zero, radianTestEval_derivative, radianTestEval_field, mul_assoc,
    ← Finset.mul_sum]
  change Complex.I * (hodgeFrequency ξ ⬝ᵥ hodgeSpectrum A ξ) = 0
  rw [hA, hodgeTransverse_dot_zero, mul_zero]

private theorem hodgeDerivative_longitudinal (b i : Fin 4) (w A : HodgeSchwartzField)
    (hA : ∀ ξ, hodgeSpectrum A ξ = hodgeTransverse ξ (hodgeSpectrum w ξ)) :
    coordinateDerivative b ((w - A) i) = coordinateDerivative i ((w - A) b) := by
  apply eq_of_radianTestEval
  intro ξ
  simp only [radianTestEval_derivative, radianTestEval_field]
  rw [hodgeSpectrum_sub, hA]
  change Complex.I * (ξ b : ℂ) * hodgeLongitudinal ξ (hodgeSpectrum w ξ) i =
    Complex.I * (ξ i : ℂ) * hodgeLongitudinal ξ (hodgeSpectrum w ξ) b
  rw [hodgeLongitudinal_rank_one]
  simp only [Pi.smul_apply, smul_eq_mul, hodgeFrequency]
  ring

private theorem hodgeTransverse_kills_gradient (ξ : E) (u : SchwartzMap E ℂ) :
    hodgeTransverse ξ (hodgeSpectrum (fun i => coordinateDerivative i u) ξ) = 0 := by
  have heq : hodgeSpectrum (fun i => coordinateDerivative i u) ξ =
      (Complex.I * radianTestEval ξ u) • hodgeFrequency ξ := by
    ext i
    rw [hodgeSpectrum, ← radianTestEval_eq, radianTestEval_derivative]
    simp [hodgeFrequency, mul_assoc, mul_comm, mul_left_comm]
  rw [heq, map_smul, hodgeTransverse_freq, smul_zero]

private theorem hodgeLongitudinal_kills_skew_divergence (ξ : E)
    (B : Fin 4 → Fin 4 → SchwartzMap E ℂ) (hB : ∀ j i, B j i = -B i j) :
    hodgeLongitudinal ξ (hodgeSpectrum (fun i => ∑ j, coordinateDerivative j (B j i)) ξ) = 0 := by
  apply hodgeLongitudinal_kills
  let T : ComplexComponents := fun j i => radianTestEval ξ (B j i)
  let S : ComplexComponents := fun j i => Complex.I * (ξ j : ℂ) * (ξ i : ℂ)
  have hT : ∀ j i, T j i = -T i j := by
    intro j i
    change radianTestEval ξ (B j i) = -radianTestEval ξ (B i j)
    rw [hB, map_neg]
  have hS : ∀ j i, S j i = S i j := by
    intro j i
    dsimp [S]
    ring
  have heq : hodgeFrequency ξ ⬝ᵥ hodgeSpectrum (fun i => ∑ j, coordinateDerivative j (B j i)) ξ =
      ∑ i, ∑ j, T i j * S i j := by
    rw [Finset.sum_comm]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro i _
    simp only [hodgeSpectrum, ← radianTestEval_eq, map_sum, radianTestEval_derivative,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [T, S, hodgeFrequency]
    ring
  exact heq.trans (skew_symmetric_contraction_zero T S hT hS)

/-- The actual one-slot differentiated commutator on a Schwartz Hodge pair.
The transverse component is specified by its Fourier symbol. Both coefficients
on the right are derivatives of the original \(f\). -/
theorem hodgeCommutator_spectrum (b : Fin 4) (f : SchwartzMap E ℂ)
    (w A : HodgeSchwartzField)
    (hA : ∀ ξ, hodgeSpectrum A ξ = hodgeTransverse ξ (hodgeSpectrum w ξ)) (ξ : E) :
    hodgeTransverse ξ (hodgeSpectrum (fun i => hodgeProduct f (coordinateDerivative b (w i))) ξ) -
      hodgeSpectrum (fun i => hodgeProduct f (coordinateDerivative b (A i))) ξ =
    -hodgeTransverse ξ (hodgeSpectrum (fun i => hodgeProduct (coordinateDerivative i f)
      ((w - A) b)) ξ) +
    hodgeLongitudinal ξ (hodgeSpectrum (fun i =>
      ∑ j, hodgeProduct (coordinateDerivative j f) (hodgeSkew b A j i)) ξ) := by
  let C := w - A
  let contrib (u : HodgeSchwartzField) : HodgeSchwartzField :=
    fun i => hodgeProduct f (coordinateDerivative b (u i))
  let grad : HodgeSchwartzField := fun i => hodgeProduct (coordinateDerivative i f) (C b)
  let skew : HodgeSchwartzField := fun i =>
    ∑ j, hodgeProduct (coordinateDerivative j f) (hodgeSkew b A j i)
  have hw : contrib w = contrib C + contrib A := by
    funext i
    dsimp only [contrib, C, Pi.add_apply, Pi.sub_apply]
    rw [map_sub, hodgeProduct_sub]
    abel
  have hcurl (i : Fin 4) : coordinateDerivative b (C i) = coordinateDerivative i (C b) :=
    hodgeDerivative_longitudinal b i w A hA
  have hC : contrib C = (fun i => coordinateDerivative i (hodgeProduct f (C b))) - grad := by
    funext i
    dsimp only [contrib, grad, Pi.sub_apply]
    rw [hcurl, coordinateDerivative_hodgeProduct, add_sub_cancel_left]
  have hdiv := hodgeDivergence_transverse w A hA
  have hskew (i : Fin 4) := hodgeSkew_divergence b A hdiv i
  have hA_prod : contrib A = (fun i => ∑ j, coordinateDerivative j
      (hodgeProduct f (hodgeSkew b A j i))) - skew := by
    funext i
    dsimp only [contrib, skew, Pi.sub_apply]
    rw [← hskew i, hodgeProduct_sum]
    simp only [coordinateDerivative_hodgeProduct, Finset.sum_add_distrib, add_sub_cancel_left]
  have hP : hodgeTransverse ξ (hodgeSpectrum (contrib C) ξ) =
      -hodgeTransverse ξ (hodgeSpectrum grad ξ) := by
    rw [hC, hodgeSpectrum_sub, map_sub, hodgeTransverse_kills_gradient, zero_sub]
  have hQ : hodgeLongitudinal ξ (hodgeSpectrum (contrib A) ξ) =
      -hodgeLongitudinal ξ (hodgeSpectrum skew ξ) := by
    have hs (j i : Fin 4) : hodgeProduct f (hodgeSkew b A j i) =
        -hodgeProduct f (hodgeSkew b A i j) := by
      rw [hodgeSkew_antisymm b A j i]
      ext x
      simp only [hodgeProduct_apply, SchwartzMap.neg_apply, mul_neg]
    rw [hA_prod, hodgeSpectrum_sub, map_sub, hodgeLongitudinal_kills_skew_divergence ξ _ hs,
      zero_sub]
  change hodgeTransverse ξ (hodgeSpectrum (contrib w) ξ) - hodgeSpectrum (contrib A) ξ =
    -hodgeTransverse ξ (hodgeSpectrum grad ξ) + hodgeLongitudinal ξ (hodgeSpectrum skew ξ)
  calc
    _ = hodgeTransverse ξ (hodgeSpectrum (contrib C) ξ) -
        hodgeLongitudinal ξ (hodgeSpectrum (contrib A) ξ) := by
      rw [hw, hodgeSpectrum_add, map_add]
      change _ + hodgeTransverse ξ (hodgeSpectrum (contrib A) ξ) - hodgeSpectrum (contrib A) ξ =
        _ - (hodgeSpectrum (contrib A) ξ - hodgeTransverse ξ (hodgeSpectrum (contrib A) ξ))
      abel
    _ = _ := by rw [hP, hQ, sub_neg_eq_add]

end Burnett.P01
