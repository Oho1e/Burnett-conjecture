import Burnett.Analysis.FrozenScreen.Symbol
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option maxHeartbeats 3400000

noncomputable section

namespace Burnett.V06

open Matrix Set Burnett.RicciSymbol
open scoped Matrix BigOperators ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem smooth_dot_on (U : Set E) (u v : E → Covector)
    (hu : ∀ i, ContDiffOn ℝ ∞ (fun x => u x i) U)
    (hv : ∀ i, ContDiffOn ℝ ∞ (fun x => v x i) U) :
    ContDiffOn ℝ ∞ (fun x => u x ⬝ᵥ v x) U :=
  ContDiffOn.sum (fun i _ => (hu i).mul (hv i))

private theorem smooth_matrix_action_on (U : Set E) (A : E → ScreenMatrix) (v : E → Covector)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U)
    (hv : ∀ j, ContDiffOn ℝ ∞ (fun x => v x j) U) (i : Index) :
    ContDiffOn ℝ ∞ (fun x => (A x *ᵥ v x) i) U := by
  change ContDiffOn ℝ ∞ (fun x => ∑ j, A x i j * v x j) U
  exact ContDiffOn.sum (fun j _ => (hA i j).mul (hv j))

private theorem smooth_matrix_mul_on (U : Set E) (A B : E → ScreenMatrix)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U)
    (hB : ∀ i j, ContDiffOn ℝ ∞ (fun x => B x i j) U) (i j : Index) :
    ContDiffOn ℝ ∞ (fun x => (A x * B x) i j) U := by
  rw [show (fun x => (A x * B x) i j) = (fun x => ∑ k, A x i k * B x k j) from by
    funext x; rw [Matrix.mul_apply]]
  exact ContDiffOn.sum (fun k _ => (hA i k).mul (hB k j))

private theorem smooth_det_on (U : Set E) (A : E → ScreenMatrix)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) :
    ContDiffOn ℝ ∞ (fun x => (A x).det) U := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum (fun σ _ => contDiffOn_const.mul (contDiffOn_prod (fun i _ => hA (σ i) i)))

private theorem smooth_matrix_inverse_on (U : Set E) (A : E → ScreenMatrix)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U)
    (hInv : ∀ x ∈ U, (A x).det ≠ 0) (i j : Index) :
    ContDiffOn ℝ ∞ (fun x => (A x)⁻¹ i j) U := by
  have hAdj : ContDiffOn ℝ ∞ (fun x => (A x).adjugate i j) U := by
    simp only [Matrix.adjugate_apply]
    apply smooth_det_on U (fun x => (A x).updateRow j (Pi.single i (1 : ℝ)))
    intro k l
    by_cases hek : k = j
    · subst k
      simpa using (contDiffOn_const : ContDiffOn ℝ ∞
        (fun _ : E => (Pi.single i (1 : ℝ) : Index → ℝ) l) U)
    · simpa [Matrix.updateRow_apply, hek] using hA k l
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul] using
    (((smooth_det_on U A hA).inv hInv).mul hAdj)

/-- Smoothness of the actual normalized screen symbol on its domain. The
metric, input tensor, and frequency can vary together in the same parameter. -/
theorem frozenScreenSymbol_contDiffOn
    (U : Set E) (B H : E → ScreenMatrix) (q : E → Covector)
    (hB : ∀ i j, ContDiffOn ℝ ∞ (fun x => B x i j) U)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun x => H x i j) U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x => q x i) U)
    (hq₀ : ∀ x ∈ U, q x ≠ 0)
    (hw₀ : ∀ x ∈ U, screenSecondDirection (B x) (screenUnitCovector (q x)) ≠ 0)
    (hA₀ : ∀ x ∈ U, (screenMetricExtension (B x)
      (screenDirectionProjection (B x) (screenUnitCovector (q x)))).det ≠ 0)
    (i j : Index) :
    ContDiffOn ℝ ∞ (fun x => frozenScreenSymbol (B x) (H x) (q x) i j) U := by
  let e (x : E) := screenUnitCovector (q x)
  let w (x : E) := screenSecondDirection (B x) (e x)
  let Q (x : E) := screenDirectionProjection (B x) (e x)
  let A (x : E) := screenMetricExtension (B x) (Q x)
  let R (x : E) := screenInverse (B x) (Q x)
  let S (x : E) := Q x * H x * Q x
  have hn (x : E) (hx : x ∈ U) : q x ⬝ᵥ q x ≠ 0 := fun h => hq₀ x hx (dotProduct_self_eq_zero.mp h)
  have hsqrt (x : E) (hx : x ∈ U) : Real.sqrt (q x ⬝ᵥ q x) ≠ 0 := by
    have hnPos : 0 < q x ⬝ᵥ q x := lt_of_le_of_ne
      (Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)) (Ne.symm (hn x hx))
    exact (Real.sqrt_pos.2 hnPos).ne'
  have he (k : Index) : ContDiffOn ℝ ∞ (fun x => e x k) U :=
    (((smooth_dot_on U q q hQ hQ).sqrt hn).inv hsqrt).mul (hQ k)
  let Be (x : E) := B x *ᵥ e x
  have hBe (k : Index) : ContDiffOn ℝ ∞ (fun x => Be x k) U :=
    smooth_matrix_action_on U B e hB he k
  have hw (k : Index) : ContDiffOn ℝ ∞ (fun x => w x k) U :=
    (hBe k).sub ((smooth_dot_on U e Be he hBe).mul (he k))
  have hww (x : E) (hx : x ∈ U) : w x ⬝ᵥ w x ≠ 0 :=
    fun h => hw₀ x hx (dotProduct_self_eq_zero.mp h)
  have hQMat (k l : Index) : ContDiffOn ℝ ∞ (fun x => Q x k l) U := by
    simpa only [Q, screenDirectionProjection, w, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, vecMulVec_apply] using
      ((contDiffOn_const (c := (1 : ScreenMatrix) k l)).sub ((he k).mul (he l))).sub
        (((smooth_dot_on U w w hw hw).inv hww).mul ((hw k).mul (hw l)))
  have hQB := smooth_matrix_mul_on U Q B hQMat hB
  have hQBQ := smooth_matrix_mul_on U (fun x => Q x * B x) Q hQB hQMat
  have hA (k l : Index) : ContDiffOn ℝ ∞ (fun x => A x k l) U := by
    simpa only [A, screenMetricExtension, Matrix.add_apply, Matrix.sub_apply] using
      (hQBQ k l).add (contDiffOn_const.sub (hQMat k l))
  have hAi := smooth_matrix_inverse_on U A hA hA₀
  have hQAi := smooth_matrix_mul_on U Q (fun x => (A x)⁻¹) hQMat hAi
  have hR (k l : Index) : ContDiffOn ℝ ∞ (fun x => R x k l) U :=
    smooth_matrix_mul_on U (fun x => Q x * (A x)⁻¹) Q hQAi hQMat k l
  have hQH := smooth_matrix_mul_on U Q H hQMat hH
  have hS (k l : Index) : ContDiffOn ℝ ∞ (fun x => S x k l) U :=
    smooth_matrix_mul_on U (fun x => Q x * H x) Q hQH hQMat k l
  have hBS := smooth_matrix_mul_on U B S hB hS
  have hTr : ContDiffOn ℝ ∞ (fun x => Matrix.trace (B x * S x)) U :=
    ContDiffOn.sum (fun k _ => hBS k k)
  change ContDiffOn ℝ ∞ (fun x => frozenScreenProjection (B x) (Q x) (H x) i j) U
  change ContDiffOn ℝ ∞ (fun x => S x i j - Matrix.trace (B x * S x) / 2 * R x i j) U
  exact (hS i j).sub ((hTr.div_const 2).mul (hR i j))

end Burnett.V06
