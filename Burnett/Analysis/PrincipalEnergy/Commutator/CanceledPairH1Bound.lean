import Burnett.Analysis.PrincipalEnergy.Commutator.CanceledPairLinearity
import Burnett.Analysis.PrincipalEnergy.Quantization.ActualWeakPair

set_option autoImplicit false
set_option maxHeartbeats 3400000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateH1)
open scoped ComplexConjugate InnerProductSpace BigOperators

private theorem scalarSchwartzProduct_L2_bound (r f : SchwartzMap Space ℂ) {U : ℝ} (hU : 0≤U)
    (hValue : ∀ x, ‖r x‖≤U) : ‖(scalarSchwartzProduct r f).toLp 2 volume‖≤U*‖f.toLp 2 volume‖ := by
  let g := scalarSchwartzProduct r f
  have hSq (u : SchwartzMap Space ℂ) : ‖u.toLp 2 volume‖^2=∫ x, ‖u x‖^2 := by
    rw [l2_norm_sq_integral]
    exact integral_congr_ae ((u.coeFn_toLp 2 volume).fun_comp fun z => ‖z‖^2)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hU (norm_nonneg _))).mp
  change ‖g.toLp 2 volume‖^2≤(U*‖f.toLp 2 volume‖)^2
  rw [mul_pow,hSq,hSq,← integral_const_mul]
  apply integral_mono ((g.memLp 2 volume).integrable_norm_pow (by decide : (2:ℕ) ≠ 0))
    (((f.memLp 2 volume).integrable_norm_pow (by decide : (2:ℕ) ≠ 0)).const_mul _)
  intro x
  change ‖scalarSchwartzProduct r f x‖^2≤U^2*‖f x‖^2
  rw [scalarSchwartzProduct_apply,norm_mul,← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (hValue x) (norm_nonneg _)) 2

theorem schwartz_L2_norm_le_coordinateH1 (f : SchwartzMap Space ℂ) :
    ‖f.toLp 2 volume‖≤coordinateH1 f := by
  unfold coordinateH1
  apply Real.le_sqrt_of_sq_le
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- An \(H^1\) pairing bound for the actual corrected form, derived from
the full action and physical paraproduct before using any \(L^2\) theorem
for the commutator. -/
theorem exists_canceledCoefficientPair_H1_bound {a : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (hBase : CompactBaseOrderOne a) (hCont : Continuous (Function.uncurry a))
    (hSym : FirstOrderFormalSymmetry a) (M : ℝ) (hM : 0≤M) :
    ∃ D : ℝ, 0≤D ∧ ∀ (r : SchwartzMap Space ℂ) (U V : ℝ),
      0≤U → 0≤V → (∀ x, conj (r x)=r x) → (∀ x, ‖r x‖≤U) →
      ∀ (P : SchwartzMap Space ℂ → ComplexL2 Space),
      (∀ f, ‖P f‖≤M*(U+V)*‖f.toLp 2 volume‖) →
      ∀ f g : SchwartzMap Space ℂ,
        ‖canceledCoefficientPair a r P f g‖≤D*(U+V)*coordinateH1 f*coordinateH1 g := by
  obtain ⟨K,hK,hWeak⟩ := exists_actualCoefficientCommutator_weakPair_bound ha hBase hCont hSym
  refine ⟨2*(K+M),by positivity,?_⟩
  intro r U V hU hV hReal hValue P hP f g
  have hF : ‖(scalarSchwartzProduct r f-(0:ℂ) • f).toLp 2 volume‖≤U*‖f.toLp 2 volume‖ := by
    simpa only [zero_smul,sub_zero] using scalarSchwartzProduct_L2_bound r f hU hValue
  have hG : ‖(scalarSchwartzProduct r g-(0:ℂ) • g).toLp 2 volume‖≤U*‖g.toLp 2 volume‖ := by
    simpa only [zero_smul,sub_zero] using scalarSchwartzProduct_L2_bound r g hU hValue
  have hL (u : SchwartzMap Space ℂ) : ‖u.toLp 2 volume‖≤coordinateH1 u :=
    schwartz_L2_norm_le_coordinateH1 u
  have hH (u : SchwartzMap Space ℂ) : 0≤coordinateH1 u := Real.sqrt_nonneg _
  let B := coordinateH1 f*coordinateH1 g
  have hB : 0≤B := mul_nonneg (hH f) (hH g)
  let J := M*(U+V)
  have hJ : 0≤J := by dsimp only [J]; positivity
  have hSum : coordinateH1 f*‖g.toLp 2 volume‖+‖f.toLp 2 volume‖*coordinateH1 g≤B+B :=
    add_le_add (mul_le_mul_of_nonneg_left (hL g) (hH f)) (mul_le_mul_of_nonneg_right (hL f) (hH g))
  let T := ∫ x, conj (g x)*actualCoefficientCommutator a r f x
  let X := inner ℂ (g.toLp 2 volume) (P f)
  let Y := inner ℂ (P g) (f.toLp 2 volume)
  have hT : ‖T‖≤K*U*(B+B) := (hWeak r f g 0 (by simp) hReal U hU hF hG).trans
    (mul_le_mul_of_nonneg_left hSum (by positivity))
  have hXY : (‖X‖≤J*B) ∧ (‖Y‖≤J*B) := by
    have hProd : ‖f.toLp 2 volume‖*‖g.toLp 2 volume‖≤B :=
      mul_le_mul (hL f) (hL g) (norm_nonneg _) (hH f)
    constructor
    · calc
        _ ≤ ‖g.toLp 2 volume‖*‖P f‖ := norm_inner_le_norm _ _
        _ ≤ ‖g.toLp 2 volume‖*(J*‖f.toLp 2 volume‖) := mul_le_mul_of_nonneg_left (hP f) (norm_nonneg _)
        _ = J*(‖f.toLp 2 volume‖*‖g.toLp 2 volume‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hProd hJ
    · calc
        _ ≤ ‖P g‖*‖f.toLp 2 volume‖ := norm_inner_le_norm _ _
        _ ≤ (J*‖g.toLp 2 volume‖)*‖f.toLp 2 volume‖ := mul_le_mul_of_nonneg_right (hP g) (norm_nonneg _)
        _ = J*(‖f.toLp 2 volume‖*‖g.toLp 2 volume‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hProd hJ
  change ‖T-X+Y‖≤_
  calc
    _ ≤ ‖T‖+‖X‖+‖Y‖ := (norm_add_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ K*U*(B+B)+J*B+J*B := add_le_add (add_le_add hT hXY.1) hXY.2
    _ ≤ K*(U+V)*(B+B)+J*B+J*B := by
      exact add_le_add_right (add_le_add_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hV) hK) (add_nonneg hB hB)) _) _
    _ = _ := by dsimp only [J,B]; ring

end Burnett.Analysis.CarlesonEmbedding
