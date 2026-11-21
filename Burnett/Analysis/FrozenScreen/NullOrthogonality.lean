import Burnett.Analysis.FrozenScreen.Projection
import Burnett.Algebra.MinkowskiNormalize
import Burnett.Algebra.LorentzPhysical
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Burnett.V06

open Matrix Burnett.RicciSymbol TensorFrame MinkowskiNormalize
open scoped BigOperators Matrix

private theorem symbolNorm_eq_dot_mulVec (B : ScreenMatrix) (v : Covector) :
    symbolNorm B v = v ⬝ᵥ (B *ᵥ v) := by
  simp only [symbolNorm, dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem dot_mulVec_comm (B : ScreenMatrix) (hB : Bᵀ = B) (v e : Covector) :
    v ⬝ᵥ (B *ᵥ e) = e ⬝ᵥ (B *ᵥ v) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hB, dotProduct_comm]

private theorem quadratic_polarization (B : ScreenMatrix) (hB : Bᵀ = B) (v e : Covector) :
    symbolNorm B (v + e) = symbolNorm B v + symbolNorm B e + 2 * (v ⬝ᵥ (B *ᵥ e)) := by
  simp only [symbolNorm_eq_dot_mulVec, mulVec_add, add_dotProduct, dotProduct_add]
  rw [dot_mulVec_comm B hB e v]
  ring

private theorem pairing_as_quadratic (v e : Covector) :
    pairing (v + e) (v + e) = pairing v v + pairing e e + 2 * pairing v e := by
  unfold pairing
  simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem covector_add_frame (F : Tensor2) (v e : Covector) :
    covector F (v + e) = covector F v + covector F e := by
  funext i
  simp only [covector, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem covector_smul_frame (F : Tensor2) (c : ℝ) (v : Covector) :
    covector F (c • v) = c • covector F v := by
  funext i
  simp only [covector, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem transformed_dot_mulVec (B : ScreenMatrix) (f : LorentzFrame B) (v e : Covector) :
    pairing (covector f.components v) (covector f.components e) = v ⬝ᵥ (B *ᵥ e) := by
  have hB : Bᵀ = B := by
    ext i j
    exact LorentzPhysical.metric_symmetric B f j i
  have h := pairing_as_quadratic (covector f.components v) (covector f.components e)
  rw [← covector_add_frame, pairing_self, pairing_self, pairing_self,
    LorentzPhysical.transformed_symbolNorm, LorentzPhysical.transformed_symbolNorm,
    LorentzPhysical.transformed_symbolNorm, quadratic_polarization B hB] at h
  linarith

/-- On the Lorentz-orthogonal complement of a nonzero null covector, the
quadratic form is nonnegative and its radical is precisely the null line. -/
theorem null_orthogonal_quadratic (B : ScreenMatrix) (frame : LorentzFrame B)
    (e v : Covector) (he : e ≠ 0) (hn : symbolNorm B e = 0)
    (hv : v ⬝ᵥ (B *ᵥ e) = 0) :
    0 ≤ symbolNorm B v ∧ (symbolNorm B v = 0 ↔ ∃ c : ℝ, v = c • e) := by
  obtain ⟨normal, hnormal⟩ := exists_normalizing_frame (covector frame.components e)
    (LorentzPhysical.transformed_covector_ne_zero B frame e he)
    ((LorentzPhysical.transformed_symbolNorm B frame e).trans hn)
  let f := FrameComposition.composeFrames B frame normal
  have he' : covector f.components e = NullScreen.nullCovector := by
    rw [FrameComposition.covector_composeFrames, hnormal]
  let z := covector f.components v
  have hpair : pairing z NullScreen.nullCovector = 0 := by
    change pairing (covector f.components v) NullScreen.nullCovector = _
    rw [← he', transformed_dot_mulVec B f v e, hv]
  have h01 : z 0 + z 1 = 0 := by simpa only [pairing_nullCovector] using hpair
  have hquad : symbolNorm B v = (z 2)^2 + (z 3)^2 := by
    rw [← LorentzPhysical.transformed_symbolNorm B f v]
    change symbolNorm NullScreen.minkowskiInverse z = _
    rw [MinkowskiNull.symbolNorm_eq_coordinates]
    have hz : z 1 = - z 0 := by linarith
    rw [hz]
    ring
  refine ⟨by rw [hquad]; positivity, ?_⟩
  constructor
  · intro hz
    have hz2sq : (z 2)^2 = 0 := by nlinarith [sq_nonneg (z 2), sq_nonneg (z 3)]
    have hz3sq : (z 3)^2 = 0 := by nlinarith [sq_nonneg (z 2), sq_nonneg (z 3)]
    have hz2 : z 2 = 0 := pow_eq_zero hz2sq
    have hz3 : z 3 = 0 := pow_eq_zero hz3sq
    refine ⟨z 1, f.isBasis.1 ?_⟩
    rw [covector_smul_frame, he']
    change z = z 1 • NullScreen.nullCovector
    funext i
    fin_cases i <;> simp [NullScreen.nullCovector, Fin.isValue, Pi.smul_apply, hz2, hz3]
    linarith
  · rintro ⟨c, rfl⟩
    rw [symbolNorm_eq_dot_mulVec, mulVec_smul, smul_dotProduct, dotProduct_smul,
      ← symbolNorm_eq_dot_mulVec, hn]
    simp

/-- Removing the Euclidean null direction leaves a positive form on the
two-dimensional screen. -/
theorem screen_quadratic_pos (B : ScreenMatrix) (frame : LorentzFrame B)
    (e v : Covector) (he : e ≠ 0) (hn : symbolNorm B e = 0)
    (hB : v ⬝ᵥ (B *ᵥ e) = 0) (hE : v ⬝ᵥ e = 0) (hv : v ≠ 0) :
    0 < v ⬝ᵥ (B *ᵥ v) := by
  rcases null_orthogonal_quadratic B frame e v he hn hB with ⟨hnonneg, hzero⟩
  rw [← symbolNorm_eq_dot_mulVec]
  refine lt_of_le_of_ne hnonneg ?_
  intro h
  rcases hzero.mp h.symm with ⟨c, rfl⟩
  rw [smul_dotProduct] at hE
  have hc : c = 0 := (mul_eq_zero.mp hE).resolve_right (fun ez => he (dotProduct_self_eq_zero.mp ez))
  exact hv (hc ▸ zero_smul ℝ e)

end Burnett.V06
