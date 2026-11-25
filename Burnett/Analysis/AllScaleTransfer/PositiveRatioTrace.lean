import Burnett.Analysis.AllScaleTransfer.PositiveRatioRemainderBudget

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.Analysis.LowRatio

open Set
open scoped ContDiff

/-- Retain exactly the zero-ratio trace of the one-sided symbol. -/
def zeroRatioTraceExtension (M : Point → ℂ) (z : Point) : ℂ := M (z.1,0)

@[simp] theorem zeroRatioTraceExtension_zero (M : Point → ℂ) (a : Angles) :
    zeroRatioTraceExtension M (a,0) = M (a,0) := rfl

/-- Restrict the actual one-sided symbol to the zero-ratio face and
extend this trace constantly in the ratio slot. The same C100 budget
then applies on a two-sided open ratio window for the endpoint estimate. -/
theorem zeroRatioTraceExtension_jets_of_oneSidedC100
    {U : Set Angles} (hU : IsOpen U) {b : ℝ} (hb : 0 < b) (a b' : ℝ)
    (M : Point → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hM : ContDiffOn ℝ 100 M (U ×ˢ Ico (0 : ℝ) b))
    (hJet : ∀ n ≤ 100, ∀ z ∈ U ×ˢ Ico (0 : ℝ) b,
      ‖iteratedFDerivWithin ℝ n M (U ×ˢ Ico (0 : ℝ) b) z‖ ≤ B) :
    ContDiffOn ℝ 100 (zeroRatioTraceExtension M) (Window U a b') ∧
    ∀ n ≤ 100, ∀ z ∈ Window U a b', ‖iteratedFDeriv ℝ n (zeroRatioTraceExtension M) z‖ ≤ B := by
  let P : Point →L[ℝ] Point := (ContinuousLinearMap.fst ℝ Angles ℝ).prod 0
  let S := U ×ˢ Ico (0 : ℝ) b
  let O := P ⁻¹' S
  have hP (z : Point) : P z = (z.1,0) := rfl
  have hNorm : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    rw [hP]
    calc
      ‖(z.1,(0 : ℝ))‖ = ‖z.1‖ := by rw [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)]
      _ ≤ 1 * ‖z‖ := by rw [one_mul,Prod.norm_def]; exact le_max_left _ _
  have eqO : O = U ×ˢ (univ : Set ℝ) := by
    ext z
    change P z ∈ U ×ˢ Ico (0 : ℝ) b ↔ z ∈ U ×ˢ (univ : Set ℝ)
    rw [hP]
    simp only [mem_prod,mem_Ico,le_refl,hb,and_true,mem_univ]
  have hO : IsOpen O := by rw [eqO]; exact hU.prod isOpen_univ
  have hDiff : UniqueDiffOn ℝ S := hU.uniqueDiffOn.prod (uniqueDiffOn_Ico 0 b)
  have hMaps : MapsTo P (Window U a b') S := by
    intro z hz
    rw [hP]
    exact ⟨hz.1,le_rfl,hb⟩
  have hEq : zeroRatioTraceExtension M = M ∘ P := by
    funext z
    change M (z.1,0) = M (P z)
    exact congrArg M (hP z).symm
  have hComp : ContDiffOn ℝ 100 (zeroRatioTraceExtension M) (Window U a b') := by
    rw [hEq]
    exact hM.comp P.contDiff.contDiffOn hMaps
  refine ⟨hComp,?_⟩
  intro n hn z hz
  have hSO : P z ∈ S := hMaps hz
  have hzO : z ∈ O := hSO
  have hn' : (n : WithTop ℕ∞) ≤ 100 := by exact_mod_cast hn
  rw [hEq, ← iteratedFDerivWithin_of_isOpen n hO hzO,
    P.iteratedFDerivWithin_comp_right hM hDiff hO.uniqueDiffOn hSO hn']
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  calc
    _ ≤ B * (1 : ℝ)^n :=
      mul_le_mul (hJet n hn (P z) hSO) (pow_le_pow_left₀ (norm_nonneg _) hNorm n) (by positivity) hB
    _ = B := by simp

end Burnett.Analysis.LowRatio
