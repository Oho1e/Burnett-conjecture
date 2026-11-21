import Burnett.Analysis.PrincipalEnergy.Localization.GlobalCompactMatrixPair
import Burnett.Analysis.PrincipalEnergy.Localization.ActualKernelSupport
import Burnett.Analysis.PrincipalEnergy.Commutator.HighOffSupportAction

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Set Metric Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff ComplexConjugate

/-- The actual full left action of a properly supported symbol and the
original compact input are supported in a common compact set. -/
theorem exists_firstOrderAction_support_of_properSupport {a : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (hProper : ProperKernelRelation (firstOrderKernelRelation a))
    (f : SchwartzMap Space ℂ) (hf : HasCompactSupport (f : Space → ℂ)) :
    ∃ K : Set Space, IsCompact K ∧ tsupport (f : Space → ℂ) ⊆ K ∧
      tsupport (firstOrderAction a f) ⊆ K := by
  let Q := firstOrderKernelRelation a ∩ (univ ×ˢ tsupport (f : Space → ℂ))
  let K := Prod.fst '' Q
  have hK : IsCompact K := ((hProper.2 _ hf).2).image continuous_fst
  have hF : tsupport (f : Space → ℂ) ⊆ K := fun x hx =>
    ⟨(x,x), ⟨Or.inl rfl, mem_univ _, hx⟩, rfl⟩
  refine ⟨K, hK, hF, closure_minimal (fun x hx => ?_) hK.isClosed⟩
  by_contra hxK
  have hOff : x ∉ tsupport (f : Space → ℂ) := fun hp => hxK (hF hp)
  have hEq : (fun y => firstOrderLowKernel a x (x-y) * f y) =
      fun y => -(firstOrderKernel a x (x-y) * f y) := by
    funext y
    by_cases hy : f y = 0
    · simp only [hy, mul_zero, neg_zero]
    have hRel : (x,y) ∉ firstOrderKernelRelation a :=
      fun h => hxK ⟨(x,y), ⟨h, mem_univ _, subset_closure hy⟩, rfl⟩
    have hxy : x ≠ y := fun he => hRel (Or.inl he)
    have hZero : offDiagonalFirstOrderKernel a x y = 0 := by
      by_contra h
      exact hRel (Or.inr (subset_closure ⟨hxy, h⟩))
    rw [eq_neg_iff_add_eq_zero, ← add_mul]
    change offDiagonalFirstOrderKernel a x y * f y = 0
    rw [hZero, zero_mul]
  apply hx
  rw [firstOrderAction_eq_low_add_high ha, firstOrderLowAction_eq_kernel ha _ f.integrable,
    (firstOrderHighAction_offSupport ha f x hOff).2, hEq, integral_neg, neg_add_cancel]

/-- The fixed real lattice plateau supplies cutoffs equal to one on an
arbitrary compact set, with size and derivative bounds independent of the set. -/
theorem exists_uniform_schwartz_plateau_on_compact :
    ∃ S T : ℝ, 0 ≤ S ∧ 0 ≤ T ∧ ∀ K : Set Space, IsCompact K →
      ∃ χ : SchwartzMap Space ℂ, HasCompactSupport (χ : Space → ℂ) ∧
        (∀ x, conj (χ x) = χ x) ∧
        (∀ x, ‖χ x‖ ≤ S) ∧ (∀ x, ‖fderiv ℝ (χ : Space → ℂ) x‖ ≤ T) ∧
        ∀ x ∈ K, χ x = 1 := by
  obtain ⟨q, hq, hReal, hOne⟩ := exists_lattice_schwartz_plateau
  let S := SchwartzMap.seminorm ℝ 0 0 q
  let T := SchwartzMap.seminorm ℝ 0 1 q
  have hS : 0 ≤ S := (norm_nonneg _).trans (SchwartzMap.norm_le_seminorm ℝ q (0 : Space))
  have hT : 0 ≤ T :=
    (norm_nonneg _).trans (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ q 1 (0 : Space))
  refine ⟨S, T, hS, hT, fun K hK => ?_⟩
  obtain ⟨R, hR, hBall⟩ := hK.isBounded.subset_closedBall_lt 1 (0 : Space)
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hRi : 0 ≤ R⁻¹ := (inv_pos.mpr hRpos).le
  let L : Space →L[ℝ] Space := R⁻¹ • ContinuousLinearMap.id ℝ Space
  let f (x : Space) := q (L x)
  have hComp : HasCompactSupport f :=
    hq.comp_homeomorph (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hRpos.ne'))
  let χ := hComp.toSchwartzMap ((q.smooth ⊤).comp L.contDiff)
  have hL : ‖L‖ ≤ R⁻¹ := by
    dsimp only [L]
    rw [norm_smul, Real.norm_of_nonneg hRi]
    exact mul_le_of_le_one_right hRi ContinuousLinearMap.norm_id_le
  refine ⟨χ, hComp, fun x => hReal (L x), fun x => SchwartzMap.norm_le_seminorm ℝ q (L x), ?_, ?_⟩
  · intro x
    have hF : fderiv ℝ f x = (fderiv ℝ (q : Space → ℂ) (L x)).comp L :=
      (q.differentiableAt.hasFDerivAt.comp x L.hasFDerivAt).fderiv
    have hQ : ‖fderiv ℝ (q : Space → ℂ) (L x)‖ ≤ T := by
      calc
        _ = ‖iteratedFDeriv ℝ 0 (fderiv ℝ (q : Space → ℂ)) (L x)‖ := by rw [norm_iteratedFDeriv_zero]
        _ = ‖iteratedFDeriv ℝ 1 (q : Space → ℂ) (L x)‖ := norm_iteratedFDeriv_fderiv
        _ ≤ _ := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ q 1 (L x)
    change ‖fderiv ℝ f x‖ ≤ T
    rw [hF]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hL.trans (inv_le_one_of_one_le₀ hR.le)) |>.trans hQ)
  · intro x hx
    change q (L x) = 1
    apply hOne
    have hX : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hBall hx
    calc
      ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
      _ ≤ R⁻¹ * R := mul_le_mul hL hX (norm_nonneg _) hRi
      _ = 1 := inv_mul_cancel₀ hRpos.ne'
      _ ≤ 19 := by norm_num

end Burnett.Analysis.CarlesonEmbedding
