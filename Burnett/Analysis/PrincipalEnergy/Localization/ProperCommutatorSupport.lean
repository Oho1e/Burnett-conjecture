import Burnett.Analysis.PrincipalEnergy.Localization.ActualKernelSupport
import Burnett.Analysis.PrincipalEnergy.Localization.ActualPartitionPairs
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Burnett.Analysis.FirstOrderDyadic
open scoped NNReal

/-- A compact input for the actual properly supported scalar commutator has
an actual continuous, compactly supported L² output. The compact set is
the same for every multiplying coefficient with the stated bounds. -/
theorem exists_actualScalarCommutator_output_support_of_properSupport
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a)
    (hc : Continuous (Function.uncurry a)) (hProper : ProperKernelRelation (firstOrderKernelRelation a))
    (f : SchwartzMap Space ℂ) (hf : HasCompactSupport (f : Space → ℂ)) :
    ∃ K : Set Space, IsCompact K ∧
      ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
        LipschitzWith L r → (∀ x, ‖r x‖ ≤ U) →
        tsupport (actualCoefficientCommutator a r f) ⊆ K ∧
        MemLp (actualCoefficientCommutator a r f) 2 volume := by
  let Q := firstOrderKernelRelation a ∩ (Set.univ ×ˢ tsupport (f : Space → ℂ))
  let K := Prod.fst '' Q
  have hK : IsCompact K := ((hProper.2 _ hf).2).image continuous_fst
  refine ⟨K, hK, ?_⟩
  intro r L U hLip hU
  let rf := scalarSchwartzProduct r f
  have hrf (y : Space) : rf y = r y * f y := scalarSchwartzProduct_apply r f y
  have hZero (x : Space) (hx : x ∉ K) : actualCoefficientCommutator a r f x = 0 := by
    have hxF : x ∉ tsupport (f : Space → ℂ) := fun hxF =>
      hx ⟨(x,x), ⟨Or.inl rfl, mem_univ _, hxF⟩, rfl⟩
    have hOpposite : (fun y => lowCoefficientKernel a r x y * f y) =
        (fun y => -(coefficientKernel r (firstOrderKernel a) x y * f y)) := by
      funext y
      by_cases hy : f y = 0
      · simp [hy]
      have hRelation : (x,y) ∉ firstOrderKernelRelation a := fun h =>
        hx ⟨(x,y), ⟨h, mem_univ _, subset_closure hy⟩, rfl⟩
      have hne : x ≠ y := fun h => hRelation (Or.inl h)
      have hKernel : offDiagonalFirstOrderKernel a x y = 0 := by
        by_contra h
        exact hRelation (Or.inr (subset_closure ⟨hne, h⟩))
      rw [eq_neg_iff_add_eq_zero, ← add_mul]
      change ((r x - r y) * firstOrderLowKernel a x (x-y) +
        (r x - r y) * firstOrderKernel a x (x-y)) * f y = 0
      rw [← mul_add]
      change ((r x - r y) * offDiagonalFirstOrderKernel a x y) * f y = 0
      rw [hKernel, mul_zero, zero_mul]
    have hSplit : actualCoefficientCommutator a r f x = lowCoefficientCommutator a r f x +
        (r x * firstOrderHighAction a f x - firstOrderHighAction a rf x) :=
      full_coefficient_commutator_split ha.frequency r f rf hrf x
    rw [hSplit,
      lowCoefficientCommutator_eq_kernel ha.frequency hc r r.continuous U hU f x,
      firstOrderHighCoefficientCommutator_offSupport a ha.frequency r f rf hrf L hLip hf x hxF,
      hOpposite, integral_neg, neg_add_cancel]
  have hsupp : tsupport (actualCoefficientCommutator a r f) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx (hZero x hxK)
  have hContinuous : Continuous (actualCoefficientCommutator a r f) :=
    (r.continuous.mul (firstOrderAction_continuous_and_bounded ha.frequency hc f).1).sub
      (firstOrderAction_continuous_and_bounded ha.frequency hc rf).1
  exact ⟨hsupp, hContinuous.memLp_of_hasCompactSupport (hK.of_isClosed_subset isClosed_closure hsupp)⟩

end Burnett.Analysis.CarlesonEmbedding
