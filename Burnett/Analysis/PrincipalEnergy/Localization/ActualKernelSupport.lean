import Burnett.Analysis.PrincipalEnergy.Localization.FiniteFarPairing

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Burnett.Analysis.FirstOrderDyadic
open scoped NNReal ComplexConjugate

/-- The underlying left-quantized kernel away from the diagonal. -/
def offDiagonalFirstOrderKernel (a : Space → Space → ℂ) (x y : Space) : ℂ :=
  firstOrderLowKernel a x (x-y) + firstOrderKernel a x (x-y)

/-- The diagonal and the closed support of the actual off-diagonal kernel. -/
def firstOrderKernelRelation (a : Space → Space → ℂ) : Set (Space × Space) :=
  {p | p.1 = p.2} ∪ closure {p | p.1 ≠ p.2 ∧ offDiagonalFirstOrderKernel a p.1 p.2 ≠ 0}

/-- The two coordinate projections restricted to the closed relation
take compact data back to compact sets. -/
def ProperKernelRelation (R : Set (Space × Space)) : Prop :=
  IsClosed R ∧ ∀ K : Set Space, IsCompact K →
    IsCompact (R ∩ (K ×ˢ Set.univ)) ∧ IsCompact (R ∩ (Set.univ ×ˢ K))

theorem disjoint_compact_support_exists_dist {f g : Space → ℂ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hDisjoint : Disjoint (tsupport g) (tsupport f)) :
    ∃ d : ℝ, 0<d ∧ ∀ x y, f y ≠ 0 → g x ≠ 0 → d ≤ ‖x-y‖ := by
  let S : Set (Space × Space) := tsupport g ×ˢ tsupport f
  have hCompact : IsCompact S := hg.prod hf
  rcases S.eq_empty_or_nonempty with hEmpty | hNonempty
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x y hy hx
    have hp : (x,y) ∈ S := ⟨subset_closure hx, subset_closure hy⟩
    rw [hEmpty] at hp
    exact hp.elim
  · have hCont : ContinuousOn (fun p : Space × Space => ‖p.1-p.2‖) S :=
      ((continuous_fst.sub continuous_snd).norm).continuousOn
    obtain ⟨p, hp, hmin⟩ := hCompact.exists_isMinOn hNonempty hCont
    have hne : p.1 ≠ p.2 := by
      intro hEq
      exact (Set.disjoint_left.mp hDisjoint) hp.1 (hEq.symm ▸ hp.2)
    refine ⟨‖p.1-p.2‖, norm_pos_iff.mpr (sub_ne_zero.mpr hne), ?_⟩
    intro x y hy hx
    have hxy : (x,y) ∈ S := ⟨subset_closure hx, subset_closure hy⟩
    exact (isMinOn_iff.mp hmin) (x,y) hxy

/-- Compact input and test whose product of supports misses the genuine
kernel relation have exactly zero tested commutator. -/
theorem actualScalarCommutatorPair_eq_zero_of_offKernelRelation {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hc : Continuous (Function.uncurry a))
    (r f g : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ)
    (hLip : LipschitzWith L r) (hU : ∀ x, ‖r x‖ ≤ U)
    (hf : HasCompactSupport (f : Space → ℂ)) (hg : HasCompactSupport (g : Space → ℂ))
    (hOff : Disjoint (tsupport (g : Space → ℂ) ×ˢ tsupport (f : Space → ℂ))
      (firstOrderKernelRelation a)) : actualScalarCommutatorPair a r f g = 0 := by
  have hDisjoint : Disjoint (tsupport (g : Space → ℂ)) (tsupport (f : Space → ℂ)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (Set.disjoint_left.mp hOff) (show (x,x) ∈ _ from ⟨hx, hy⟩) (.inl rfl)
  obtain ⟨d, hd, hGap⟩ := disjoint_compact_support_exists_dist hf hg hDisjoint
  unfold actualScalarCommutatorPair
  rw [actualCoefficientCommutator_separated_pair_eq_kernel ha hc r f g L U hLip hU hf d hd hGap]
  calc
    _ = ∫ _ : Space × Space, (0 : ℂ) ∂((volume : Measure Space).prod volume) := by
      apply integral_congr_ae
      filter_upwards with p
      by_cases hx : g p.1 = 0
      · simp only [hx, map_zero, zero_mul]
      by_cases hy : f p.2 = 0
      · simp only [hy, mul_zero]
      have hxy : p.1 ≠ p.2 := fun h =>
        (Set.disjoint_left.mp hOff)
          (show p ∈ _ from ⟨subset_closure hx, subset_closure hy⟩) (.inl h)
      have hRaw : offDiagonalFirstOrderKernel a p.1 p.2 = 0 := by
        by_contra hn
        exact (Set.disjoint_left.mp hOff)
          (show p ∈ _ from ⟨subset_closure hx, subset_closure hy⟩)
          (.inr (subset_closure ⟨hxy, hn⟩))
      have hK : fullCoefficientKernel a r p.1 p.2 =
          (r p.1-r p.2) * offDiagonalFirstOrderKernel a p.1 p.2 := by
        simp only [fullCoefficientKernel, lowCoefficientKernel, coefficientKernel,
          offDiagonalFirstOrderKernel, mul_add]
      rw [hK, hRaw, mul_zero, zero_mul, mul_zero]
    _ = 0 := integral_zero _ _

/-- The proper support condition for the actual symbol yields a compact
test neighborhood for every compact input support. This neighborhood
depends on that input support and the genuine operator relation. -/
theorem exists_scalarCommutator_compact_test_region_of_properSupport
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a)
    (hc : Continuous (Function.uncurry a)) (hProper : ProperKernelRelation (firstOrderKernelRelation a))
    (f : SchwartzMap Space ℂ) (hf : HasCompactSupport (f : Space → ℂ)) :
    ∃ K : Set Space, IsCompact K ∧
      ∀ (r g : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
        LipschitzWith L r → (∀ x, ‖r x‖ ≤ U) → HasCompactSupport (g : Space → ℂ) →
        Disjoint (tsupport (g : Space → ℂ)) K → actualScalarCommutatorPair a r f g = 0 := by
  let Q := firstOrderKernelRelation a ∩ (Set.univ ×ˢ tsupport (f : Space → ℂ))
  have hQ : IsCompact Q := (hProper.2 _ hf).2
  let K : Set Space := Prod.fst '' Q
  refine ⟨K, hQ.image continuous_fst, ?_⟩
  intro r g L U hLip hU hg hDisjoint
  apply actualScalarCommutatorPair_eq_zero_of_offKernelRelation ha hc r f g L U hLip hU hf hg
  apply Set.disjoint_left.mpr
  intro p hp hpRel
  have hpK : p.1 ∈ K := ⟨p, ⟨hpRel, mem_univ _, hp.2⟩, rfl⟩
  exact (Set.disjoint_left.mp hDisjoint) hp.1 hpK

end Burnett.Analysis.CarlesonEmbedding
