import Burnett.Analysis.PrincipalEnergy.Localization.ProperActionLocalization
import Burnett.Analysis.PrincipalEnergy.Quantization.SourceDerivative
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Proper support of the same left action, read from a physical cutoff sandwich. -/

set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable section

namespace Burnett.V03

open Set Filter Function MeasureTheory
open Burnett.Analysis.CarlesonEmbedding Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff

/-- On an open source region disjoint from the output point, a vanishing
actual action on smooth compact tests forces the concrete kernel to vanish. -/
theorem offDiagonalFirstOrderKernel_zero_of_vanishing_action
    {a : Space → Space → ℂ} (ha : FrequencyOrderOne a) (hc : Continuous (uncurry a))
    (x : Space) {U : Set Space} (hU : IsOpen U) (hx : x ∉ U)
    (hZero : ∀ f : SchwartzMap Space ℂ, HasCompactSupport (f : Space → ℂ) →
      tsupport (f : Space → ℂ) ⊆ U → firstOrderAction a f x = 0) :
    EqOn (offDiagonalFirstOrderKernel a x) 0 U := by
  obtain ⟨C, hC, hd⟩ := exists_firstOrderKernel_relativeDerivative_bound ha
  have hl : Continuous (fun y => firstOrderLowKernel a x (x-y)) := by
    let q : Space → Space × Space := fun y => (x, x-y)
    have hq : Continuous q := continuous_const.prodMk (continuous_const.sub continuous_id)
    change Continuous (uncurry (firstOrderLowKernel a) ∘ q)
    exact (firstOrderLowKernel_joint_continuous ha hc).comp hq
  have hh : ContinuousOn (fun y => firstOrderKernel a x (x-y)) U := by
    intro y hy
    have hxy : x - y ≠ 0 := sub_ne_zero.mpr fun he => hx (he.symm ▸ hy)
    have hk : ContinuousAt (firstOrderKernel a x) (x-y) := (hd x (x-y) hxy).1.continuousAt
    have ht : ContinuousAt (fun z : Space => x - z) y := continuousAt_const.sub continuousAt_id
    change ContinuousWithinAt (firstOrderKernel a x ∘ (fun z : Space => x-z)) U y
    exact (hk.comp ht).continuousWithinAt
  have hK : ContinuousOn (offDiagonalFirstOrderKernel a x) U := hl.continuousOn.add hh
  have hae : ∀ᵐ y ∂(volume : Measure Space), y ∈ U → offDiagonalFirstOrderKernel a x y = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hK.locallyIntegrableOn hU.measurableSet) ?_
    intro g hgs hgc hgU
    have hgC : HasCompactSupport (fun y => (g y : ℂ)) := hgc.comp_left Complex.ofReal_zero
    let f := hgC.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hgs)
    have hf : HasCompactSupport (f : Space → ℂ) := hgC
    have hfS : Function.support (f : Space → ℂ) ⊆ Function.support g := by
      intro y hy hz
      apply hy
      change ((g y : ℝ) : ℂ) = 0
      exact_mod_cast hz
    have hfU : tsupport (f : Space → ℂ) ⊆ U := (closure_mono hfS).trans hgU
    have hfOff : x ∉ tsupport (f : Space → ℂ) := fun hm => hx (hfU hm)
    obtain ⟨hHighI, hHigh⟩ := firstOrderHighAction_offSupport ha f x hfOff
    have hLowI : Integrable (fun y => firstOrderLowKernel a x (x-y) * f y) :=
      (hl.mul f.continuous).integrable_of_hasCompactSupport hf.mul_left
    have H := hZero f hf hfU
    rw [firstOrderAction_eq_low_add_high ha, firstOrderLowAction_eq_kernel ha _ f.integrable, hHigh] at H
    calc
      _ = ∫ y, firstOrderLowKernel a x (x-y) * f y + firstOrderKernel a x (x-y) * f y := by
        apply integral_congr_ae
        filter_upwards with y
        rw [Complex.real_smul]
        change ((g y : ℝ) : ℂ) * (firstOrderLowKernel a x (x-y) + firstOrderKernel a x (x-y)) =
           firstOrderLowKernel a x (x-y) * (g y : ℂ) + firstOrderKernel a x (x-y) * (g y : ℂ)
        ring
      _ = 0 := (integral_add hLowI hHighI).trans H
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).mpr hae)
    hU hK continuousOn_const

/-- A left action supported inside the fixed output compact set and killing
all tests away from the fixed input compact set has the actual proper kernel
relation demanded by the scalar commutator estimate. -/
theorem proper_firstOrderKernelRelation_of_compact_cutoff_action
    {a : Space → Space → ℂ} (ha : FrequencyOrderOne a) (hc : Continuous (uncurry a))
    {S T : Set Space} (hS : IsCompact S) (hT : IsCompact T)
    (hOut : ∀ f : SchwartzMap Space ℂ, HasCompactSupport (f : Space → ℂ) →
      ∀ x ∉ S, firstOrderAction a f x = 0)
    (hIn : ∀ f : SchwartzMap Space ℂ, HasCompactSupport (f : Space → ℂ) →
      tsupport (f : Space → ℂ) ⊆ Tᶜ → ∀ x, firstOrderAction a f x = 0) :
    ProperKernelRelation (firstOrderKernelRelation a) := by
  let R := closure {p : Space × Space | p.1 ≠ p.2 ∧ offDiagonalFirstOrderKernel a p.1 p.2 ≠ 0}
  have hR : R ⊆ S ×ˢ T := by
    refine closure_minimal ?_ (hS.isClosed.prod hT.isClosed)
    intro p hp
    refine ⟨?_, ?_⟩
    · by_contra hx
      have hz := offDiagonalFirstOrderKernel_zero_of_vanishing_action ha hc p.1
        isClosed_singleton.isOpen_compl (by simp : p.1 ∉ ({p.1}ᶜ : Set Space))
        (fun f hf _ => hOut f hf p.1 hx)
      exact hp.2 (hz (show p.2 ∈ ({p.1}ᶜ : Set Space) from hp.1.symm))
    · by_contra hy
      let U : Set Space := Tᶜ ∩ {p.1}ᶜ
      have hU : IsOpen U := hT.isClosed.isOpen_compl.inter isClosed_singleton.isOpen_compl
      have hxU : p.1 ∉ U := fun hx => hx.2 rfl
      have hz := offDiagonalFirstOrderKernel_zero_of_vanishing_action ha hc p.1 hU hxU
        (fun f hf h => hIn f hf (h.trans inter_subset_left) p.1)
      exact hp.2 (hz (show p.2 ∈ U from ⟨hy, hp.1.symm⟩))
  have hClosed : IsClosed (firstOrderKernelRelation a) :=
    (isClosed_eq continuous_fst continuous_snd).union isClosed_closure
  refine ⟨hClosed, fun K hK => ⟨?_, ?_⟩⟩
  · refine ((hK.prod hK).union (hS.prod hT)).of_isClosed_subset
      (hClosed.inter (hK.isClosed.prod isClosed_univ)) ?_
    rintro ⟨x,y⟩ ⟨hxy,hKx⟩
    rcases hxy with he | hr
    · change x = y at he
      exact Or.inl ⟨hKx.1, he ▸ hKx.1⟩
    · exact Or.inr (hR hr)
  · refine ((hK.prod hK).union (hS.prod hT)).of_isClosed_subset
      (hClosed.inter (isClosed_univ.prod hK.isClosed)) ?_
    rintro ⟨x,y⟩ ⟨hxy,hKy⟩
    rcases hxy with he | hr
    · change x = y at he
      exact Or.inl ⟨he.symm ▸ hKy.2, hKy.2⟩
    · exact Or.inr (hR hr)

end Burnett.V03
