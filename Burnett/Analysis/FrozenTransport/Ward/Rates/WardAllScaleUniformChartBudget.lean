import Burnett.Analysis.FrozenTransport.Ward.WardLowTransfer
import Burnett.Analysis.FrozenTransport.Ward.WardLowTransferCoordinates

set_option autoImplicit false
set_option maxRecDepth 6900
set_option maxHeartbeats 14500000

noncomputable section

namespace Burnett.C02

open Set Metric Burnett.A02.FrequencySplit
open scoped ContDiff

open private wardRatioChartNeighborhood wardRatioChartNeighborhood_open wardRatioChartLift_smooth wardRatioChartCompact wardRatioChartCompact_compact wardRatioChartCompact_subset wardRatioChartDomain_subset from Burnett.Analysis.FrozenTransport.Ward.WardLowTransferCoordinates

private theorem wardContinuousOn_frequencyJet {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F : X × Y → ℂ} {O : Set (X × Y)} (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O) (n : ℕ) :
    ContinuousOn (fun p : X × Y => iteratedFDeriv ℝ n (fun y => F (p.1,y)) p.2) O := by
  let L := ContinuousLinearMap.inr ℝ X Y
  let R := ContinuousMultilinearMap.compContinuousLinearMapL (G := ℂ) (fun _ : Fin n => L)
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hfull : ContinuousOn (iteratedFDeriv ℝ n F) O :=
    (hF.continuousOn_iteratedFDerivWithin hn hO.uniqueDiffOn).congr
      (fun x hx => (iteratedFDerivWithin_of_isOpen n hO hx).symm)
  apply (R.continuous.comp_continuousOn hfull).congr
  intro p hp
  let off : X × Y := (p.1,0)
  let V := (fun z : X × Y => z + off) ⁻¹' O
  let G (z : X × Y) := F (z + off)
  have hTranslate : ContDiff ℝ ∞ (fun z : X × Y => z + off) := contDiff_id.add contDiff_const
  have hV : IsOpen V := hO.preimage hTranslate.continuous
  have hG : ContDiffOn ℝ ∞ G V := hF.comp hTranslate.contDiffOn (fun _ hz => hz)
  have hShift : L p.2 + off = p := by ext <;> simp [L,off]
  have hx : L p.2 ∈ V := by change L p.2 + off ∈ O; rwa [hShift]
  have hSlice : (fun y => F (p.1,y)) = G ∘ L := by funext y; simp [G,L,off]
  change iteratedFDeriv ℝ n (fun y => F (p.1,y)) p.2 = R (iteratedFDeriv ℝ n F p)
  rw [hSlice]
  have v := L.iteratedFDerivWithin_comp_right hG hV.uniqueDiffOn
    (hV.preimage L.continuous).uniqueDiffOn hx hn
  rw [iteratedFDerivWithin_of_isOpen n (hV.preimage L.continuous) hx,
    iteratedFDerivWithin_of_isOpen n hV hx] at v
  change _ = (iteratedFDeriv ℝ n (fun z : X × Y => F (z + off)) (L p.2)).compContinuousLinearMap (fun _ => L) at v
  rw [iteratedFDeriv_comp_add_right, hShift] at v
  exact v

/-- The compact frequency jets used by the original first-low transfer
have one common bound for the whole frozen-center family. -/
theorem exists_wardRatioChartFamilyBudget {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K V : Set X) (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (F : X × WardLowPoint → ℂ) (U : Set WardLowPoint)
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ U))
    (hU : ∀ x : WardLowPoint, ‖x.1‖ = 1 → ‖x.2.1‖ = 1 → |x.2.2| < 1 / 3 → x ∈ U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ c ∈ K,
      (∀ i, ContDiffOn ℝ 100 (fun x => F (c,wardRatioChartLift i x)) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) (1 / 4))) ∧
      ∀ i n, n ≤ 100 → ∀ x ∈ wardPairChartDomain i ×ˢ Ico (0 : ℝ) (1 / 4),
        ‖iteratedFDerivWithin ℝ n (fun y => F (c,wardRatioChartLift i y))
          (wardPairChartDomain i ×ˢ Ico (0 : ℝ) (1 / 4)) x‖ ≤ D := by
  classical
  let N : Set (X × WardRatioDomain) := V ×ˢ wardRatioChartNeighborhood
  have hN : IsOpen N := hV.prod wardRatioChartNeighborhood_open
  let P (i : WardPairChart) (z : X × WardRatioDomain) := F (z.1, wardRatioChartLift i z.2)
  have hP (i : WardPairChart) : ContDiffOn ℝ ∞ (P i) N := by
    apply hF.comp (contDiff_fst.contDiffOn.prodMk ((wardRatioChartLift_smooth i).comp contDiff_snd.contDiffOn (fun _ hz => hz.2)))
    intro z hz
    have hRatio : |z.2.2| < 1 / 3 := abs_lt.mpr
      ⟨by simpa only [neg_div] using hz.2.2.1, hz.2.2.2⟩
    exact ⟨hz.1, hU _
      (wardSphereChartLift_norm_eq_one i.1 z.2.1.1 (mem_ball_zero_iff.mp hz.2.1.1))
      (wardSphereChartLift_norm_eq_one i.2 z.2.1.2 (mem_ball_zero_iff.mp hz.2.1.2)) hRatio⟩
  have hSub : K ×ˢ wardRatioChartCompact ⊆ N := fun _ h => ⟨hKV h.1, wardRatioChartCompact_subset h.2⟩
  have hJetBound (i : WardPairChart) (n : ℕ) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ c ∈ K, ∀ y ∈ wardRatioChartCompact,
        ‖iteratedFDeriv ℝ n (fun x => P i (c,x)) y‖ ≤ B := by
    have hContinuous := (wardContinuousOn_frequencyJet hN (hP i) n).norm.mono hSub
    obtain ⟨B,hB⟩ := (hK.prod wardRatioChartCompact_compact).bddAbove_image hContinuous
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro c hc y hy
    exact (hB (mem_image_of_mem _ (show (c,y) ∈ K ×ˢ wardRatioChartCompact from ⟨hc,hy⟩))).trans (le_max_left _ _)
  choose B hB hJet using hJetBound
  let D := ∑ i : WardPairChart, ∑ n ∈ Finset.range 101, B i n
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun n _ => hB i n
  refine ⟨D,hD,?_⟩
  intro c hc
  have hSlice (i : WardPairChart) :
      ContDiffOn ℝ ∞ (fun x => F (c,wardRatioChartLift i x)) wardRatioChartNeighborhood :=
    (hP i).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => ⟨hKV hc,hx⟩)
  constructor
  · intro i
    exact ((hSlice i).of_le (WithTop.coe_le_coe.mpr le_top)).mono
      ((wardRatioChartDomain_subset i).trans wardRatioChartCompact_subset)
  · intro i n hn x hx
    have hxK := wardRatioChartDomain_subset i hx
    have hDiff : ContDiffAt ℝ n (fun y => F (c,wardRatioChartLift i y)) x :=
      ((hSlice i).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
        (wardRatioChartNeighborhood_open.mem_nhds (wardRatioChartCompact_subset hxK))
    have hu := (wardPairChartDomain_open i).uniqueDiffOn.prod (uniqueDiffOn_Ico (0 : ℝ) (1 / 4))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hu hDiff hx]
    exact (hJet i n c hc x hxK).trans
      ((Finset.single_le_sum (fun n _ => hB i n) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))).trans
        (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun n _ => hB k n) (Finset.mem_univ i)))

end Burnett.C02
