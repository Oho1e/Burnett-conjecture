import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleComparablePaddedFamily
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleUniformChartBudget
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer

set_option autoImplicit false
set_option maxRecDepth 6400
set_option maxHeartbeats 5200000

noncomputable section

namespace Burnett.C02

open Set Metric Burnett.A02.FrequencySplit Burnett.A05 Burnett.A05.BoxFourier
open scoped ContDiff

open private wardContinuousOn_frequencyJet from Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleUniformChartBudget
open private wardComparablePaddedSymbol from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer

def wardComparableBoxFamily {X : Type*} (ϑ : ℝ → ℝ) (κ : ℝ) (F : X × Joint → ℂ)
    (k : ℤ) (p : X × BoxSpace) : ℂ :=
  wardComparablePaddedSymbol ϑ κ (fun x => F (p.1,x))
    ((2 : ℝ)^k • (boxToPair p.2).1, (boxToPair p.2).2)

set_option maxHeartbeats 500000 in
theorem wardComparableBoxFamily_smooth {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : Set X) (hV : IsOpen V) (F : X × Joint → ℂ) (hF : ContDiffOn ℝ ∞ F (V ×ˢ wardTriadDomain))
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (κ : ℝ) (hκ : 0 < κ) (k : ℤ) :
    ContDiffOn ℝ ∞ (wardComparableBoxFamily ϑ κ F k) (V ×ˢ (univ : Set BoxSpace)) := by
  let lift (z : X × BoxSpace) : X × Joint :=
    (z.1, ((2 : ℝ)^k • (boxToPair z.2).1, (boxToPair z.2).2))
  let P (p : X × Joint) := wardComparablePaddedSymbol ϑ κ (fun y => F (p.1,y)) p.2
  change ContDiffOn ℝ ∞ (P ∘ lift) (V ×ˢ (univ : Set BoxSpace))
  have hLift : ContDiff ℝ ∞ lift :=
    contDiff_fst.prodMk (((contDiff_const.smul (contDiff_fst.comp boxToPair.contDiff)).prodMk
      (contDiff_snd.comp boxToPair.contDiff)).comp contDiff_snd)
  have hMap : MapsTo lift (V ×ˢ (univ : Set BoxSpace)) (V ×ˢ (univ : Set Joint)) :=
    fun _ hz => ⟨hz.1,mem_univ _⟩
  have hP : ContDiffOn ℝ ∞ P (V ×ˢ (univ : Set Joint)) :=
    wardComparablePaddedFamily_smooth V hV F hF ϑ hϑ κ hκ
  have hLiftOn : ContDiffOn ℝ ∞ lift (V ×ˢ (univ : Set BoxSpace)) := hLift.contDiffOn
  exact ContDiffOn.comp (f := lift) (g := P) hP hLiftOn hMap

/-- One derivative bound works on the actual compact boxes for every
frozen center and each of the finitely many relative dyadic shifts. -/
theorem exists_wardComparableBoxFamily_jetBound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K V : Set X) (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (F : X × Joint → ℂ) (hF : ContDiffOn ℝ ∞ F (V ×ˢ wardTriadDomain))
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (κ : ℝ) (hκ : 0 < κ) (I : Finset ℤ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c ∈ K, ∀ k ∈ I,
      ContDiff ℝ ∞ (fun x => wardComparableBoxFamily ϑ κ F k (c,x)) ∧
      ∀ n ≤ 40, ∀ x : BoxSpace, x ∈ ball (0 : BoxSpace) 5 →
      ‖iteratedFDeriv ℝ n (fun y => wardComparableBoxFamily ϑ κ F k (c,y)) x‖ ≤ B := by
  classical
  let O : Set (X × BoxSpace) := V ×ˢ univ
  have hO : IsOpen O := hV.prod isOpen_univ
  have hG (k : ℤ) : ContDiffOn ℝ ∞ (wardComparableBoxFamily ϑ κ F k) O :=
    wardComparableBoxFamily_smooth V hV F hF ϑ hϑ κ hκ k
  have hJet (k : ℤ) (n : ℕ) :
      ∃ D : ℝ, 0 ≤ D ∧ ∀ c ∈ K, ∀ x : BoxSpace, x ∈ closedBall (0 : BoxSpace) 5 →
        ‖iteratedFDeriv ℝ n (fun y => wardComparableBoxFamily ϑ κ F k (c,y)) x‖ ≤ D := by
    have hSub : K ×ˢ closedBall (0 : BoxSpace) 5 ⊆ O := fun _ h => ⟨hKV h.1, mem_univ _⟩
    have hc := (wardContinuousOn_frequencyJet hO (hG k) n).norm.mono hSub
    obtain ⟨D,hD⟩ := (hK.prod (isCompact_closedBall (0 : BoxSpace) 5)).bddAbove_image hc
    exact ⟨max D 0,le_max_right _ _,fun c hc x hx =>
      (hD (mem_image_of_mem _ (show (c,x) ∈ K ×ˢ closedBall (0 : BoxSpace) 5 from ⟨hc,hx⟩))).trans (le_max_left _ _)⟩
  choose D hD hBound using hJet
  let B := ∑ k ∈ I, ∑ n ∈ Finset.range 41, D k n
  have hB : 0 ≤ B := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun n _ => hD k n
  refine ⟨B,hB,?_⟩
  intro c hc k hk
  have hs : ContDiff ℝ ∞ (fun x => wardComparableBoxFamily ϑ κ F k (c,x)) := contDiffOn_univ.mp
    ((hG k).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => ⟨hKV hc,hx⟩))
  refine ⟨hs,?_⟩
  intro n hn x hx
  exact (hBound k n c hc x (ball_subset_closedBall hx)).trans
    ((Finset.single_le_sum (fun n _ => hD k n) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun n _ => hD k n) hk))

end Burnett.C02
