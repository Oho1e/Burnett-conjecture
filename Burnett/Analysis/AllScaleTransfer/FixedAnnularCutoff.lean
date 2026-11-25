import Burnett.Analysis.AllScaleTransfer.ActualGapBoxSeries
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric
open scoped ContDiff

abbrev FrequencyPair := Frequency × Frequency

/-- The two coordinate blocks of the actual Fourier box. -/
abbrev boxToPair : BoxSpace ≃L[ℝ] FrequencyPair := EuclideanSpace.sumEquivProd

theorem boxToPair_apply (z : BoxSpace) : boxToPair z = (firstInput z, secondInput z) := rfl

@[simp] theorem boxToPair_joined (ζ υ : Frequency) : boxToPair (joinedInputs ζ υ) = (ζ, υ) := by
  rw [boxToPair_apply, firstInput_joined, secondInput_joined]

/-- Fixed plateau cutoff for a compact block inside the open overlap of a
normalized annulus and the angular chart. -/
theorem exists_fixed_annular_cutoff {K V : Set FrequencyPair}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ β : FrequencyPair → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      tsupport β ⊆ V ∧ ∀ z ∈ K, β z = 1 := by
  obtain ⟨e, he, hV'⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨d, hd, hdK⟩ := hK.exists_isCompact_cthickening
  let u := min e d
  have hu : 0 < u := lt_min he hd
  obtain ⟨f, hf, sf, rf⟩ := (isOpen_thickening (δ := u) (E := K)).exists_smooth_support_eq
  obtain ⟨g, hg, sg, rg⟩ := hK.isClosed.isOpen_compl.exists_smooth_support_eq
  have negless (z : FrequencyPair) : 0 < f z + g z := by
    have hfn := (rf (mem_range_self z)).1
    have hgn := (rg (mem_range_self z)).1
    by_cases hz : z ∈ K
    · have hn : f z ≠ 0 := Function.mem_support.mp (hf ▸ self_subset_thickening hu K hz)
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hfn (Ne.symm hn)) hgn
    · have hn : g z ≠ 0 := Function.mem_support.mp (hg ▸ hz)
      exact add_pos_of_nonneg_of_pos hfn (lt_of_le_of_ne hgn (Ne.symm hn))
  let β := fun z : FrequencyPair => f z / (f z + g z)
  have hβ : ContDiff ℝ ∞ β := sf.div (sf.add sg) (fun z => (negless z).ne')
  have hs : tsupport β ⊆ cthickening u K := by
    apply (closure_mono ?_).trans (closure_thickening_subset_cthickening u K)
    intro z hz
    rw [← hf]
    exact Function.mem_support.mpr (fun h => Function.mem_support.mp hz (by simp [β, h]))
  refine ⟨β, hβ, hdK.of_isClosed_subset isClosed_closure
    (hs.trans (cthickening_mono (min_le_right e d) K)),
    hs.trans ((cthickening_mono (min_le_left e d) K).trans hV'), ?_⟩
  intro z hz
  have hg0 : g z = 0 := Function.notMem_support.mp (hg ▸ not_not.mpr hz)
  have hf0 : f z ≠ 0 := Function.mem_support.mp (hf ▸ self_subset_thickening hu K hz)
  simp [β, hg0, hf0]

/-- All fixed-chart jets through a prescribed finite order on a compact
portion of an open set have one common operator-norm bound. -/
theorem exists_compact_contDiffOn_jet_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {K V : Set E}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) (hSmooth : ContDiffOn ℝ ∞ f V)
    (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ N, ∀ z ∈ K, ‖iteratedFDeriv ℝ n f z‖ ≤ C := by
  have bounded (n : Fin (N + 1)) :
      ∃ B : ℝ, ∀ z ∈ K, ‖iteratedFDeriv ℝ n.val f z‖ ≤ B := by
    have hn : (n.val : WithTop ℕ∞) ≤ ∞ := by
      exact_mod_cast (show (n.val : ℕ∞) ≤ ⊤ from le_top)
    have hc := hSmooth.continuousOn_iteratedFDerivWithin hn hV.uniqueDiffOn
    obtain ⟨B, hB⟩ := hK.bddAbove_image (hc.mono hKV).norm
    refine ⟨B, fun z hz => ?_⟩
    rw [← iteratedFDerivWithin_of_isOpen n.val hV (hKV hz)]
    exact hB (mem_image_of_mem _ hz)
  choose B hB using bounded
  refine ⟨∑ n : Fin (N + 1), max (B n) 0, Finset.sum_nonneg fun n _ => le_max_right _ _, ?_⟩
  intro n hn z hz
  let i : Fin (N + 1) := ⟨n, Nat.lt_succ_iff.mpr hn⟩
  exact (hB i z hz).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => le_max_right (B j) 0) (Finset.mem_univ i)))

end Burnett.A05.BoxFourier
