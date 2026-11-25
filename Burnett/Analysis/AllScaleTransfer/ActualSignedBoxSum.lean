import Burnett.Analysis.AllScaleTransfer.PositiveActualCapBoxExtension

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.A05.BoxFourier

open Set
open Burnett.Analysis.CapFourier
open scoped ContDiff

/-- The four signed profiles use their own open chart cutoffs, so their
sum agrees with the unique active profile on each closed annular patch.
Derivatives of the sum retain the same geometric gap factor. -/
theorem signed_annular_box_profiles_sum {α : ℝ} (hα : 0 < α)
    (G : CapSigns → ℕ → BoxSpace → ℂ) (C : CapSigns → ℝ)
    (hsmooth : ∀ signs s, ContDiff ℝ 99 (G signs s))
    (hbound : ∀ signs s n, n ≤ 40 → ∀ z, ‖iteratedFDeriv ℝ n (G signs s) z‖ ≤ C signs * radialGapDecay s)
    (hzero : ∀ signs s z, boxToPair z ∉ signedPairV α signs → G signs s z = 0) :
    let SumProfile (s : ℕ) (z : BoxSpace) := ∑ signs : CapSigns, G signs s z
    (∀ s, ContDiff ℝ 99 (SumProfile s)) ∧
    (∀ s n, n ≤ 40 → ∀ z, ‖iteratedFDeriv ℝ n (SumProfile s) z‖ ≤
      (∑ signs : CapSigns, C signs) * radialGapDecay s) ∧
    (∀ signs s z, boxToPair z ∈ signedPairK α signs → SumProfile s z = G signs s z) := by
  intro SumProfile
  refine ⟨fun s => ContDiff.sum (fun signs _ => hsmooth signs s), ?_, ?_⟩
  · intro s n hn z
    have hn' : (n : WithTop ℕ∞) ≤ 99 := by exact_mod_cast (hn.trans (by decide : (40 : ℕ) ≤ 99))
    have H (signs : CapSigns) : ContDiff ℝ n (G signs s) := (hsmooth signs s).of_le hn'
    have hd := iteratedFDeriv_sum (u := (Finset.univ : Finset CapSigns)) (f := fun signs => G signs s)
      (i := n) (fun signs _ => H signs)
    change ‖iteratedFDeriv ℝ n (fun z => ∑ signs : CapSigns, G signs s z) z‖ ≤ _
    rw [hd, Finset.sum_apply]
    calc
      _ ≤ ∑ signs : CapSigns, C signs * radialGapDecay s :=
        norm_sum_le_of_le _ (fun signs _ => hbound signs s n hn z)
      _ = _ := (Finset.sum_mul ..).symm
  · intro signs s z hz
    unfold SumProfile
    refine Finset.sum_eq_single signs ?_ (by simp)
    intro other _ hne
    exact hzero other s z (signedPairK_notMem_other_signedPairV hα (Ne.symm hne) hz)

end Burnett.A05.BoxFourier
