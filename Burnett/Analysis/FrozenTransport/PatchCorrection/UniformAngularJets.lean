import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeA08Profile

set_option autoImplicit false
set_option maxHeartbeats 3800000
noncomputable section
namespace Burnett.V11

open Set Metric
open Burnett.A02.FrequencySplit (E Joint)
open scoped ContDiff BigOperators

def gaugeAngularWindow : Set (Joint × E) :=
  (closedBall (0:E) (1/4) ×ˢ sphere (0:E) 1) ×ˢ sphere (0:E) 1

def GaugeProfileBound (N : ℕ) (M : ℝ) (F : Joint × E → ℂ) : Prop :=
  ∃ W : Set (Joint × E), IsOpen W ∧ gaugeAngularWindow ⊆ W ∧ ContDiffOn ℝ ∞ F W ∧
    ∀ n ≤ N, ∀ y ∈ gaugeAngularWindow, ‖iteratedFDeriv ℝ n F y‖ ≤ M

private theorem continuousOn_secondPartialJet {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X × Y → ℂ} {O : Set (X × Y)} (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (n : ℕ) :
    ContinuousOn (fun p : X × Y => iteratedFDeriv ℝ n (fun y => f (p.1,y)) p.2) O := by
  let L := ContinuousLinearMap.inr ℝ X Y
  let R := ContinuousMultilinearMap.compContinuousLinearMapL (G:=ℂ) (fun _ : Fin n => L)
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hfull : ContinuousOn (iteratedFDeriv ℝ n f) O :=
    (hf.continuousOn_iteratedFDerivWithin hn hO.uniqueDiffOn).congr
      (fun x hx => (iteratedFDerivWithin_of_isOpen n hO hx).symm)
  apply (R.continuous.comp_continuousOn hfull).congr
  intro p hp
  let off : X × Y := (p.1,0)
  let V := (fun q : X × Y => q + off) ⁻¹' O
  let g (q : X × Y) := f (q+off)
  have trans : ContDiff ℝ ∞ (fun q : X × Y => q + off) := contDiff_id.add contDiff_const
  have vOpen : IsOpen V := hO.preimage trans.continuous
  have hg : ContDiffOn ℝ ∞ g V := hf.comp trans.contDiffOn (fun _ h => h)
  have shift : L p.2 + off = p := by ext <;> simp [L,off]
  have hx : L p.2 ∈ V := by change L p.2 + off ∈ O; rwa [shift]
  have hslice : (fun y => f (p.1,y)) = g ∘ L := by funext y; simp [g,L,off]
  change iteratedFDeriv ℝ n (fun y => f (p.1,y)) p.2 = R (iteratedFDeriv ℝ n f p)
  rw [hslice]
  have v := L.iteratedFDerivWithin_comp_right hg vOpen.uniqueDiffOn (vOpen.preimage L.continuous).uniqueDiffOn hx hn
  rw [iteratedFDerivWithin_of_isOpen n (vOpen.preimage L.continuous) hx,
    iteratedFDerivWithin_of_isOpen n vOpen hx] at v
  change _ = (iteratedFDeriv ℝ n (fun q : X × Y => f (q+off)) (L p.2)).compContinuousLinearMap (fun _ => L) at v
  rw [iteratedFDeriv_comp_add_right,shift] at v
  exact v

/-- An open-neighborhood smooth family on the exact product of the compact base
window and the A08 angular window admits one bound before the patch center. -/
theorem exists_uniform_frozen_angular_jets {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (hK : IsCompact K) (F : X × (Joint × E) → ℂ) (O : Set (X × (Joint × E)))
    (hO : IsOpen O) (hSub : K ×ˢ gaugeAngularWindow ⊆ O) (hF : ContDiffOn ℝ ∞ F O) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, GaugeProfileBound N M (fun y => F (x,y)) := by
  classical
  have hQ : IsCompact gaugeAngularWindow := ((isCompact_closedBall _ _).prod (isCompact_sphere _ _)).prod (isCompact_sphere _ _)
  have bound (n : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ K, ∀ y ∈ gaugeAngularWindow,
      ‖iteratedFDeriv ℝ n (fun p => F (x,p)) y‖ ≤ A := by
    have hc := (continuousOn_secondPartialJet hO hF n).norm.mono hSub
    obtain ⟨A,hA⟩ := (hK.prod hQ).bddAbove_image hc
    exact ⟨max A 0,le_max_right _ _,fun x hx y hy => (hA (mem_image_of_mem _ (show (x,y) ∈ K ×ˢ gaugeAngularWindow from ⟨hx,hy⟩))).trans (le_max_left _ _)⟩
  choose A hA aBound using bound
  refine ⟨∑ n ∈ Finset.range (N+1), A n, Finset.sum_nonneg (fun n _ => hA n), ?_⟩
  intro x hx
  let incl (y : Joint × E) := (x,y)
  have di : ContDiff ℝ ∞ incl := contDiff_const.prodMk contDiff_id
  refine ⟨incl ⁻¹' O,hO.preimage di.continuous,fun y hy => hSub ⟨hx,hy⟩,
    hF.comp di.contDiffOn (fun _ h => h),?_⟩
  exact fun n hn y hy => (aBound n x hx y hy).trans (Finset.single_le_sum (fun k _ => hA k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

end Burnett.V11
