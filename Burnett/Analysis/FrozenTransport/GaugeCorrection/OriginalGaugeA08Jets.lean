import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeA08Profile

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section
namespace Burnett.V08

open Set Metric Matrix Burnett.A06
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight)
open scoped ContDiff Matrix

/-- The full angular profile, including the non-radial three-leg low cutoff,
has all of the joint compact jet bounds required by the A08 operator theorem. -/
theorem exists_gaugeTriadAngularProfile_jet_bound (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (κ : ℝ) (hκ : 0 < κ) (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {x : E | x ≠ 0}) (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun x => S x i j) {x : E | x ≠ 0}) (k i j : TensorSlot) (N : ℕ) :
    let Q := (closedBall (0 : E) (1/4) ×ˢ sphere (0 : E) 1) ×ˢ sphere (0 : E) 1
    let F := gaugeTriadAngularProfile θ κ m w a C S k i j
    ∃ (W : Set (Joint × E)) (M : ℝ), IsOpen W ∧ Q ⊆ W ∧ ContDiffOn ℝ ∞ F W ∧ 0 ≤ M ∧
      ∀ n ≤ N, ∀ x ∈ Q, ‖iteratedFDeriv ℝ n F x‖ ≤ M := by
  classical
  intro Q F
  let U := {x : Joint × E | x.1.2 ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun (continuous_snd.comp continuous_fst) continuous_const
  have hhigh (x : Joint × E) (hx : x ∈ U) : 0 < ‖x.1.2‖ := norm_pos_iff.mpr hx
  let l (x : Joint × E) := x.1.1
  let h (x : Joint × E) := x.1.2
  have dl : ContDiff ℝ ∞ l := contDiff_fst.comp contDiff_fst
  have dh : ContDiff ℝ ∞ h := contDiff_snd.comp contDiff_fst
  have den (x : Joint × E) (hx : x ∈ U) : κ^2*(‖h x‖^2+‖l x+h x‖^2) ≠ 0 :=
    (mul_pos (pow_pos hκ _) (add_pos_of_pos_of_nonneg (pow_pos (hhigh x hx) 2) (sq_nonneg _))).ne'
  have mask : ContDiffOn ℝ ∞ (fun x : Joint × E =>
      (lowSlotWeight θ κ x.1.1 x.1.2 (-(x.1.1+x.1.2)) : ℂ)) U := by
    simp only [lowSlotWeight, norm_neg]
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hθ.comp_contDiffOn ((dl.norm_sq ℝ).contDiffOn.div
      (contDiff_const.mul ((dh.norm_sq ℝ).add ((dl.add dh).norm_sq ℝ))).contDiffOn den))
  obtain ⟨W,_,hW,hSub,hBase,_,_⟩ := exists_lowGaugeAngularExpansionProfile_jet_bound m w a ha
    (gaugeEntryBasis k) C S hS i j (1/4) (by norm_num) N
  let W' := W ∩ U
  have open' : IsOpen W' := hW.inter hU
  have sub : Q ⊆ W' := by
    intro x hx
    refine ⟨hSub hx, ?_⟩
    have v : ‖x.1.2‖=1 := mem_sphere_zero_iff_norm.mp hx.1.2
    exact norm_pos_iff.mp (v.symm ▸ zero_lt_one)
  have smooth : ContDiffOn ℝ ∞ F W' :=
    (mask.mono inter_subset_right).mul (hBase.mono inter_subset_left)
  have compact : IsCompact Q := ((isCompact_closedBall _ _).prod (isCompact_sphere _ _)).prod (isCompact_sphere _ _)
  have hBound (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Q, ‖iteratedFDeriv ℝ n F x‖ ≤ B := by
    have order : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have hc : ContinuousOn (iteratedFDeriv ℝ n F) W' :=
      (smooth.continuousOn_iteratedFDerivWithin order open'.uniqueDiffOn).congr
        (fun x hx => (iteratedFDerivWithin_of_isOpen n open' hx).symm)
    obtain ⟨B,hB⟩ := compact.bddAbove_image (hc.norm.mono sub)
    exact ⟨max B 0, le_max_right _ _, fun x hx => (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩
  choose B hB bound using hBound
  refine ⟨W', ∑ n ∈ Finset.range (N+1), B n, open', sub, smooth, Finset.sum_nonneg (fun n _ => hB n), ?_⟩
  exact fun n hn x hx => (bound n x hx).trans (Finset.single_le_sum (fun t _ => hB t)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

end Burnett.V08
