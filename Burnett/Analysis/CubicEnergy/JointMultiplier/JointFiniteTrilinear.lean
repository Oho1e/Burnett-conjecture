import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWeightedSummation

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Finset
open scoped ENNReal ContDiff

private theorem two_offset_weights (C : ℝ≥0∞) (hc : C<⊤) (u v : ℕ → ℝ) (j k : ℕ) :
    (∑ i ∈ range 7,∑ l ∈ range 7,C*ratioCost (u i) j*ratioCost (v l) k) < ⊤ :=
  ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.sum_lt_top.mpr (fun _ _ =>
    ENNReal.mul_lt_top (ENNReal.mul_lt_top hc ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top))

/-- A bound on the actual sum over any finite consecutive dyadic scales.
Its three symbol costs are the weighted masses of one reference kernel. -/
theorem joint_finite_trilinear (p s z : ℝ) (hp : 1<p) (hs : 1<s) (hz : 1<z)
    (hb : triBalance p s z) :
    ∃ B₁ B₂ B₃ : ℝ≥0∞, B₁<⊤ ∧ B₂<⊤ ∧ B₃<⊤ ∧
      ∀ (m : Joint → ℝ), ContDiffOn ℝ ∞ m {y | y ≠ 0} →
      ∀ (t : ℝ), 0<t → ∀ (n : ℕ) (f g h : SchwartzMap E ℂ),
      ‖∑ i : Fin n, testedBlock (symbolBlock m) (dyadicScale t i) f g h‖ₑ ≤
        (B₁*kernelMoment (symbolBlock m) 1 1+B₂*kernelMoment (symbolBlock m) 5 1+
          B₃*kernelMoment (symbolBlock m) 1 5)*triLpMass f g h p s z := by
  obtain ⟨a,d,ha,cut,slot⟩ := testedBlock_slot_expansion
  obtain ⟨C₁,C₂,C₃,h₁,h₂,h₃,placements⟩ := dyadic_three_placements a d ha cut p s z hp hs hz hb
  let F := range 7
  let c₁ := fun i j : ℕ => C₁*ratioCost (highOffset i) 1*ratioCost (highOffset j) 1
  let c₂ := fun i _ : ℕ => C₂*ratioCost 32 5*ratioCost (highOffset i) 1
  let c₃ := fun i _ : ℕ => C₃*ratioCost (highOffset i) 1*ratioCost 32 5
  refine ⟨∑ i ∈ F,∑ j ∈ F,c₁ i j,∑ i ∈ F,∑ j ∈ F,c₂ i j,∑ i ∈ F,∑ j ∈ F,c₃ i j,
    two_offset_weights _ h₁ _ _ _ _,?_,two_offset_weights _ h₃ _ _ _ _,?_⟩
  · exact ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.sum_lt_top.mpr (fun j _ =>
      ENNReal.mul_lt_top (ENNReal.mul_lt_top h₂ ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top))
  intro m hm t ht n f g h
  let A := symbolBlock m
  obtain ⟨compact,smooth⟩ := symbolBlock_regular m hm
  let X := fun (k : Fin n) i j => windowBlock A (dyadicScale t k) f g h a a d (highOffset i) (highOffset j) (1/4)
  let Y := fun (k : Fin n) i j => windowBlock A (dyadicScale t k) f g h d a a 32 (highOffset i) (highOffset j)
  let Z := fun (k : Fin n) i j => windowBlock A (dyadicScale t k) f g h a d a (highOffset i) 32 (highOffset j)
  let G := triLpMass f g h p s z
  let K₁ := kernelMoment A 1 1
  let K₂ := kernelMoment A 5 1
  let K₃ := kernelMoment A 1 5
  have hi (i : ℕ) : 0<highOffset i := by unfold highOffset; positivity
  have sx (i j : ℕ) : ‖∑ k, X k i j‖ₑ ≤ c₁ i j*K₁*G :=
    tested_window_sum_bound A compact smooth f g h a a d (highOffset i) (highOffset j) (1/4) t n
      1 1 C₁ G (fun y => (placements _ _ _ t (hi i) (hi j) (by norm_num) ht n f g h y).1)
  have sy (i j : ℕ) : ‖∑ k, Y k i j‖ₑ ≤ c₂ i j*K₂*G :=
    tested_window_sum_bound A compact smooth f g h d a a 32 (highOffset i) (highOffset j) t n
      5 1 C₂ G (fun y => (placements _ _ _ t (by norm_num) (hi i) (hi j) ht n f g h y).2.1)
  have sz (i j : ℕ) : ‖∑ k, Z k i j‖ₑ ≤ c₃ i j*K₃*G :=
    tested_window_sum_bound A compact smooth f g h a d a (highOffset i) 32 (highOffset j) t n
      1 5 C₃ G (fun y => (placements _ _ _ t (hi i) (by norm_num) (hi j) ht n f g h y).2.2)
  have flip : (∑ k : Fin n, testedBlock A (dyadicScale t k) f g h) =
      ∑ i ∈ F,∑ j ∈ F,((∑ k,X k i j)+(∑ k,Y k i j)+(∑ k,Z k i j)) := by
    change (∑ k : Fin n, testedBlock (symbolBlock m) (dyadicScale t k) f g h) = _
    simp_rw [slot m hm]
    change (∑ k : Fin n,∑ i ∈ F,∑ j ∈ F, (X k i j+Y k i j+Z k i j)) = _
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    simp only [Finset.sum_add_distrib]
  rw [flip]
  calc
    _ ≤ ∑ i ∈ F,∑ j ∈ F,(c₁ i j*K₁*G+c₂ i j*K₂*G+c₃ i j*K₃*G) := by
      refine (enorm_sum_le _ _).trans (sum_le_sum fun i _ =>
        (enorm_sum_le _ _).trans (sum_le_sum fun j _ => ?_))
      exact (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans
        (add_le_add (sx i j) (sy i j))) (sz i j))
    _ = ((∑ i ∈ F,∑ j ∈ F,c₁ i j)*K₁+(∑ i ∈ F,∑ j ∈ F,c₂ i j)*K₂+
        (∑ i ∈ F,∑ j ∈ F,c₃ i j)*K₃)*G := by
      simp only [Finset.sum_add_distrib,Finset.sum_mul,add_mul]

end Burnett.A02.FrequencySplit
