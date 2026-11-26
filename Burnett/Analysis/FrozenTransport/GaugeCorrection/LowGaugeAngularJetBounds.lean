import Burnett.Analysis.FrozenTransport.GaugeCorrection.LowGaugeJointProfile

set_option autoImplicit false
set_option maxRecDepth 3900
set_option maxHeartbeats 5100000

noncomputable section

namespace Burnett.V08

open Set Metric Matrix Burnett.P01
open Burnett.A02.FrequencySplit (E)
open scoped ContDiff BigOperators Matrix

/-- The component profile in the order expected by the angular expansion,
with the independent low sphere in its last variable. -/
def lowGaugeAngularExpansionProfile (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ)
    (G : ComplexComponents) (C : Matrix TensorSlot TensorSlot ℝ) (S : E → Matrix TensorSlot TensorSlot ℝ)
    (i j : TensorSlot) (x : (E × E) × E) : ℂ :=
  lowGaugeJointProfile m w a G C S i j (x.2, x.1.1, x.1.2)

private theorem isOpen_cyclicLowProfileSet : IsOpen cyclicLowProfileSet := by
  have h₀ := isOpen_lt continuous_const (continuous_norm.comp
    (continuous_fst : Continuous fun p : E × E × E => p.1))
    (f := fun _ : E × E × E => (1/4 : ℝ))
  have h₁ := isOpen_lt (continuous_norm.comp (continuous_fst.comp
    (continuous_snd : Continuous fun p : E × E × E => p.2))) continuous_const
    (g := fun _ : E × E × E => (1/2 : ℝ))
  have h₂ := isOpen_lt continuous_const (continuous_norm.comp (continuous_snd.comp
    (continuous_snd : Continuous fun p : E × E × E => p.2)))
    (f := fun _ : E × E × E => (3/4 : ℝ))
  exact h₀.inter (h₁.inter h₂)

/-- Every finite set of actual mixed jets is bounded on the compact
Cartesian-ratio ball and both unit spheres. The corresponding open-domain
smoothness is the input used for the angular expansion. -/
theorem exists_lowGaugeAngularExpansionProfile_jet_bound
    (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (G : ComplexComponents) (C : Matrix TensorSlot TensorSlot ℝ) (S : E → Matrix TensorSlot TensorSlot ℝ)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun ξ => S ξ i j) {ξ : E | ξ ≠ 0})
    (i j : TensorSlot) (ρ : ℝ) (hρ : ρ < 1/2) (N : ℕ) :
    let Q := (closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1) ×ˢ sphere (0 : E) 1
    let F := lowGaugeAngularExpansionProfile m w a G C S i j
    ∃ (W : Set ((E × E) × E)) (M : ℝ), IsOpen W ∧ Q ⊆ W ∧ ContDiffOn ℝ ∞ F W ∧
      0 ≤ M ∧ ∀ k ≤ N, ∀ x ∈ Q, ‖iteratedFDeriv ℝ k F x‖ ≤ M := by
  classical
  let Q := (closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1) ×ˢ sphere (0 : E) 1
  let reorder (x : (E × E) × E) : E × E × E := (x.2, x.1.1, x.1.2)
  let W := reorder ⁻¹' cyclicLowProfileSet
  let F := lowGaugeAngularExpansionProfile m w a G C S i j
  have hReorder : ContDiff ℝ ∞ reorder :=
    contDiff_snd.prodMk ((contDiff_fst.comp contDiff_fst).prodMk (contDiff_snd.comp contDiff_fst))
  have hW : IsOpen W := isOpen_cyclicLowProfileSet.preimage hReorder.continuous
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod (isCompact_sphere _ _) |>.prod (isCompact_sphere _ _)
  have hSub : Q ⊆ W := by
    intro x hx
    have hRatio : ‖x.1.1‖ ≤ ρ := mem_closedBall_zero_iff.mp hx.1.1
    have hHigh : ‖x.1.2‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx.1.2
    have hLow : ‖x.2‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx.2
    change 1/4 < ‖x.2‖ ∧ ‖x.1.1‖ < 1/2 ∧ 3/4 < ‖x.1.2‖
    exact ⟨by rw [hLow]; norm_num, hRatio.trans_lt hρ, by rw [hHigh]; norm_num⟩
  have hF : ContDiffOn ℝ ∞ F W :=
    (lowGaugeJointProfile_contDiffOn m w a ha G C S hS i j).comp hReorder.contDiffOn (fun _ h => h)
  have hBound (k : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Q, ‖iteratedFDeriv ℝ k F x‖ ≤ B := by
    have hOrder : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have hContinuity : ContinuousOn (iteratedFDeriv ℝ k F) W :=
      (hF.continuousOn_iteratedFDerivWithin hOrder hW.uniqueDiffOn).congr
        (fun x hx => (iteratedFDerivWithin_of_isOpen k hW hx).symm)
    obtain ⟨B, hB⟩ := hQ.bddAbove_image (hContinuity.norm.mono hSub)
    exact ⟨max B 0, le_max_right _ _, fun x hx => (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩
  choose B hB hDeriv using hBound
  refine ⟨W, ∑ k ∈ Finset.range (N + 1), B k, hW, hSub, hF, Finset.sum_nonneg (fun k _ => hB k), ?_⟩
  intro k hk x hx
  exact (hDeriv k x hx).trans (Finset.single_le_sum (fun l _ => hB l)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))

end Burnett.V08
