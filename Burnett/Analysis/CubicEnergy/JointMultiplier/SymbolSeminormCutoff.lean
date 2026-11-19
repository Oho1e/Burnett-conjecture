import Burnett.Analysis.CubicEnergy.JointMultiplier.SymbolSeminormAnnulus

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Finset MeasureTheory Metric Set
open scoped ContDiff Topology

/-- Smooth multiplication by the fixed reference cutoff costs a dimensionless
constant and no additional derivative order on the compact annulus. -/
theorem symbol_reference_cutoff_bound (N : ℕ) : ∃ L : ℝ, 0≤L ∧ ∀ (m : Joint → ℝ)
    (_hm : ContDiffOn ℝ ∞ m {z | z ≠ 0}) (D : ℝ), 0≤D →
    (∀ i : ℕ, i≤N → ∀ ξ ∈ symbolReferenceShell,
      ‖iteratedFDeriv ℝ i (fun u => m (splitFreq u)) ξ‖ ≤ D) →
    ∀ i : ℕ, i≤N → ∀ ξ ∈ symbolReferenceShell,
      ‖iteratedFDeriv ℝ i (fun u => symbolBlock m (splitFreq u)) ξ‖ ≤ L*D := by
  have cs : ContDiff ℝ ∞ annularWindow :=
    ballWindow.contDiff.sub (ballWindow.contDiff.comp (contDiff_const.smul contDiff_id))
  have compact : IsCompact symbolReferenceShell := (isCompact_closedBall (0:Freq8) 2).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    (fun ξ h => by simpa only [mem_closedBall,dist_zero_right] using h.2)
  have ex (i : ℕ) : ∃ B : ℝ, 0≤B ∧ ∀ ξ ∈ symbolReferenceShell, ‖iteratedFDeriv ℝ i annularWindow ξ‖ ≤ B := by
    have cd : Continuous (iteratedFDeriv ℝ i annularWindow) := cs.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨b,hb⟩ := compact.bddAbove_image cd.norm.continuousOn
    exact ⟨max b 0,le_max_right _ _,fun ξ hξ => (hb (mem_image_of_mem _ hξ)).trans (le_max_left _ _)⟩
  choose B Bpos bc using ex
  let L := fun i : ℕ => ∑ z ∈ range (i+1), (i.choose z:ℝ)*B z
  have lpos (i : ℕ) : 0≤L i := sum_nonneg (fun z _ => mul_nonneg (Nat.cast_nonneg _) (Bpos z))
  refine ⟨∑ i ∈ range (N+1), L i,sum_nonneg (fun i _ => lpos i),?_⟩
  intro m hm D hd bd i hi ξ hξ
  let U : Set Freq8 := {z | z ≠ 0}
  let f := fun u => m (splitFreq u)
  have ho : IsOpen U := isClosed_singleton.isOpen_compl
  have h0 : ξ ∈ U := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : 0<(1:ℝ)/2) hξ.1)
  have fs : ContDiffOn ℝ ∞ f U := hm.comp splitFreq.contDiff.contDiffOn (fun z hz h => hz (splitFreq.injective (h.trans splitFreq.map_zero.symm)))
  have order_le : (i:WithTop ℕ∞)≤∞ := by exact_mod_cast le_top
  let g := fun u => annularWindow u * f u
  have cast : ‖iteratedFDeriv ℝ i (fun u => symbolBlock m (splitFreq u)) ξ‖ = ‖iteratedFDeriv ℝ i g ξ‖ := by
    have e : (fun u => symbolBlock m (splitFreq u)) = Complex.ofRealLI ∘ g := by
      funext u; simp only [symbolBlock,ContinuousLinearEquiv.symm_apply_apply]; rfl
    rw [e]
    exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left ((cs.contDiffAt).mul (fs.contDiffAt (ho.mem_nhds h0))) order_le
  rw [cast]
  have prod := norm_iteratedFDerivWithin_mul_le cs.contDiffOn fs ho.uniqueDiffOn h0 order_le
  simp only [iteratedFDerivWithin_of_isOpen _ ho h0] at prod
  apply prod.trans
  have lw : L i ≤ ∑ l ∈ range (N+1), L l :=
    single_le_sum (fun l _ => lpos l) (mem_range.mpr (by omega : i<N+1))
  refine le_trans ?_ (mul_le_mul_of_nonneg_right lw hd)
  rw [show L i = _ from rfl,Finset.sum_mul]
  apply sum_le_sum
  intro z hz
  exact mul_le_mul (mul_le_mul_of_nonneg_left (bc z ξ hξ) (Nat.cast_nonneg _))
    (bd _ (by omega) ξ hξ) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Bpos z))

/-- The uniform mixed moment depends only on a finite jet of the *uncut*
real scalar symbol on the eight-dimensional reference annulus. -/
theorem symbol_joint_annular_moment (j k : ℕ) : ∃ C : ℝ, 0≤C ∧
    ∀ (m : Joint → ℝ) (_hm : ContDiffOn ℝ ∞ m {z | z ≠ 0}) (D : ℝ), 0≤D →
      (∀ i : ℕ, i≤j+k+9 → ∀ ξ ∈ symbolReferenceShell,
        ‖iteratedFDeriv ℝ i (fun u => m (splitFreq u)) ξ‖ ≤ D) →
      (∫ y : Joint, (1+‖y.1‖)^j*(1+‖y.2‖)^k*‖blockKernel (symbolBlock m) y‖) ≤ C*D := by
  obtain ⟨L,hL,cut⟩ := symbol_reference_cutoff_bound (j+k+9)
  obtain ⟨C,hC,mass⟩ := symbolBlock_mixed_moment_finite_derivatives j k
  exact ⟨C*L,mul_nonneg hC hL,fun m hm D hd der =>
    (mass m hm (L*D) (mul_nonneg hL hd) (cut m hm D hd der)).trans_eq (mul_assoc ..).symm⟩

end Burnett.A02.FrequencySplit
