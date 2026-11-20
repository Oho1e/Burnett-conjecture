import Burnett.Analysis.CubicEnergy.JointMultiplier.BilinearKernel

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Metric Set Filter Burnett.RicciSymbol
open scoped ENNReal ContDiff Topology

def ballWindow : ContDiffBump (0 : Freq8) := ⟨1,2,by norm_num,by norm_num⟩
def annularWindow (u : Freq8) : ℝ := ballWindow u - ballWindow ((2:ℝ) • u)

private theorem window_smooth : ContDiff ℝ ∞ annularWindow :=
  ballWindow.contDiff.sub (ballWindow.contDiff.comp (contDiff_const.smul contDiff_id))

private theorem center (u : Freq8) (hu : ‖u‖ ≤ 1) : ballWindow u = 1 :=
  ballWindow.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hu)

private theorem outside (u : Freq8) (hu : 2 ≤ ‖u‖) : ballWindow u = 0 :=
  ballWindow.zero_of_le_dist (by simpa only [dist_zero_right] using hu)

private theorem near_zero (u : Freq8) (hu : ‖u‖ ≤ 1/2) : annularWindow u = 0 := by
  rw [annularWindow,center u (by linarith),center _ ?_,sub_self]
  rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  linarith

private theorem far_zero (u : Freq8) (hu : 2 ≤ ‖u‖) : annularWindow u = 0 := by
  rw [annularWindow,outside u hu,outside _ ?_,sub_self]
  rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  linarith

def symbolBlock (m : Joint → ℝ) (p : Joint) : ℂ := (annularWindow (splitFreq.symm p)*m p : ℝ)

theorem symbolBlock_regular (m : Joint → ℝ) (hm : ContDiffOn ℝ ∞ m {q | q ≠ 0}) :
    HasCompactSupport (symbolBlock m) ∧ ContDiff ℝ ∞ (symbolBlock m) := by
  let h := fun u : Freq8 => ((annularWindow u * m (splitFreq u) : ℝ) : ℂ)
  have hc : HasCompactSupport h := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Freq8) 2)
    intro u hu
    by_contra hout
    have hi : 2 ≤ ‖u‖ := by
      have hlt : 2 < ‖u‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hout
      exact hlt.le
    exact hu (by simp [h,far_zero u hi])
  have hd : ContDiff ℝ ∞ h := by
    apply contDiff_iff_contDiffAt.mpr
    intro u
    by_cases hu : u=0
    · subst u
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Freq8 => (0 : ℂ)) 0).congr_of_eventuallyEq
      filter_upwards [ball_mem_nhds (0:Freq8) (by norm_num : 0 < (1:ℝ)/2)] with v hv
      have : ‖v‖ < 1/2 := by simpa only [mem_ball,dist_zero_right] using hv
      simp [h,near_zero v this.le]
    · have ne : splitFreq u ≠ 0 := fun eq => hu (splitFreq.injective (eq.trans splitFreq.map_zero.symm))
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp u
        (window_smooth.contDiffAt.mul ((hm.contDiffAt (isOpen_compl_singleton.mem_nhds ne)).comp u splitFreq.contDiff.contDiffAt))
  have equality : symbolBlock m = h ∘ splitFreq.symm := by
    funext p
    simp only [h,Function.comp_apply,symbolBlock,ContinuousLinearEquiv.apply_symm_apply]
  rw [equality]
  exact ⟨hc.comp_homeomorph splitFreq.symm.toHomeomorph,hd.comp splitFreq.symm.contDiff⟩

/-- This finite single-scale constant is available for each of the three
actual Coifman–Meyer symbols in the first-order commutator. -/
theorem commutator_block_bound (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ z, b (t • z)=t*b z) (j : Index)
    (m : Joint → ℝ) (h : m = (fun q => lowSymbol b j q.1 q.2) ∨
      m = (fun q => productSymbol j q.1 q.2) ∨ m = (fun q => inputSymbol j q.1 q.2)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {p s r t : ℝ≥0∞} [ENNReal.HolderTriple p s r]
      [ENNReal.HolderTriple r t 1] (f v w : SchwartzMap E ℂ) (scale : ℝ),
      (∫⁻ y : Joint, ∫⁻ x, ‖blockKernel (symbolBlock m) y * (f (x-scale • y.1)*v (x-scale • y.2)*w x)‖ₑ) ≤
        C * (eLpNorm (f : E → ℂ) p volume * eLpNorm (v : E → ℂ) s volume * eLpNorm (w : E → ℂ) t volume) := by
  obtain ⟨hl,hp,hi,_⟩ := (commutator_symbol_decomposition b hb hh).1 j
  have hm : ContDiffOn ℝ ∞ m {q | q ≠ 0} := by
    rcases h with rfl|rfl|rfl
    · exact hl.1
    · exact hp.1
    · exact hi.1
  obtain ⟨hc,hs⟩ := symbolBlock_regular m hm
  exact blockKernel_uniform_pairing _ hc hs

end Burnett.A02.FrequencySplit
