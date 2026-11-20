import Burnett.Analysis.CubicEnergy.JointMultiplier.AnnularBound

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Filter Metric Burnett.RicciSymbol
open scoped BigOperators Topology ContDiff

/-- The dilation parameter for consecutive annular blocks in a two-sided partial sum. -/
def bandFactor (N k : ℕ) : ℝ := (2:ℝ)^k * ((2:ℝ)^N)⁻¹

private theorem telescope (u : Freq8) (l : ℕ) :
    ∑ k ∈ Finset.range l, annularWindow ((2:ℝ)^k • u) =
      ballWindow u - ballWindow ((2:ℝ)^l • u) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Finset.sum_range_succ,ih,annularWindow,smul_smul,pow_succ']
    ring

private theorem window_sum (u : Freq8) (hu : u ≠ 0) :
    ∀ᶠ N : ℕ in atTop, (∑ k ∈ Finset.range (N+N), annularWindow (bandFactor N k • u)) = 1 := by
  have hn := norm_pos_iff.mpr hu
  have big := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually
    (eventually_ge_atTop (max ‖u‖ (2/‖u‖)))
  filter_upwards [big] with N hN
  have hd : 0 < (2:ℝ)^N := pow_pos (by norm_num) _
  have lo : ‖((2:ℝ)^N)⁻¹ • u‖ ≤ 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
    exact (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hN) (inv_nonneg.mpr hd.le)).trans_eq
      (inv_mul_cancel₀ hd.ne')
  have hi : 2 ≤ ‖(2:ℝ)^N • u‖ := by
    rw [norm_smul,Real.norm_of_nonneg hd.le]
    exact (div_le_iff₀ hn).mp ((le_max_right _ _).trans hN)
  have collapse : (2:ℝ)^(N+N)*((2:ℝ)^N)⁻¹ = (2:ℝ)^N := by
    rw [pow_add,mul_assoc,mul_inv_cancel₀ hd.ne',mul_one]
  have lo' := ballWindow.one_of_mem_closedBall (x := ((2:ℝ)^N)⁻¹ • u)
    (by simpa only [mem_closedBall,dist_zero_right] using lo)
  have hi' := ballWindow.zero_of_le_dist (x := (2:ℝ)^N • u)
    (by simpa only [dist_zero_right] using hi)
  simpa only [bandFactor,smul_smul,collapse,lo',hi',sub_zero] using telescope (((2:ℝ)^N)⁻¹ • u) (N+N)

theorem annular_partition_symbol (m : Joint → ℝ)
    (hhom : ∀ t : ℝ, 0<t → ∀ z, m (t • z)=m z) (z : Joint) (hz : z ≠ 0) :
    ∀ᶠ N : ℕ in atTop, (∑ k ∈ Finset.range (N+N), symbolBlock m (bandFactor N k • z)) = (m z : ℂ) := by
  have ne : splitFreq.symm z ≠ 0 := fun eq => hz (splitFreq.symm.injective (eq.trans splitFreq.symm.map_zero.symm))
  filter_upwards [window_sum (splitFreq.symm z) ne] with N hN
  have hreal : (∑ k ∈ Finset.range (N+N), annularWindow (bandFactor N k • splitFreq.symm z)*m z) = m z := by
    rw [← Finset.sum_mul,hN,one_mul]
  have hs (k : ℕ) : 0 < bandFactor N k := by unfold bandFactor; positivity
  simpa only [symbolBlock,map_smul,hhom _ (hs _) z,Complex.ofReal_mul,Complex.ofReal_sum] using
    congrArg (fun x : ℝ => (x : ℂ)) hreal

theorem commutator_annular_partition (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ z, b (t • z)=t*b z) (j : Index)
    (m : Joint → ℝ) (h : m = (fun q => lowSymbol b j q.1 q.2) ∨
      m = (fun q => productSymbol j q.1 q.2) ∨ m = (fun q => inputSymbol j q.1 q.2))
    (z : Joint) (hz : z ≠ 0) :
    ∀ᶠ N : ℕ in atTop, (∑ k ∈ Finset.range (N+N), symbolBlock m (bandFactor N k • z)) = (m z : ℂ) := by
  apply annular_partition_symbol m _ z hz
  intro t ht q
  rcases h with rfl|rfl|rfl
  · exact lowSymbol_scale hb hh j t ht q.1 q.2
  · exact (highSymbols_scale j t ht q.1 q.2).1
  · exact (highSymbols_scale j t ht q.1 q.2).2

end Burnett.A02.FrequencySplit
