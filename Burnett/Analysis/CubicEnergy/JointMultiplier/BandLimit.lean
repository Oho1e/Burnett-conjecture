import Burnett.Analysis.CubicEnergy.JointMultiplier.BandPartition
import Burnett.Analysis.CubicEnergy.JointMultiplier.BlockOperator

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Filter
open scoped ContDiff FourierTransform RealInnerProductSpace Topology BigOperators

def partialSymbol (m : Joint → ℝ) (N : ℕ) (p : Joint) : ℂ :=
  ∑ k ∈ Finset.range (N+N), symbolBlock m (bandFactor N k • p)

private theorem finite_window (m : Joint → ℝ) (hhom : ∀ t : ℝ, 0<t → ∀ z, m (t • z)=m z)
    (p : Joint) (N l : ℕ) :
    (∑ k ∈ Finset.range l, symbolBlock m (bandFactor N k • p)) =
    ((ballWindow (bandFactor N 0 • splitFreq.symm p) -
        ballWindow (bandFactor N l • splitFreq.symm p) : ℝ) : ℂ) * (m p : ℂ) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hpos : 0 < bandFactor N l := by unfold bandFactor; positivity
    have hnext : 2*bandFactor N l = bandFactor N (l+1) := by simp only [bandFactor,pow_succ']; ring
    rw [Finset.sum_range_succ,ih,symbolBlock,map_smul,hhom _ hpos,annularWindow,smul_smul,hnext]
    push_cast
    ring

theorem partialSymbol_norm_le (m : Joint → ℝ) (hhom : ∀ t : ℝ, 0<t → ∀ z, m (t • z)=m z)
    (p : Joint) (N : ℕ) : ‖partialSymbol m N p‖ ≤ ‖m p‖ := by
  unfold partialSymbol
  rw [finite_window m hhom,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs]
  apply mul_le_of_le_one_left (norm_nonneg _)
  apply abs_le.mpr
  constructor <;> linarith [ballWindow.nonneg (x := bandFactor N 0 • splitFreq.symm p),
     ballWindow.le_one (x := bandFactor N 0 • splitFreq.symm p),
     ballWindow.nonneg (x := bandFactor N (N+N) • splitFreq.symm p),
     ballWindow.le_one (x := bandFactor N (N+N) • splitFreq.symm p)]

def testCarrier (f v : SchwartzMap E ℂ) (x : E) (p : Joint) : ℂ :=
  Complex.exp ((↑(2*Real.pi*(inner ℝ p.1 x + inner ℝ p.2 x)) : ℂ)*Complex.I) *
    (𝓕 (f : E → ℂ) p.1 * 𝓕 (v : E → ℂ) p.2)

theorem testCarrier_integrable (f v : SchwartzMap E ℂ) (x : E) : Integrable (testCarrier f v x) := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let V := SchwartzMap.fourierTransformCLM ℂ v
  have base : Integrable (fun p : Joint => F p.1 * V p.2) := F.integrable.mul_prod V.integrable
  have hc : Continuous (fun p : Joint => Complex.exp ((↑(2*Real.pi*(inner ℝ p.1 x + inner ℝ p.2 x)) : ℂ)*Complex.I)) := by fun_prop
  exact base.norm.mono' (hc.mul ((F.continuous.comp continuous_fst).mul (V.continuous.comp continuous_snd))).aestronglyMeasurable
    (.of_forall fun p => by simp [testCarrier,Complex.norm_exp,F,V])

/-- For Schwartz inputs the true frequency integrals of the two-sided partial
sums converge pointwise, with domination coming from the telescoped cutoff. -/
theorem partialSymbol_integrals_tendsto (m : Joint → ℝ) (hs : ContDiffOn ℝ ∞ m {p | p ≠ 0})
    (hhom : ∀ t : ℝ, 0<t → ∀ z, m (t • z)=m z)
    (C : ℝ) (hC : ∀ p, ‖m p‖ ≤ C) (f v : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun N => ∫ p, partialSymbol m N p * testCarrier f v x p)
      atTop (𝓝 (∫ p, (m p : ℂ)*testCarrier f v x p)) := by
  have hK := (symbolBlock_regular m hs).2.continuous
  have hS (N : ℕ) : Continuous (partialSymbol m N) := by
    apply continuous_finset_sum
    intro k _
    exact hK.comp (continuous_const.smul continuous_id)
  have hT := testCarrier_integrable f v x
  refine tendsto_integral_of_dominated_convergence (fun p => C*‖testCarrier f v x p‖)
    (fun N => (hS N).aestronglyMeasurable.mul hT.aestronglyMeasurable) (hT.norm.const_mul C) ?_ ?_
  · intro N
    filter_upwards with p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((partialSymbol_norm_le m hhom p N).trans (hC p)) (norm_nonneg _)
  · haveI : NoAtoms (volume : Measure Joint) := by rw [Measure.volume_eq_prod E E]; infer_instance
    filter_upwards [(Set.countable_singleton (0 : Joint)).ae_notMem volume] with p hp
    apply tendsto_const_nhds.congr'
    filter_upwards [annular_partition_symbol m hhom p hp] with N hN
    simp only [partialSymbol,hN]

end Burnett.A02.FrequencySplit
