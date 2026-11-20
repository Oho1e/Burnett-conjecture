import Burnett.Analysis.CubicEnergy.JointMultiplier.JointFiniteTrilinear

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Filter Finset
open scoped ENNReal FourierTransform ContDiff Topology

def jointTestFactor (f g h : SchwartzMap E ℂ) (p : Joint) : ℂ :=
  𝓕 (f : E → ℂ) p.1 * 𝓕 (g : E → ℂ) p.2 * 𝓕 (h : E → ℂ) (-(p.1+p.2))

def jointTrilinear (m : Joint → ℝ) (f g h : SchwartzMap E ℂ) : ℂ :=
  ∫ p : Joint, (m p : ℂ)*jointTestFactor f g h p

theorem integrable_jointTestFactor (f g h : SchwartzMap E ℂ) : Integrable (jointTestFactor f g h) := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let G := SchwartzMap.fourierTransformCLM ℂ g
  let H := SchwartzMap.fourierTransformCLM ℂ h
  have base : Integrable (fun p : Joint => F p.1*G p.2) := F.integrable.mul_prod G.integrable
  have co : Continuous (fun p : Joint => H (-(p.1+p.2))) := H.continuous.comp (continuous_fst.add continuous_snd).neg
  have weighted := base.bdd_mul co.aestronglyMeasurable ⟨_,fun p => H.norm_le_seminorm ℂ _⟩
  exact weighted.congr (.of_forall fun p => mul_comm _ _)

theorem joint_symbol_bounded (m : Joint → ℝ) (hs : ContDiffOn ℝ ∞ m {p | p ≠ 0})
    (hhom : ∀ t : ℝ, 0<t → ∀ z, m (t • z)=m z) : ∃ C : ℝ, ∀ p, ‖m p‖ ≤ C := by
  obtain ⟨C,_,bound⟩ := degreeZero_derivative_bounds m hs hhom 0
  refine ⟨max C ‖m 0‖,?_⟩
  intro p
  by_cases h : p=0
  · simpa only [h] using le_max_right C ‖m 0‖
  · exact (by simpa using bound p h : ‖m p‖ ≤ C).trans (le_max_left _ _)

/-- Removing both dyadic tails in the actual tested physical blocks gives the
trilinear Fourier integral with the original symbol, including the true output
frequency of the test. -/
theorem joint_tested_sums_converge (m : Joint → ℝ) (hs : ContDiffOn ℝ ∞ m {p | p ≠ 0})
    (hhom : ∀ t : ℝ, 0<t → ∀ z, m (t • z)=m z) (f g h : SchwartzMap E ℂ) :
    Tendsto (fun N => ∑ i : Fin (N+N), testedBlock (symbolBlock m) (bandFactor N (i:ℕ)) f g h)
      atTop (𝓝 (jointTrilinear m f g h)) := by
  obtain ⟨C,hC⟩ := joint_symbol_bounded m hs hhom
  obtain ⟨hc,hd⟩ := symbolBlock_regular m hs
  let H := jointTestFactor f g h
  have hi := integrable_jointTestFactor f g h
  have co (N : ℕ) : Continuous (partialSymbol m N) := by
    apply continuous_finset_sum
    intro k _
    exact hd.continuous.comp (continuous_const.smul continuous_id)
  have lim : Tendsto (fun N => ∫ p : Joint, partialSymbol m N p*H p) atTop
      (𝓝 (jointTrilinear m f g h)) := by
    unfold jointTrilinear
    refine tendsto_integral_of_dominated_convergence (fun p => C*‖H p‖)
      (fun N => (co N).aestronglyMeasurable.mul hi.aestronglyMeasurable) (hi.norm.const_mul C) ?_ ?_
    · intro N
      filter_upwards with p
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((partialSymbol_norm_le m hhom p N).trans (hC p)) (norm_nonneg _)
    · haveI : NoAtoms (volume : Measure Joint) := by rw [Measure.volume_eq_prod E E]; infer_instance
      filter_upwards [(Set.countable_singleton (0 : Joint)).ae_notMem volume] with p hp
      apply tendsto_const_nhds.congr'
      filter_upwards [annular_partition_symbol m hhom p hp] with N hN
      simp only [partialSymbol,hN,H]
  refine lim.congr ?_
  intro N
  have shape (t : ℝ) : triDensity (symbolBlock m) t f g h =
      fun p => symbolBlock m (t • p)*H p := by
    funext p
    simp only [triDensity,H,jointTestFactor,mul_assoc]
  have iv (k : ℕ) : Integrable (fun p : Joint => symbolBlock m (bandFactor N k • p)*H p) := by
    rw [← shape]
    exact integrable_triDensity (symbolBlock m) hc hd _ f g h
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => testedBlock (symbolBlock m) (bandFactor N k) f g h)]
  simp_rw [testedBlock_density (symbolBlock m) hc hd,shape]
  rw [← integral_finset_sum _ (fun k _ => iv k)]
  apply integral_congr_ae
  filter_upwards with p
  simp only [partialSymbol,Finset.sum_mul]

/-- The paper's full-scale trilinear estimate on actual Schwartz tests, with
three explicit reference-kernel moments controlling the symbol. -/
theorem joint_trilinear_weighted (p s z : ℝ) (hp : 1<p) (hs : 1<s) (hz : 1<z) (bal : triBalance p s z) :
    ∃ B₁ B₂ B₃ : ℝ≥0∞, B₁<⊤ ∧ B₂<⊤ ∧ B₃<⊤ ∧
      ∀ (m : Joint → ℝ), ContDiffOn ℝ ∞ m {y | y ≠ 0} →
      (∀ t : ℝ, 0<t → ∀ y, m (t • y)=m y) → ∀ (f g h : SchwartzMap E ℂ),
      ‖jointTrilinear m f g h‖ₑ ≤
        (B₁*kernelMoment (symbolBlock m) 1 1+B₂*kernelMoment (symbolBlock m) 5 1+
          B₃*kernelMoment (symbolBlock m) 1 5)*triLpMass f g h p s z := by
  obtain ⟨B₁,B₂,B₃,h₁,h₂,h₃,est⟩ := joint_finite_trilinear p s z hp hs hz bal
  refine ⟨B₁,B₂,B₃,h₁,h₂,h₃,?_⟩
  intro m hm hh f g h
  have tend := joint_tested_sums_converge m hm hh f g h
  refine le_of_tendsto ((continuous_enorm.tendsto _).comp tend) (.of_forall fun N => ?_)
  exact est m hm (((2:ℝ)^N)⁻¹) (by positivity) (N+N) f g h

theorem joint_trilinear_bound (p s z : ℝ) (hp : 1<p) (hs : 1<s) (hz : 1<z) (bal : triBalance p s z)
    (m : Joint → ℝ) (hm : ContDiffOn ℝ ∞ m {y | y ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ y, m (t • y)=m y) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ f g h : SchwartzMap E ℂ,
      ‖jointTrilinear m f g h‖ₑ ≤ C*triLpMass f g h p s z := by
  obtain ⟨B₁,B₂,B₃,h₁,h₂,h₃,est⟩ := joint_trilinear_weighted p s z hp hs hz bal
  obtain ⟨hc,hd⟩ := symbolBlock_regular m hm
  have finite (j k : ℕ) := kernelMoment_lt_top (symbolBlock m) hc hd j k
  exact ⟨_,ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨
    ENNReal.mul_lt_top h₁ (finite 1 1),ENNReal.mul_lt_top h₂ (finite 5 1)⟩,
    ENNReal.mul_lt_top h₃ (finite 1 5)⟩,est m hm hh⟩

end Burnett.A02.FrequencySplit
