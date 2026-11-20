import Burnett.Analysis.CubicEnergy.JointMultiplier.BandLimit

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Filter Burnett.RicciSymbol
open scoped ContDiff Topology BigOperators

def spatialBlock (m : Joint → ℝ) (s : ℝ) (f v : SchwartzMap E ℂ) (x : E) : ℂ :=
  ∫ y : Joint, blockKernel (symbolBlock m) y * (f (x-s • y.1) * v (x-s • y.2))

private theorem profile_bound (m : Joint → ℝ) (hs : ContDiffOn ℝ ∞ m {p | p ≠ 0})
    (hhom : ∀ t : ℝ, 0<t → ∀ z, m (t • z)=m z) :
    ∃ C : ℝ, ∀ p, ‖m p‖ ≤ C := by
  obtain ⟨C,_,bound⟩ := degreeZero_derivative_bounds m hs hhom 0
  refine ⟨max C ‖m 0‖,fun p => ?_⟩
  by_cases h : p=0
  · simpa only [h] using le_max_right C ‖m 0‖
  · exact (by simpa using bound p h : ‖m p‖ ≤ C).trans (le_max_left _ _)

/-- Both frequency tails can be removed simultaneously in the actual physical
block operators, for every Schwartz input pair and every evaluation point. -/
theorem spatial_partial_sums_tendsto (m : Joint → ℝ) (hs : ContDiffOn ℝ ∞ m {p | p ≠ 0})
    (hhom : ∀ t : ℝ, 0<t → ∀ z, m (t • z)=m z)
    (f v : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun N => ∑ k ∈ Finset.range (N+N), spatialBlock m (bandFactor N k) f v x) atTop
      (𝓝 (∫ p, (m p : ℂ)*testCarrier f v x p)) := by
  obtain ⟨C,hC⟩ := profile_bound m hs hhom
  obtain ⟨hcomp,hsm⟩ := symbolBlock_regular m hs
  have hP (s : ℝ) : spatialBlock m s f v x =
      ∫ p, symbolBlock m (s • p) * testCarrier f v x p :=
    block_operator_fourier (symbolBlock m) hcomp hsm s f v x
  have hb : ∃ D : ℝ, ∀ p, ‖symbolBlock m p‖ ≤ D := by
    obtain ⟨p,hp⟩ := hsm.continuous.norm.exists_forall_ge_of_hasCompactSupport hcomp.norm
    exact ⟨_,hp⟩
  obtain ⟨D,hD⟩ := hb
  have hT := testCarrier_integrable f v x
  have hi (s : ℝ) : Integrable (fun p => symbolBlock m (s • p) * testCarrier f v x p) := by
    exact hT.bdd_mul ((hsm.continuous.comp (continuous_const.smul continuous_id)).aestronglyMeasurable) ⟨D,fun p => hD _⟩
  refine (partialSymbol_integrals_tendsto m hs hhom C hC f v x).congr ?_
  intro N
  simp_rw [hP]
  rw [← integral_finset_sum _ (fun k _ => hi (bandFactor N k))]
  apply integral_congr_ae
  filter_upwards with p
  simp only [partialSymbol,Finset.sum_mul]

theorem cubic_symbols_spatial_reconstruction (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hh : ∀ t : ℝ, 0<t → ∀ z, b (t • z)=t*b z) (j : Index)
    (m : Joint → ℝ) (h : m = (fun q => lowSymbol b j q.1 q.2) ∨
      m = (fun q => productSymbol j q.1 q.2) ∨ m = (fun q => inputSymbol j q.1 q.2))
    (f v : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun N => ∑ k ∈ Finset.range (N+N), spatialBlock m (bandFactor N k) f v x) atTop
      (𝓝 (∫ p, (m p : ℂ)*testCarrier f v x p)) := by
  obtain ⟨hl,hp,hi,_⟩ := (commutator_symbol_decomposition b hb hh).1 j
  rcases h with rfl|rfl|rfl
  · exact spatial_partial_sums_tendsto _ hl.1 (fun t ht q => lowSymbol_scale hb hh j t ht q.1 q.2) f v x
  · exact spatial_partial_sums_tendsto _ hp.1 (fun t ht q => (highSymbols_scale j t ht q.1 q.2).1) f v x
  · exact spatial_partial_sums_tendsto _ hi.1 (fun t ht q => (highSymbols_scale j t ht q.1 q.2).2) f v x

end Burnett.A02.FrequencySplit
