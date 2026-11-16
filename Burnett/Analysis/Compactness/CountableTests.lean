import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Simultaneous subsequences for countable scalar tests

This is the countable compactness step used in F05. It supplies neither
pseudodifferential operator bounds nor positivity or a microlocal measure.
-/

open Filter Set Topology

namespace Burnett.Analysis.Compactness

/-- One subsequence works for every member of a countable family of tests
whose values lie in specified compact sets. -/
theorem exists_subsequence_all_tests
    {ι X : Type*} [Countable ι] [TopologicalSpace X] [FirstCountableTopology X]
    (a : ℕ → ι → X) (K : ι → Set X) (hK : ∀ j, IsCompact (K j))
    (ha : ∀ n j, a n j ∈ K j) :
    ∃ l : ι → X, (∀ j, l j ∈ K j) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ j, Tendsto (fun n => a (φ n) j) atTop (𝓝 (l j)) := by
  have hprod : IsCompact (Set.pi Set.univ K) := isCompact_univ_pi hK
  obtain ⟨l, hl, φ, hφ, hlim⟩ := hprod.tendsto_subseq
    (fun n j _ => ha n j)
  refine ⟨l, fun j => hl j (Set.mem_univ j), φ, hφ, ?_⟩
  intro j
  simpa only [Function.comp_apply] using
    ((continuous_apply j).continuousAt.tendsto.comp hlim)

/-- Uniform boundedness in the sequence index for each real scalar test
gives one strictly increasing subsequence along which all tests converge. -/
theorem exists_subsequence_of_testwise_abs_le
    {ι : Type*} [Countable ι] (a : ℕ → ι → ℝ) (C : ι → ℝ)
    (ha : ∀ n j, |a n j| ≤ C j) :
    ∃ l : ι → ℝ, (∀ j, |l j| ≤ C j) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ j, Tendsto (fun n => a (φ n) j) atTop (𝓝 (l j)) := by
  obtain ⟨l, hl, φ, hφ, hlim⟩ := exists_subsequence_all_tests
    a (fun j => Set.Icc (-C j) (C j)) (fun _ => isCompact_Icc)
    (fun n j => abs_le.mp (ha n j))
  exact ⟨l, fun j => abs_le.mpr (hl j), φ, hφ, hlim⟩

end Burnett.Analysis.Compactness
