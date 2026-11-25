import Burnett.Analysis.Microlocal.Overlap.GlobalOriginalCovariantCutoff
import Burnett.Geometry.Cotangent.CompactTestPartition

/-! Fixed global plateaux and exact finite decompositions of original tests. -/
set_option autoImplicit false
set_option maxRecDepth 4650
set_option maxHeartbeats 4800000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.CotangentTests (exists_finite_smooth_cutoffs_on_compact)
open scoped ContDiff Manifold Topology BigOperators

local notation "E" => CoordinateSpace
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- A chart-supported global scalar is one throughout an open neighbourhood
of any compact subset of its chart. -/
theorem exists_globalPlateau_in_chart (c : AtlasChart M) (S : Set M) (hS : IsCompact S)
    (hSc : S ⊆ c.chart.source) :
    ∃ (V : Set M) (β : M → ℝ), IsOpen V ∧ S ⊆ V ∧
      ContMDiff Model 𝓘(ℝ) ∞ β ∧ HasCompactSupport β ∧
      tsupport β ⊆ c.chart.source ∧ ∀ x ∈ V, β x = 1 := by
  obtain ⟨n, _, f, V, hV, hSV, hf, hOne⟩ :=
    exists_finite_smooth_cutoffs_on_compact (fun _ : Unit => c.chart.source)
      (fun _ => c.chart.open_source) hS
      (fun _ hx => mem_iUnion.mpr ⟨(), hSc hx⟩)
  let β (p : M) := ∑ i, f i p
  let Z := ⋃ i, tsupport (f i)
  have hZ : IsCompact Z := isCompact_iUnion fun i => (hf i).2.1
  have hβZ : tsupport β ⊆ Z := by
    apply closure_minimal _ hZ.isClosed
    intro x hx
    by_contra hOutside
    have hz (i : Fin n) : f i x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hi => hOutside (mem_iUnion.mpr ⟨i, hi⟩))
    exact hx (Finset.sum_eq_zero fun i _ => hz i)
  exact ⟨V, β, hV, hSV, contMDiff_finset_sum (fun i _ => (hf i).1),
    hZ.of_isClosed_subset isClosed_closure hβZ,
    hβZ.trans (iUnion_subset fun i => (hf i).2.2.1), hOne⟩

variable [SecondCountableTopology M]

omit [T2Space M] in
/-- Compactly supported scalar sums lift to exact sums of the actual original
covariant jet sections. -/
theorem originalCovariantGlobalCutoffTest_eq_finiteSum {ι : Type*} [Fintype ι]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (α : M → ℝ) (hα : ContMDiff Model 𝓘(ℝ) ∞ α) (hαc : HasCompactSupport α)
    (a : ι → M → ℝ) (ha : ∀ l, ContMDiff Model 𝓘(ℝ) ∞ (a l))
    (hac : ∀ l, HasCompactSupport (a l)) (hSum : ∀ x, ∑ l, a l x = α x) (n : ℕ) :
    originalCovariantGlobalCutoffTest r B g hB hg hsB hsG α hα hαc n =
      ∑ l, originalCovariantGlobalCutoffTest r B g hB hg hsB hsG (a l) (ha l) (hac l) n := by
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_sum, Finset.sum_apply, originalCovariantGlobalCutoffTest,
    globalCutoffSymmetricJetTest_apply]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, hSum x]

end Burnett.Microlocal.Overlap
