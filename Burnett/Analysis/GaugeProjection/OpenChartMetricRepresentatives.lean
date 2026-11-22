import Burnett.Analysis.GaugeProjection.LocalizedMetricSchwartzInputs
import Burnett.Analysis.LocalWeakDerivative
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.P01

open Set Filter Metric
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open scoped Topology ContDiff Manifold

/-- A single real smooth cutoff equal to one near the compact localization
set, with its full support inside the given open chart. -/
theorem exists_projectedChartCutoff {K U : Set CoordinateSpace} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ η : CoordinateSpace → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      ∃ V : Set CoordinateSpace, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn η 1 V := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : CoordinateSpace)
  let W := U ∩ ball (0 : CoordinateSpace) r
  have hW : IsOpen W := hU.inter isOpen_ball
  have hKW : K ⊆ W := subset_inter hKU hr
  obtain ⟨η, h0, h1, _⟩ := exists_smooth_zero_one_nhds_of_isClosed 𝓘(ℝ, CoordinateSpace)
    hW.isClosed_compl hK.isClosed (disjoint_left.mpr fun _ hx hKx => hx (hKW hKx))
  have hs : tsupport (η : CoordinateSpace → ℝ) ⊆ W := by
    intro x hx
    by_contra hn
    exact (notMem_tsupport_iff_eventuallyEq.mpr (h0.filter_mono (nhds_le_nhdsSet hn))) hx
  have hComp : HasCompactSupport (η : CoordinateSpace → ℝ) :=
    (isCompact_closedBall (0 : CoordinateSpace) r).of_isClosed_subset isClosed_closure
      (hs.trans (inter_subset_right.trans ball_subset_closedBall))
  obtain ⟨V, hV, hKV, hVone⟩ := mem_nhdsSet_iff_exists.mp h1
  exact ⟨η, η.contMDiff.contDiff, hComp, hs.trans inter_subset_left,
    V ∩ U, hV.inter hU, subset_inter hKV hKU, inter_subset_right, fun x hx => hVone hx.1⟩

/-- Apply the same scalar cutoff to every component of a coordinate metric. -/
def cutoffCoordinateMetric (η : CoordinateSpace → ℝ) (g : CoordinateSpace → Tensor2)
    (x : CoordinateSpace) (i j : Index) : ℝ :=
  η x * g x i j

private theorem cutoffCoordinateMetric_smooth {η : CoordinateSpace → ℝ}
    {g : CoordinateSpace → Tensor2} {U : Set CoordinateSpace} (hU : IsOpen U)
    (hη : ContDiff ℝ ∞ η) (hηU : tsupport η ⊆ U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) U) :
    SmoothCoordinateComponents (cutoffCoordinateMetric η g) :=
  fun i j => Burnett.Analysis.LocalWeakDerivative.contDiff_test_mul_local hU hη hηU (hg i j)

private theorem cutoffCoordinateMetric_eqOn {η : CoordinateSpace → ℝ} {g : CoordinateSpace → Tensor2}
    {V : Set CoordinateSpace} (hη : EqOn η 1 V) :
    EqOn (cutoffCoordinateMetric η g) g V := by
  intro x hx
  funext i j
  simp only [cutoffCoordinateMetric, hη hx, Pi.one_apply, one_mul]

/-- Global smooth representatives of all coordinate tensors and the background,
chosen with one cutoff that equals one near the compact set. -/
theorem exists_openChartMetricRepresentatives {K U : Set CoordinateSpace}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (g : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (hg : ∀ n i j, ContDiffOn ℝ ∞ (fun x => g n x i j) U)
    (hg₀ : ∀ i j, ContDiffOn ℝ ∞ (fun x => g₀ x i j) U) :
    ∃ (G : ℕ → CoordinateSpace → Tensor2) (G₀ : CoordinateSpace → Tensor2),
      (∀ n, SmoothCoordinateComponents (G n)) ∧ SmoothCoordinateComponents G₀ ∧
      (∀ n, G n =ᶠ[𝓝ˢ K] g n) ∧ G₀ =ᶠ[𝓝ˢ K] g₀ := by
  obtain ⟨η, hη, _, hηU, V, hV, hKV, _, hηV⟩ := exists_projectedChartCutoff hK hU hKU
  have agree (f : CoordinateSpace → Tensor2) : cutoffCoordinateMetric η f =ᶠ[𝓝ˢ K] f :=
    eventually_of_mem (hV.mem_nhdsSet.mpr hKV) fun _ hx => cutoffCoordinateMetric_eqOn hηV hx
  exact ⟨fun n => cutoffCoordinateMetric η (g n), cutoffCoordinateMetric η g₀,
    fun n => cutoffCoordinateMetric_smooth hU hη hηU (hg n),
    cutoffCoordinateMetric_smooth hU hη hηU hg₀, fun n => agree (g n), agree g₀⟩

end Burnett.P01
