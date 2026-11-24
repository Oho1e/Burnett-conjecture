import Burnett.Analysis.Microlocal.Overlap.BaseFourierAction
import Burnett.Geometry.MaximalChart.MetricCoordinates
import Burnett.Geometry.FlatRigidity.WeakCurvature

/-! Pull the smooth receiving base phase back to the tested compact
interior, keeping a smooth cutoff in the larger transport window. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set Burnett.Fourier Burnett.Geometry ConnectionDifference
open Burnett.Geometry.MaximalChart (AtlasChart)
open scoped ContDiff InnerProduct Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- A prescribed smooth receiving test pulls back exactly on the compact
input window, and can be localized inside a larger transport window. -/
theorem exists_receivingBaseMode_pullback (c d : AtlasChart M)
    (K S : Set E) (hK : IsCompact K) (hKS : K ⊆ interior S)
    (hSU : S ⊆ (c.transition d).source) (b : BoundedSymbol E)
    (hb : ContDiff ℝ ∞ (b : E → ℂ)) :
    ∃ a : BoundedSymbol E, ContDiff ℝ ∞ (a : E → ℂ) ∧ tsupport (a : E → ℂ) ⊆ S ∧
      a.bound = b.bound ∧ ∀ x ∈ K, a x = b (c.transition d x) := by
  obtain ⟨L, _, _, hL, χ, hχ, _, hSupp, hRange, hOne⟩ :=
    FlatRigidity.exists_smooth_cutoff_on_compact_chart hK isOpen_interior hKS
  let e := c.transition d
  let a (x : E) := (χ x : ℂ) * b (e x)
  have hBase : tsupport (fun x => (χ x : ℂ)) ⊆ tsupport χ := by
    apply closure_mono
    intro x hx h
    apply hx
    change (χ x : ℂ) = 0
    rw [h, Complex.ofReal_zero]
  have hS : tsupport a ⊆ S := tsupport_mul_subset_left.trans
    (hBase.trans (hSupp.trans (hL.trans interior_subset)))
  have hLocal : ContDiffOn ℝ ∞ a e.source :=
    (Complex.ofRealCLM.contDiff.comp hχ).contDiffOn.mul (hb.comp_contDiffOn (c.smooth_transition d))
  have hSmooth : ContDiff ℝ ∞ a := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ e.source
    · exact hLocal.contDiffAt (e.open_source.mem_nhds hx)
    · exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℂ)) x).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hSU (hS h))))
  let ψ : BoundedSymbol E :=
    ⟨a, hSmooth.continuous.measurable.aestronglyMeasurable, b.bound, b.bound_nonneg, fun x => by
      change ‖(χ x : ℂ) * b (e x)‖ ≤ b.bound
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hRange x).1]
      exact (mul_le_mul_of_nonneg_left (b.norm_le _) (hRange x).1).trans
        (mul_le_of_le_one_left b.bound_nonneg (hRange x).2)⟩
  refine ⟨ψ, hSmooth, hS, rfl, fun x hx => ?_⟩
  change (χ x : ℂ) * b (e x) = b (e x)
  rw [hOne x hx, Complex.ofReal_one, one_mul]

/-- All spatial Fourier waves used in the joint-symbol extension are smooth. -/
theorem contDiff_baseFourierPhaseSymbol (k : E) :
    ContDiff ℝ ∞ (baseFourierPhaseSymbol k : E → ℂ) := by
  have hin : ContDiff ℝ ∞ (fun x : E => inner ℝ k x) := (innerSL ℝ k).contDiff
  have h : ContDiff ℝ ∞ (fun x : E => (2 * Real.pi * inner ℝ k x : ℝ)) := contDiff_const.mul hin
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp h).mul contDiff_const)

end Burnett.Microlocal.Overlap
