import Burnett.Analysis.Microlocal.Overlap.CompactLeftClassicalOperator
import Burnett.Analysis.Microlocal.Overlap.JointClassicalBilateralMixing

/-! Angular regularity used to identify classical principal symbols by modulation. -/
set_option autoImplicit false

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Burnett.Geometry.ConnectionDifference
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AtlasOverlapKernel (HasAngularPrincipalRegularity)
open scoped ContDiff Topology

local notation "E" => CoordinateSpace

/-- A compactly based smooth degree-zero symbol has all regularity needed
by the bounded modulation tests. -/
theorem hasAngularPrincipalRegularity_of_compactSmooth
    (a : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hSupport : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (hDiff : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => a x 0)) (hDegree : ∀ x, DegreeZero (a x)) :
    HasAngularPrincipalRegularity a := by
  obtain ⟨C, _, hC⟩ := exists_uniform_baseDerivative_of_homogeneousAngular a S hS hSupport hDiff hZero hDegree 0
  refine ⟨⟨C, fun x ξ => ?_⟩, (contDiff_uncurry_infraredAngularPrincipal hDiff).continuous,
    fun ξ _ => (contDiff_baseAngularSection a hDiff hZero ξ).continuous, ?_, hDegree⟩
  · simpa only [norm_iteratedFDeriv_zero] using hC x ξ
  · intro x ξ hξ
    have hξ' : ξ ∈ ({0}ᶜ : Set E) := hξ
    exact (hDiff.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hy => ⟨mem_univ _, hy⟩)).continuousAt (isOpen_compl_singleton.mem_nhds hξ')

end Burnett.Microlocal.Overlap
