import Burnett.Geometry.Causality.IntrinsicRegularPiecewiseCausality
import Burnett.Geometry.Cotangent.OpenRegion.GloballyHyperbolicLift

set_option autoImplicit false

noncomputable section
namespace Burnett.Geometry.OpenRegion

open Set MeasureTheory
open TopologicalSpace (Opens)
open scoped ContDiff Manifold Topology
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open CotangentAngularExtension ActualTestLift FiniteCausalVolume
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian)
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] puncturedMeasurable puncturedBorel

/-- Compact diamonds and strong causality for intrinsic piecewise `C¹` curves
give the full open-region lift of the same ambient Einstein measure. -/
theorem exists_openRegionEinsteinLift_of_intrinsicPiecewise (U : Opens M)
    (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g) (hL : HasLorentzSignature g)
    (o : TimeOrientation (restrictBilinear U g))
    (hDiam : ∀ a b : U, IsCompact {z : U | (a, z) ∈ intrinsicPiecewiseCausalRelation o ∧
      (z, b) ∈ intrinsicPiecewiseCausalRelation o})
    (hStrong : LocallyNoCausalReturn (intrinsicPiecewiseCausalRelation o))
    (μ : Measure (Cosphere r)) [IsLocallyFiniteMeasure μ]
    (hNull : μ {p | hamiltonian g hL.isNondegenerate p ≠ 0} = 0)
    (hMom : HasCosphereEinsteinMoments r g hL.isNondegenerate μ)
    (hTransport : ∀ a : CotangentBundle M → ℝ,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent →
      (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p) →
      (∃ K : Set M, IsCompact K ∧ tsupport a ⊆ (fun p => p.1) ⁻¹' K) →
      (∫ p : Cosphere r, actualHamiltonDerivative g a p.val ∂μ) = 0) :
    ∃ ν : Measure (puncturedCotangent (M := U)), HasLiftedRegionEinsteinEquations U r g hL μ ν := by
  have hGH := (chartGlobalHyperbolicity_iff_intrinsicPiecewise
    (isSmooth_restrictBilinear U g hg) (hasLorentzSignature_restrictBilinear U hL) o).2 ⟨hDiam, hStrong⟩
  exact exists_openRegionEinsteinLift_of_chartGlobalHyperbolicity U r g hg hL o hGH μ hNull hMom hTransport

/-- The regular convention for piecewise `C¹` causal curves supplies the same
full open-region lift from its compact diamonds and strong causality. -/
theorem exists_openRegionEinsteinLift_of_regularIntrinsicPiecewise (U : Opens M)
    (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g) (hL : HasLorentzSignature g)
    (o : TimeOrientation (restrictBilinear U g))
    (hDiam : ∀ a b : U, IsCompact {z : U | (a, z) ∈ regularIntrinsicPiecewiseCausalRelation o ∧
      (z, b) ∈ regularIntrinsicPiecewiseCausalRelation o})
    (hStrong : LocallyNoCausalReturn (regularIntrinsicPiecewiseCausalRelation o))
    (μ : Measure (Cosphere r)) [IsLocallyFiniteMeasure μ]
    (hNull : μ {p | hamiltonian g hL.isNondegenerate p ≠ 0} = 0)
    (hMom : HasCosphereEinsteinMoments r g hL.isNondegenerate μ)
    (hTransport : ∀ a : CotangentBundle M → ℝ,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent →
      (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p) →
      (∃ K : Set M, IsCompact K ∧ tsupport a ⊆ (fun p => p.1) ⁻¹' K) →
      (∫ p : Cosphere r, actualHamiltonDerivative g a p.val ∂μ) = 0) :
    ∃ ν : Measure (puncturedCotangent (M := U)), HasLiftedRegionEinsteinEquations U r g hL μ ν := by
  have hGH := chartGlobalHyperbolicity_of_regularIntrinsicPiecewise
    (isSmooth_restrictBilinear U g hg) (hasLorentzSignature_restrictBilinear U hL) o hDiam hStrong
  exact exists_openRegionEinsteinLift_of_chartGlobalHyperbolicity U r g hg hL o hGH μ hNull hMom hTransport

end Burnett.Geometry.OpenRegion
