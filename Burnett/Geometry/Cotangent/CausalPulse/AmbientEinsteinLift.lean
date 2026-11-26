import Burnett.Analysis.Microlocal.Overlap.CosphereEinsteinMoments
import Burnett.Geometry.Causality.IntrinsicRegularPiecewiseCausality
import Burnett.Geometry.Cotangent.CausalPulse.ActualPulseMomentumLift
import Burnett.Geometry.Cotangent.CausalPulse.CompleteNullTimeFromCausality
import Burnett.Geometry.Cotangent.CosphereNullInclusion
import Burnett.Geometry.Cotangent.TensorPhaseTests

set_option autoImplicit false
set_option maxHeartbeats 5400000

noncomputable section
namespace Burnett.Geometry.CausalOrbitPulse

open Set MeasureTheory
open scoped ContDiff ENNReal Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.ActualTestLift
open Burnett.Geometry.FiniteCausalVolume
open Burnett.Geometry.ContravariantTensor Burnett.Geometry.IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian)
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] puncturedMeasurable puncturedBorel unitNullMeasurable unitNullBorel

/-- The paper's original cosphere transport equation for smooth, positively
one-homogeneous tests with compact support in the base. -/
def HasCosphereHamiltonTransport (r : Metric (M := M)) (g : Field (M := M))
    (μ : Measure (Cosphere r)) : Prop :=
  ∀ a : CotangentBundle M → ℝ,
    ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent →
    (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p) →
    (∃ K : Set M, IsCompact K ∧ ∀ p ∈ puncturedCotangent, p.proj ∉ K → a p = 0) →
    (∫ p : Cosphere r, actualHamiltonDerivative g a p.val ∂μ) = 0

/-- The full cotangent equations and local second moments on the original manifold. -/
def HasFullMomentumEinsteinEquations (r : Metric (M := M)) (g : Field (M := M))
    (hn : IsNondegenerate g) (μ : Measure (Cosphere r))
    (ν : Measure (puncturedCotangent (M := M))) : Prop :=
  ν.Regular ∧ ν {p | dualEnergy g hn p.val ≠ 0} = 0 ∧
    (∀ K : Set M, IsCompact K →
      let Q := {p : puncturedCotangent (M := M) | p.val.proj ∈ K}
      let V := (projection (r := r)) ⁻¹' K
      (∫⁻ p : puncturedCotangent (M := M),
        ENNReal.ofReal (Q.indicator (fun q : puncturedCotangent (M := M) => (cotangentNorm r q.val)^2) p)
        ∂ν) = μ V ∧ μ V < (⊤ : ℝ≥0∞)) ∧
    (∀ Q : ContravariantTwoTensor M, IsTensorTest Q →
      Integrable (einsteinPair g hn Q) (ManifoldVolume.geometricMeasure g) ∧
      Integrable (fun p : puncturedCotangent (M := M) => intrinsicTensorPhase Q p.val) ν ∧
      (∫ x, einsteinPair g hn Q x ∂ManifoldVolume.geometricMeasure g) =
        ∫ p : puncturedCotangent (M := M), intrinsicTensorPhase Q p.val ∂ν) ∧
    ∀ b : CotangentBundle M → ℝ,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ b puncturedCotangent →
      HasCompactSupport (fun p : puncturedCotangent (M := M) => b p.val) →
      Integrable (fun p : puncturedCotangent (M := M) => actualHamiltonDerivative g b p.val) ν ∧
      (∫ p : puncturedCotangent (M := M), actualHamiltonDerivative g b p.val ∂ν) = 0

private theorem exists_fullMomentumEinsteinLift_of_chartGlobalHyperbolicity
    (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g) (hL : HasLorentzSignature g)
    (o : TimeOrientation g) (hGH : ChartGlobalHyperbolicity o)
    (μ : Measure (Cosphere r)) [IsLocallyFiniteMeasure μ]
    (hNull : μ {p | hamiltonian g hL.isNondegenerate p ≠ 0} = 0)
    (hMom : HasCosphereEinsteinMoments r g hL.isNondegenerate μ)
    (hTransport : HasCosphereHamiltonTransport r g μ) :
    ∃ ν : Measure (puncturedCotangent (M := M)),
      HasFullMomentumEinsteinEquations r g hL.isNondegenerate μ ν := by
  let hn := hL.isNondegenerate
  let hs := hL.isSymmetric
  let μN := unitNullMeasureOfCosphere r g hn μ
  letI : IsLocallyFiniteMeasure μN := unitNullMeasureOfCosphere_locallyFinite r g hg hn hs μ
  have ht : HasActualUnitTransport r g hn μN := by
    apply unitNullMeasureOfCosphere_hasActualUnitTransport r g hg hn hs μ hNull
    intro a ha hhom hSupp
    obtain ⟨K, hK, hKS⟩ := hSupp
    exact hTransport a ha hhom ⟨K, hK, fun p _ hp =>
      image_eq_zero_of_notMem_tsupport (fun hP => hp (hKS hP))⟩
  obtain ⟨T, hTc, hT⟩ := exists_completeNullTime_of_chartGlobalHyperbolicity g hg hL o hGH
  obtain ⟨s, hpos, _, hReg, hNullν, hLocal, hQuadratic, hFullTransport⟩ :=
    exists_actualFullMomentumLift_of_completeNullTime r g hg hn hs T hTc hT μN ht
  let ν := actualWeightedLift r g hn s hpos μN
  let e := unitNullIntoCosphere r g hn
  have hE := (unitNullIntoCosphere_isClosedEmbedding r g hg hn hs).measurableEmbedding
  have hMap : μN.map e = μ := unitNullMeasureOfCosphere_map r g hg hn hs μ hNull
  refine ⟨ν, hReg, hNullν, ?_, ?_, hFullTransport⟩
  · intro K hK
    have hKμ : μ ((projection (r := r)) ⁻¹' K) = μN {p | p.val.proj ∈ K} := by
      rw [← hMap, hE.map_apply]
      rfl
    dsimp only
    rw [hKμ]
    exact hLocal K hK
  · intro Q hQ
    obtain ⟨hiBase, hiPhase, hEq⟩ := hMom Q hQ
    have hMeas : Measurable (fun p : puncturedCotangent (M := M) => intrinsicTensorPhase Q p.val) :=
      ((contMDiff_intrinsicTensorPhase Q hQ.2.2).continuous.comp continuous_subtype_val).measurable
    obtain ⟨hiFull, hFull⟩ := hQuadratic (intrinsicTensorPhase Q) hMeas
      (fun p _ a _ => intrinsicTensorPhase_cotangentScale Q p a)
    have hCosphereI := hE.integrable_map_iff (μ := μN) (g := fun p : Cosphere r => intrinsicTensorPhase Q p.val)
    have hCosphere := hE.integral_map (μ := μN) (fun p : Cosphere r => intrinsicTensorPhase Q p.val)
    rw [hMap] at hCosphereI hCosphere
    exact ⟨hiBase, hiFull.mpr (hCosphereI.mp hiPhase), hEq.trans (hFull.trans hCosphere.symm).symm⟩

/-- The local-moment lift of the original transported Einstein cosphere
measure for intrinsic global hyperbolicity with the closed future cone. -/
theorem exists_fullMomentumEinsteinLift_of_intrinsicPiecewise
    (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g) (hL : HasLorentzSignature g)
    (o : TimeOrientation g)
    (hDiam : ∀ a b : M, IsCompact {z : M | (a, z) ∈ intrinsicPiecewiseCausalRelation o ∧
      (z, b) ∈ intrinsicPiecewiseCausalRelation o})
    (hStrong : LocallyNoCausalReturn (intrinsicPiecewiseCausalRelation o))
    (μ : Measure (Cosphere r)) [IsLocallyFiniteMeasure μ]
    (hNull : μ {p | hamiltonian g hL.isNondegenerate p ≠ 0} = 0)
    (hMom : HasCosphereEinsteinMoments r g hL.isNondegenerate μ)
    (hTransport : HasCosphereHamiltonTransport r g μ) :
    ∃ ν : Measure (puncturedCotangent (M := M)),
      HasFullMomentumEinsteinEquations r g hL.isNondegenerate μ ν :=
  exists_fullMomentumEinsteinLift_of_chartGlobalHyperbolicity r g hg hL o
    ((chartGlobalHyperbolicity_iff_intrinsicPiecewise hg hL o).2 ⟨hDiam, hStrong⟩) μ hNull hMom hTransport

/-- The same ambient lift for the convention of regular piecewise `C¹`
causal curves with nonzero one-sided velocities. -/
theorem exists_fullMomentumEinsteinLift_of_regularIntrinsicPiecewise
    (r : Metric (M := M)) (g : Field (M := M)) (hg : IsSmooth g) (hL : HasLorentzSignature g)
    (o : TimeOrientation g)
    (hDiam : ∀ a b : M, IsCompact {z : M | (a, z) ∈ regularIntrinsicPiecewiseCausalRelation o ∧
      (z, b) ∈ regularIntrinsicPiecewiseCausalRelation o})
    (hStrong : LocallyNoCausalReturn (regularIntrinsicPiecewiseCausalRelation o))
    (μ : Measure (Cosphere r)) [IsLocallyFiniteMeasure μ]
    (hNull : μ {p | hamiltonian g hL.isNondegenerate p ≠ 0} = 0)
    (hMom : HasCosphereEinsteinMoments r g hL.isNondegenerate μ)
    (hTransport : HasCosphereHamiltonTransport r g μ) :
    ∃ ν : Measure (puncturedCotangent (M := M)),
      HasFullMomentumEinsteinEquations r g hL.isNondegenerate μ ν :=
  exists_fullMomentumEinsteinLift_of_chartGlobalHyperbolicity r g hg hL o
    (chartGlobalHyperbolicity_of_regularIntrinsicPiecewise hg hL o hDiam hStrong) μ hNull hMom hTransport

end Burnett.Geometry.CausalOrbitPulse
