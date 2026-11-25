import Burnett.Geometry.Cotangent.OpenRegion.EinsteinMoments
import Burnett.Geometry.Cotangent.OpenRegion.Transport
import Burnett.Geometry.Cotangent.CausalPulse.ActualPulseMomentumLift

set_option autoImplicit false
set_option maxHeartbeats 5400000
set_option maxRecDepth 3900

noncomputable section

namespace Burnett.Geometry.OpenRegion

open Set MeasureTheory
open TopologicalSpace (Opens)
open scoped ContDiff ENNReal Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.ActualTestLift
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CausalOrbitPulse
open Burnett.Geometry.ContravariantTensor Burnett.Geometry.IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian)
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] puncturedMeasurable puncturedBorel unitNullMeasurable unitNullBorel

/-- Full null cotangent equations and the exact local second-moment identity
with the given cosphere measure of the open subspacetime. -/
def HasLiftedRegionEinsteinEquations (U : Opens M) (r : Metric (M := M))
    (g : Field (M := M)) (hL : HasLorentzSignature g) (μ : Measure (Cosphere r))
    (ν : Measure (puncturedCotangent (M := U))) : Prop :=
    let rU := restrictRiemannian U r
    let gU := restrictBilinear U g
    let hnU : IsNondegenerate gU := fun p => hL.isNondegenerate p.val
    ν.Regular ∧ ν {p | dualEnergy gU hnU p.val ≠ 0} = 0 ∧
      (∀ K : Set U, IsCompact K →
        let Q := {p : puncturedCotangent (M := U) | p.val.1 ∈ K}
        let V := (projection (r := rU)) ⁻¹' K
        (∫⁻ p : puncturedCotangent (M := U),
          ENNReal.ofReal (Q.indicator (fun q : puncturedCotangent (M := U) => (cotangentNorm rU q.val)^2) p)
          ∂ν) = (cosphereMeasureOfOpen U r μ) V ∧ (cosphereMeasureOfOpen U r μ) V < (⊤ : ℝ≥0∞)) ∧
      (∀ Q : ContravariantTwoTensor U, IsTensorTest Q →
        Integrable (einsteinPair gU hnU Q) (ManifoldVolume.geometricMeasure gU) ∧
        Integrable (fun p : puncturedCotangent (M := U) => intrinsicTensorPhase Q p.val) ν ∧
        (∫ x, einsteinPair gU hnU Q x ∂ManifoldVolume.geometricMeasure gU) =
          ∫ p : puncturedCotangent (M := U), intrinsicTensorPhase Q p.val ∂ν) ∧
      ∀ b : CotangentBundle U → ℝ,
        ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ b puncturedCotangent →
        HasCompactSupport (fun p : puncturedCotangent (M := U) => b p.val) →
        Integrable (fun p : puncturedCotangent (M := U) => actualHamiltonDerivative gU b p.val) ν ∧
        (∫ p : puncturedCotangent (M := U), actualHamiltonDerivative gU b p.val ∂ν) = 0

/-- A continuous complete time on the null orbits of the open region lifts
the restriction of the same ambient transported Einstein measure. -/
theorem exists_openRegionEinsteinLift_of_completeNullTime (U : Opens M) (r : Metric (M := M))
    (g : Field (M := M)) (hg : IsSmooth g) (hL : HasLorentzSignature g)
    (T : U → ℝ) (hTc : Continuous T)
    (hT : HasCompleteNullTime T (restrictBilinear U g) (isSmooth_restrictBilinear U g hg)
      (hasLorentzSignature_restrictBilinear U hL).isNondegenerate
      (hasLorentzSignature_restrictBilinear U hL).isSymmetric)
    (μ : Measure (Cosphere r)) [IsLocallyFiniteMeasure μ]
    (hNull : μ {p | hamiltonian g hL.isNondegenerate p ≠ 0} = 0)
    (hMom : HasCosphereEinsteinMoments r g hL.isNondegenerate μ)
    (hTransport : ∀ a : CotangentBundle M → ℝ,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent →
      (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p) →
      (∃ K : Set M, IsCompact K ∧ tsupport a ⊆ (fun p => p.1) ⁻¹' K) →
      (∫ p : Cosphere r, actualHamiltonDerivative g a p.val ∂μ) = 0) :
    ∃ ν : Measure (puncturedCotangent (M := U)), HasLiftedRegionEinsteinEquations U r g hL μ ν := by
  let rU := restrictRiemannian U r
  let gU := restrictBilinear U g
  let hLU := hasLorentzSignature_restrictBilinear U hL
  let hnU := hLU.isNondegenerate
  let hsU := hLU.isSymmetric
  let ρ := cosphereMeasureOfOpen U r μ
  let μU := unitNullMeasureOfCosphere rU gU hnU ρ
  have hgU := isSmooth_restrictBilinear U g hg
  obtain ⟨htU, hFin, _⟩ := unitNullMeasureOfOpen_transport U r g hg hL.isNondegenerate hL.isSymmetric μ hNull hTransport
  letI : IsLocallyFiniteMeasure μU := hFin
  obtain ⟨s, hpos, _, hReg, hNullν, hLocal, hQuadratic, hFullTransport⟩ :=
    exists_actualFullMomentumLift_of_completeNullTime rU gU hgU hnU hsU T hTc hT μU htU
  let ν := actualWeightedLift rU gU hnU s hpos μU
  let e := unitNullIntoCosphere rU gU hnU
  have hE := (unitNullIntoCosphere_isClosedEmbedding rU gU hgU hnU hsU).measurableEmbedding
  have hMap : μU.map e = ρ :=
    unitNullMeasureOfCosphere_map rU gU hgU hnU hsU ρ
      (cosphereMeasureOfOpen_offNull U r g hL.isNondegenerate hL.isSymmetric μ hNull)
  have hMomU := hasCosphereEinsteinMoments_openSubtype U r g hg hL.isNondegenerate hL.isSymmetric μ hMom
  refine ⟨ν, hReg, hNullν, ?_, ?_, hFullTransport⟩
  · intro K hK
    have hKμ : ρ ((projection (r := rU)) ⁻¹' K) = μU {p | p.val.1 ∈ K} := by
      rw [← hMap, hE.map_apply]
      rfl
    dsimp only
    rw [hKμ]
    exact hLocal K hK
  · intro Q hQ
    obtain ⟨hiBase, hiPhase, hEq⟩ := hMomU Q hQ
    have hMeas : Measurable (fun p : puncturedCotangent (M := U) => intrinsicTensorPhase Q p.val) :=
      ((contMDiff_intrinsicTensorPhase Q hQ.2.2).continuous.comp continuous_subtype_val).measurable
    obtain ⟨hiFull, hFull⟩ := hQuadratic (intrinsicTensorPhase Q) hMeas
      (fun p _ a _ => intrinsicTensorPhase_cotangentScale Q p a)
    have hCosphereI := hE.integrable_map_iff (μ := μU) (g := fun p : Cosphere rU => intrinsicTensorPhase Q p.val)
    have hCosphere := hE.integral_map (μ := μU) (fun p : Cosphere rU => intrinsicTensorPhase Q p.val)
    rw [hMap] at hCosphereI hCosphere
    exact ⟨hiBase, hiFull.mpr (hCosphereI.mp hiPhase), hEq.trans (hFull.trans hCosphere.symm).symm⟩

end Burnett.Geometry.OpenRegion
