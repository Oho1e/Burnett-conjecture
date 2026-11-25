import Burnett.Analysis.GaugeProjection.StrongCompactness.PaperChartNorms
import Burnett.Analysis.GaugeProjection.StrongCompactness.ReceivingCovariantL2

/-! Vacuum limits and strong physical compactness for the original admissible sequence. -/

set_option autoImplicit false
noncomputable section

namespace Burnett.P01

open Filter MeasureTheory Set Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F08.IntrinsicBaseMarginal (auxiliaryEinsteinDensity_baseMarginal physicalMeasure_zero_over_vacuumOpen)
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeCovariantGradientSchwartz_tendsto_zero_of_intrinsicL2)
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The unprojected covariant derivative tends strongly to zero on each compact subset
with its original geometric volume. -/
def HasStrongIntrinsicDhOn (r : Metric (M := M)) (B : Field (M := M))
    (g : ℕ → Field (M := M)) (U : Set M) : Prop :=
  ∀ K : Set M, IsCompact K → K ⊆ U →
    Tendsto (fun n => eLpNorm (IntrinsicDhMeasure.normScalar r (fun x => g n x - B x)) 2
      ((ManifoldVolume.geometricMeasure B).restrict K)) atTop (𝓝 0)

/-- Local strong convergence in the geometric volume controls all receiving covariant cutoffs. -/
theorem hasStrongOriginalCovariantGradientOn_of_strongIntrinsicDh (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (U : Set M) (hStrong : HasStrongIntrinsicDhOn r B g U) :
    HasStrongOriginalCovariantGradientOn r B g hB hg hn U := by
  intro c χ hχ hχU i
  apply fixedVolumeCovariantGradientSchwartz_tendsto_zero_of_intrinsicL2 r B g hB hg hn U _ c χ hχ hχU i
  intro K hK hKU
  simpa only [Function.comp_apply, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hStrong K hK hKU)

/-- On every open region, pointwise vacuum is equivalent to full-sequence strong convergence
of the homogeneous projected weak derivative on all compatible charts and cutoffs.
Unprojected geometric local strong convergence implies vacuum and vanishing of the given
quadratic measure on that region. -/
theorem vacuumOpen_strongCompactness
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (U : Set M) (hU : IsOpen U) :
    ((∀ x ∈ U, ∀ u v : TangentSpace Model x, IntrinsicRicciTrace.ricci B x u v = 0) ↔
      ∀ (c : AtlasChart M), c.chart.source ⊆ U → ∀ (χ : D)
        (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart.target),
        Tendsto (fun n => Real.sqrt (receivingStrongProjectionEnergy B g hB hg c χ hχ n)) atTop (𝓝 0)) ∧
    (HasStrongIntrinsicDhOn r B g U →
      (∀ x ∈ U, ∀ u v : TangentSpace Model x, IntrinsicRicciTrace.ricci B x u v = 0) ∧
      ∀ μ : Measure (Cosphere r),
        (∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) →
        HasCosphereEinsteinMoments r B hSig.isNondegenerate μ →
        (∀ x, IntrinsicScalarEinstein.intrinsicScalar B hSig.isNondegenerate x = 0) →
        μ.restrict (projection ⁻¹' U) = 0) := by
  refine ⟨vacuumOpen_iff_all_charts_homogeneousProjectedGradient_norm_tendsto_zero
    r B g hB hg hSig hsG hnG hconv hb hv U hU, fun hRaw => ?_⟩
  have hStrong := hasStrongOriginalCovariantGradientOn_of_strongIntrinsicDh r B g hB hg hSig.isNondegenerate U hRaw
  have hProjected := hasStrongProjectedGradientOn_of_strongOriginalCovariantGradient
    r B g hB hg hSig.isNondegenerate hconv U hStrong
  have hRic := (vacuumOpen_iff_hasStrongProjectedGradientOn r B g hB hg hSig hsG hnG hconv hb hv U hU).mpr hProjected
  refine ⟨hRic, fun μ hFin hMom hScal => ?_⟩
  have hMarg := auxiliaryEinsteinDensity_baseMarginal r B hB hSig.isSymmetric hSig.isNondegenerate μ hFin hMom
  exact Measure.restrict_eq_zero.mpr
    (physicalMeasure_zero_over_vacuumOpen r B hSig.isNondegenerate μ hMarg hScal U hU hRic)

end Burnett.P01
