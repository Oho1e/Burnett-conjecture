import Burnett.Analysis.GaugeProjection.StrongCompactness.ReceivingPhysicalMeasureZero

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 4800000

noncomputable section

namespace Burnett.P01

open Set Filter MeasureTheory Matrix Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian)
open Burnett.Geometry.UnitNullCompactness (CotangentBundle dualEnergy)
open Burnett.Geometry.IntrinsicScalarEinstein (covariantForm)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase measurable_fixedChartPhase_comp)
open Burnett.F07.IntrinsicAmplitude (intrinsicPhysicalWeight)
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity
open Burnett.X02.SobolevTestJet (D test_smooth)
open scoped ComplexOrder ContDiff ENNReal Manifold Matrix MatrixOrder

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The part of the original auxiliary cosphere in the receiving chart
over the exact level set where the localization equals one. -/
def receivingProjectionPlateau {r : Metric (M := M)} (c : AtlasChart M) (χ : D) : Set (Cosphere r) :=
  (projection ⁻¹' c.chart.source) ∩ {p | (χ : E → ℝ) (fixedChartPhase c p.val).1 = 1}

omit [T2Space M] [SecondCountableTopology M] in
theorem measurableSet_receivingProjectionPlateau {r : Metric (M := M)} (c : AtlasChart M) (χ : D) :
    MeasurableSet (receivingProjectionPlateau (r := r) c χ) := by
  apply ((UnitCosphere.continuous_projection r).measurable c.chart.open_source.measurableSet).inter
  have hx := (measurable_fixedChartPhase_comp (Subtype.val : Cosphere r → CotangentBundle M)
    continuous_subtype_val c).fst
  exact measurableSet_eq_fun ((test_smooth χ).continuous.measurable.comp hx) measurable_const

/-- On the plateau, the two-slot projected covariance is positive,
vanishes off the null cone, and satisfies the exact Lorenz contraction
on the cone. Its quarter contraction is the same original measure. -/
def HasReceivingProjectedPhysicalDefect
    (r : Metric (M := M)) (B : Field (M := M)) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ : D) (A : IntrinsicAmplitudeCovariance r) (μ : Measure (Cosphere r)) : Prop :=
  let W := receivingProjectionPlateau (r := r) c χ
  let Q := receivingProjectedAmplitudeCovariance c A.density
  let G (p : Cosphere r) := receivingBackgroundInverse B c (projection p)
  (∀ᵐ p ∂A.control.restrict W,
    (Q p).PosSemidef ∧ (hamiltonian B hn p ≠ 0 → Q p = 0) ∧
    (hamiltonian B hn p = 0 → ∀ (v : OrderedPair → ℂ) (b : Index),
      let H := tensorOfVector ((Q p) *ᵥ v)
      let ξ := atlasChartUnitCovector c p
      IsSymmetricComplexTensor H ∧ complexContracted (G p) ξ H b =
        complexMetricTrace (G p) H * ((ξ b / 2 : ℝ) : ℂ))) ∧
  μ.restrict W = ((A.control.restrict {p | hamiltonian B hn p = 0}).restrict W).withDensity
    (fun p => ENNReal.ofReal (quarterDensity G (fun _ => (1 : Matrix OrderedPair OrderedPair ℂ)) Q p))

omit [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
private theorem receivingInverse_symmetric {r : Metric (M := M)} (B : Field (M := M))
    (hSig : HasLorentzSignature B) (c : AtlasChart M) (p : Cosphere r)
    (hp : projection p ∈ c.chart.source) :
    IsSymmetricTensor (receivingBackgroundInverse B c (projection p)) := by
  let x := projection p
  let b := chartTangentBasis c x hp
  rw [receivingBackgroundInverse_in_fiber B c hSig.isSymmetric hSig.isNondegenerate x hp]
  exact FiberMetric.contravariant_symmetric (covariantForm B x) (hSig.isNondegenerate x)
    (⟨hSig.isSymmetric x⟩ : (covariantForm B x).IsSymm) b

omit [T2Space M] [SecondCountableTopology M] in
/-- Read the actual projected covariance on the same F07 measure and chart
plateau, preserving the exact angular scalar density. -/
theorem hasReceivingProjectedPhysicalDefect_of_originalIntrinsicAmplitude
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r) (μ : Measure (Cosphere r))
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hμ : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ)
    (c : AtlasChart M) (χ : D) :
    HasReceivingProjectedPhysicalDefect r B hSig.isNondegenerate c χ A μ := by
  unfold HasReceivingProjectedPhysicalDefect
  intro W Q G
  have hW : MeasurableSet W := measurableSet_receivingProjectionPlateau c χ
  have hWin : ∀ᵐ p ∂A.control.restrict W, p ∈ W := ae_restrict_mem hW
  have hData := ae_restrict_of_ae (s := W) hA.2.2.2.2.2
  let Z : Set (Cosphere r) := {p | hamiltonian B hSig.isNondegenerate p = 0}
  have hNull (p : Cosphere r) (hc : projection p ∈ c.chart.source) (hz : p ∈ Z) :
      symbolNorm (G p) (atlasChartUnitCovector c p) = 0 := by
    have hh : dualEnergy B hSig.isNondegenerate p.val / 2 = 0 := hz
    rw [show G p = receivingBackgroundInverse B c (projection p) from rfl,
      receivingSymbolNorm_eq_dualEnergy B c hSig.isSymmetric hSig.isNondegenerate p hc]
    exact (div_eq_zero_iff.mp hh).resolve_right (by norm_num)
  refine ⟨?_, ?_⟩
  · filter_upwards [hData, hWin] with p hD hp
    have hc : projection p ∈ c.chart.source := hp.1
    have hpos : (atlasAmplitudeMatrix c A.density p).PosSemidef := by
      rw [atlasAmplitudeMatrix_of_mem c A.density p hc]
      exact hD.2.1 (chartTangentBasis c (projection p) hc)
    refine ⟨hpos.mul_mul_conjTranspose_same _, ?_, ?_⟩
    · exact fun ho => receivingProjectedAmplitudeCovariance_eq_zero_off_null B c hSig A.density p hc ho hD.2.2
    · intro hn v b
      exact projectedCoordinateCovariance_null_contracted (G p) (WithLp.toLp 2 (atlasChartUnitCovector c p))
        (atlasAmplitudeMatrix c A.density p) (receivingInverse_symmetric B hSig c p hc)
        (atlasChartUnitCovector_ne_zero c p hc) (hNull p hc hn)
        (atlasAmplitudeMatrix_receiving_ricciKernel B c hSig.isSymmetric hSig.isNondegenerate A.density p hc hD.2.2)
        v b
  · obtain ⟨hZ, _, _, hμEq⟩ := hμ
    change μ = (A.control.restrict Z).withDensity
      (fun p => ENNReal.ofReal (intrinsicPhysicalWeight B hSig.isNondegenerate A.density p)) at hμEq
    rw [hμEq, restrict_withDensity hW]
    apply withDensity_congr_ae
    have hZWin : ∀ᵐ p ∂(A.control.restrict Z).restrict W, p ∈ Z :=
      ae_restrict_of_ae (ae_restrict_mem hZ)
    filter_upwards [ae_restrict_mem (μ := A.control.restrict Z) hW, hZWin,
      ae_restrict_of_ae (ae_restrict_of_ae hA.2.2.2.2.2)] with p hp hzp hD
    have hc : projection p ∈ c.chart.source := hp.1
    obtain ⟨_, hξ, hPos, hK⟩ := receivingNullDensityData_of_intrinsic B c hSig A.density p hc hD.2.1 hD.2.2
    have he := projectedCoordinateCovariance_physicalContraction_eq
      (G p) (WithLp.toLp 2 (atlasChartUnitCovector c p)) (1 : Matrix OrderedPair OrderedPair ℂ)
      (receivingInverse_symmetric B hSig c p hc) hξ (hNull p hc hzp) hPos hK
    simp only [coordinateCovariance, Matrix.conjTranspose_one, one_mul, mul_one] at he
    congr 1
    rw [← receivingQuarterDensity_eq_intrinsicPhysicalWeight B c hSig.isSymmetric hSig.isNondegenerate A.density p hc]
    simp only [quarterDensity, coordinateCovariance, Q,
      Matrix.conjTranspose_one, one_mul, mul_one, he, G]

end Burnett.P01
