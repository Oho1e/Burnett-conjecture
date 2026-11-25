import Burnett.Analysis.GaugeProjection.StrongCompactness.ReceivingPhysicalCovariance

/-! Vanishing of the same physical measure in an arbitrary receiving chart. -/

set_option autoImplicit false
set_option maxRecDepth 4900
set_option maxHeartbeats 4400000

noncomputable section
namespace Burnett.P01

open Set MeasureTheory Filter Module Matrix Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open UnitCosphere (Cosphere projection hamiltonian)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity components)
open Burnett.F07.IntrinsicAmplitude (intrinsicPhysicalWeight)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity
open Burnett.A02.FrequencySplit (E)
open scoped ComplexOrder ContDiff Manifold Matrix MatrixOrder ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The original amplitude matrix compressed by the Euclidean gauge-complement projection of this chart. -/
abbrev receivingProjectedAmplitudeCovariance {r : Metric (M := M)} (c : AtlasChart M)
    (J : AmplitudeCovarianceDensity r) (p : Cosphere r) : Matrix OrderedPair OrderedPair ℂ :=
  coordinateCovariance (principalGaugeProjectionMatrix (WithLp.toLp 2 (atlasChartUnitCovector c p)))
    (atlasAmplitudeMatrix c J p)

private theorem receivingNullSymbol_iff {r : Metric (M := M)} (B : Field (M := M)) (c : AtlasChart M)
    (hSig : HasLorentzSignature B) (p : Cosphere r) (hp : projection p ∈ c.chart.source) :
    symbolNorm (receivingBackgroundInverse B c (projection p)) (atlasChartUnitCovector c p) = 0 ↔
      hamiltonian B hSig.isNondegenerate p = 0 := by
  rw [receivingSymbolNorm_eq_dualEnergy B c hSig.isSymmetric hSig.isNondegenerate p hp, hamiltonian,
    div_eq_iff (by norm_num : (2 : ℝ) ≠ 0), zero_mul]

/-- Pointwise on the null shell, zero density detects exactly zero projected covariance in the receiving chart. -/
theorem receivingProjectedAmplitudeCovariance_eq_zero_iff_intrinsicPhysicalWeight_eq_zero
    {r : Metric (M := M)} (B : Field (M := M)) (c : AtlasChart M) (hSig : HasLorentzSignature B)
    (J : AmplitudeCovarianceDensity r) (p : Cosphere r) (hp : projection p ∈ c.chart.source)
    (hNull : hamiltonian B hSig.isNondegenerate p = 0)
    (hPos : ∀ b : Basis Index ℝ (TangentSpace Model (projection p)), (components b (J p)).PosSemidef)
    (hk : HasIntrinsicAmplitudeRicciKernel r B hSig.isNondegenerate J p) :
    receivingProjectedAmplitudeCovariance c J p = 0 ↔ intrinsicPhysicalWeight B hSig.isNondegenerate J p = 0 := by
  obtain ⟨⟨frame⟩, hξ, hC, hK⟩ := receivingNullDensityData_of_intrinsic B c hSig J p hp hPos hk
  have h := physicalContraction_re_eq_zero_iff_projectedCovariance_eq_zero
    (receivingBackgroundInverse B c (projection p)) frame (WithLp.toLp 2 (atlasChartUnitCovector c p))
    (1 : Matrix OrderedPair OrderedPair ℂ) hC hξ ((receivingNullSymbol_iff B c hSig p hp).mpr hNull) hK
  rw [← receivingQuarterDensity_eq_intrinsicPhysicalWeight B c hSig.isSymmetric hSig.isNondegenerate J p hp,
    quarterDensity, div_eq_iff (by norm_num : (4 : ℝ) ≠ 0), zero_mul]
  simpa only [receivingProjectedAmplitudeCovariance, Matrix.mul_one] using h.symm

/-- The same projection annihilates the original covariance off the null shell. -/
theorem receivingProjectedAmplitudeCovariance_eq_zero_off_null
    {r : Metric (M := M)} (B : Field (M := M)) (c : AtlasChart M) (hSig : HasLorentzSignature B)
    (J : AmplitudeCovarianceDensity r) (p : Cosphere r) (hp : projection p ∈ c.chart.source)
    (hOff : hamiltonian B hSig.isNondegenerate p ≠ 0)
    (hk : HasIntrinsicAmplitudeRicciKernel r B hSig.isNondegenerate J p) :
    receivingProjectedAmplitudeCovariance c J p = 0 :=
  projectedCoordinateCovariance_eq_zero_off_null (receivingBackgroundInverse B c (projection p))
    (WithLp.toLp 2 (atlasChartUnitCovector c p)) (atlasAmplitudeMatrix c J p)
    (atlasChartUnitCovector_ne_zero c p hp) (fun h => hOff ((receivingNullSymbol_iff B c hSig p hp).mp h))
    (fun v => (atlasAmplitudeMatrix_receiving_ricciKernel B c hSig.isSymmetric hSig.isNondegenerate J p hp hk v).2)

/-- On any measurable window of a compatible chart, the original physical measure vanishes exactly when
the original projected amplitude covariance vanishes almost everywhere for the original trace there. -/
theorem intrinsicPhysicalMeasure_restrict_eq_zero_iff_receivingProjectedAmplitudeCovariance_ae_eq_zero
    {r : Metric (M := M)} {B : Field (M := M)} {g : ℕ → Field (M := M)}
    {hB : IsSmooth B} {hg : ∀ n, IsSmooth (g n)} {σ : ℕ → ℕ} (hSig : HasLorentzSignature B)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (μ : Measure (Cosphere r)) (hPhysical : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ)
    (c : AtlasChart M) (W : Set (Cosphere r)) (hW : MeasurableSet W)
    (hWc : W ⊆ projection ⁻¹' c.chart.source) :
    μ.restrict W = 0 ↔ ∀ᵐ p ∂A.control.restrict W, receivingProjectedAmplitudeCovariance c A.density p = 0 := by
  let Z : Set (Cosphere r) := {p | hamiltonian B hSig.isNondegenerate p = 0}
  let w := intrinsicPhysicalWeight B hSig.isNondegenerate A.density
  let τW := A.control.restrict W
  obtain ⟨hZ, hMeas, hNonneg, hμ⟩ := hPhysical
  change MeasurableSet Z at hZ
  change AEMeasurable w (A.control.restrict Z) at hMeas
  change (∀ᵐ p ∂A.control.restrict Z, 0 ≤ w p) at hNonneg
  change μ = (A.control.restrict Z).withDensity (fun p => ENNReal.ofReal (w p)) at hμ
  have hOrder : (τW.restrict Z) = (A.control.restrict Z).restrict W :=
    Measure.restrict_comm hZ
  have hM : AEMeasurable (fun p => ENNReal.ofReal (w p)) (τW.restrict Z) := by
    rw [hOrder]
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable hMeas.restrict
  have hPosW : ∀ᵐ p ∂τW.restrict Z, 0 ≤ w p := by
    rw [hOrder]
    exact ae_restrict_of_ae hNonneg
  have hMass : μ W = ∫⁻ p, ENNReal.ofReal (w p) ∂(τW.restrict Z) := by
    rw [hμ, withDensity_apply _ hW, hOrder]
  rw [Measure.restrict_eq_zero, hMass, lintegral_eq_zero_iff' hM]
  have hData := ae_restrict_of_ae (s := W) hA.2.2.2.2.2
  have hMem := ae_restrict_mem (μ := A.control) hW
  constructor
  · intro hZero
    filter_upwards [hData, hMem, (ae_restrict_iff' hZ).mp hZero, (ae_restrict_iff' hZ).mp hPosW]
      with p hD hp h0 hPos
    have hc := hWc hp
    by_cases hz : p ∈ Z
    · have he : w p = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp (h0 hz)) (hPos hz)
      exact (receivingProjectedAmplitudeCovariance_eq_zero_iff_intrinsicPhysicalWeight_eq_zero
        B c hSig A.density p hc hz hD.2.1 hD.2.2).mpr he
    · exact receivingProjectedAmplitudeCovariance_eq_zero_off_null B c hSig A.density p hc hz hD.2.2
  · intro hProj
    apply (ae_restrict_iff' hZ).mpr
    filter_upwards [hData, hMem, hProj] with p hD hp hP hZp
    have h0 := (receivingProjectedAmplitudeCovariance_eq_zero_iff_intrinsicPhysicalWeight_eq_zero
      B c hSig A.density p (hWc hp) hZp hD.2.1 hD.2.2).mp hP
    change ENNReal.ofReal (w p) = 0
    rw [show w p = 0 from h0, ENNReal.ofReal_zero]

end Burnett.P01
