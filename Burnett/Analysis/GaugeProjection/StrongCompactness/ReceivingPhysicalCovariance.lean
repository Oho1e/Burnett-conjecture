import Burnett.Analysis.GaugeProjection.StrongCompactness.ProjectedMeasureZero
import Burnett.Analysis.Microlocal.Overlap.OriginalVacuumIntrinsicAmplitude
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartJetMeasureBridge

/-! The physical contraction and projection in the actual receiving-chart basis. -/

set_option autoImplicit false
set_option maxRecDepth 4900
set_option maxHeartbeats 4200000

noncomputable section
namespace Burnett.P01

open Set MeasureTheory Filter Module Matrix Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open UnitNullCompactness (dualEnergy dualEnergy_in_basis)
open UnitCosphere (Cosphere projection hamiltonian)
open IntrinsicScalarEinstein (covariantForm inverseMetricTensor)
open InverseField (matrixInverse matrixInverse_covariant)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity chartTangentBasis
  chartTangentBasis_apply chartComponents components components_apply)
open Burnett.F07.IntrinsicAmplitude (intrinsicPhysicalWeight intrinsicPhysicalWeight_eq_basis quarterContractionInBasis)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.CurlDensity (ricciJetLinear ricciJetLinear_apply ricciJetSymbol_gradient gradientEmbedding)
open Burnett.Microlocal.PhysicalDensity
open Burnett.A02.FrequencySplit (E)
open Burnett.Geometry.FixedCotangentChart (inverseFrame)
open scoped ComplexOrder ContDiff Manifold Matrix MatrixOrder ENNReal

open private physicalCoefficient_mul_re from Burnett.Analysis.Microlocal.Overlap.ChartAmplitudeContractions

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The inverse background metric in a fixed receiving chart. -/
def receivingBackgroundInverse (B : Field (M := M)) (c : AtlasChart M) (x : M) : Tensor2 :=
  matrixInverse (metricComponents (fixedForm B c) (c.chart x))

private theorem fixedForm_components_in_chartTangentBasis (B : Field (M := M)) (c : AtlasChart M)
    (x : M) (hx : x ∈ c.chart.source) :
    metricComponents (fixedForm B c) (c.chart x) = FiberMetric.covariant (covariantForm B x) (chartTangentBasis c x hx) := by
  funext i j
  simp only [metricComponents, FiberMetric.covariant, chartTangentBasis_apply, covariantForm,
    fixedForm, LinearMap.mk₂_apply, fixedCoordinateBilinear, inverseFrame]
  exact congrArg (fun y => B y
    (mfderiv Model Model c.chart.symm (c.chart x) (coordinateBasis i))
    (mfderiv Model Model c.chart.symm (c.chart x) (coordinateBasis j))) (c.chart.left_inv hx)

theorem receivingBackgroundInverse_in_fiber (B : Field (M := M)) (c : AtlasChart M)
    (hs : IsSymmetric B) (hn : IsNondegenerate B) (x : M) (hx : x ∈ c.chart.source) :
    receivingBackgroundInverse B c x = FiberMetric.contravariant (covariantForm B x) (hn x) (chartTangentBasis c x hx) := by
  unfold receivingBackgroundInverse
  rw [fixedForm_components_in_chartTangentBasis B c x hx,
    matrixInverse_covariant (covariantForm B x) (hn x) (⟨hs x⟩ : (covariantForm B x).IsSymm)]

theorem atlasChartUnitCovector_in_fiber {r : Metric (M := M)} (c : AtlasChart M) (p : Cosphere r)
    (hp : projection p ∈ c.chart.source) :
    atlasChartUnitCovector c p = FiberMetric.covector (chartTangentBasis c (projection p) hp) p.val.2.toLinearMap := by
  funext i
  rw [atlasChartUnitCovector_of_mem c p hp i, FiberMetric.covector, chartTangentBasis_apply]
  rfl

theorem receivingSymbolNorm_eq_dualEnergy {r : Metric (M := M)} (B : Field (M := M)) (c : AtlasChart M)
    (hs : IsSymmetric B) (hn : IsNondegenerate B) (p : Cosphere r) (hp : projection p ∈ c.chart.source) :
    symbolNorm (receivingBackgroundInverse B c (projection p)) (atlasChartUnitCovector c p) = dualEnergy B hn p.val := by
  rw [dualEnergy_in_basis B hn hs p.val (chartTangentBasis c (projection p) hp),
    atlasChartUnitCovector_in_fiber c p hp, receivingBackgroundInverse, fixedForm_components_in_chartTangentBasis B c _ hp]
  rfl

/-- The full complex column span belongs to the symmetric Ricci kernel in the actual receiving chart. -/
theorem atlasAmplitudeMatrix_receiving_ricciKernel {r : Metric (M := M)} (B : Field (M := M)) (c : AtlasChart M)
    (hs : IsSymmetric B) (hn : IsNondegenerate B) (J : AmplitudeCovarianceDensity r)
    (p : Cosphere r) (hp : projection p ∈ c.chart.source)
    (hk : HasIntrinsicAmplitudeRicciKernel r B hn J p) (v : OrderedPair → ℂ) :
    let G := receivingBackgroundInverse B c (projection p)
    let ξ := atlasChartUnitCovector c p
    let k := tensorOfVector (atlasAmplitudeMatrix c J p *ᵥ v)
    IsSymmetricComplexTensor k ∧ ∀ i j, complexRicciSymbol G ξ k i j = 0 := by
  intro G ξ k
  let x := projection p
  let b := chartTangentBasis c x hp
  let g := covariantForm B x
  let η := p.val.2.toLinearMap
  let C := atlasAmplitudeMatrix c J p
  let Eξ := gradientEmbedding ξ
  let L := (ricciJetLinear G ξ).comp (Matrix.mulVecLin Eξ)
  letI : FiniteDimensional ℝ (TangentSpace Model x) := Module.Finite.of_basis b
  have hG : IsSymmetricTensor G := by
    change IsSymmetricTensor (receivingBackgroundInverse B c x)
    rw [receivingBackgroundInverse_in_fiber B c hs hn x hp]
    exact FiberMetric.contravariant_symmetric g (hn x) (⟨hs x⟩ : g.IsSymm) b
  have hC : C = components b (J p) := atlasAmplitudeMatrix_of_mem c J p hp
  have hColumn (q : OrderedPair) :
      IsSymmetricComplexTensor (tensorOfVector (C.col q)) ∧
      ∀ i j, complexRicciSymbol G ξ (tensorOfVector (C.col q)) i j = 0 := by
    let S := amplitudeSlice (J p) (b q.1) (b q.2)
    have hEntry : tensorOfVector (C.col q) = fun i j => S (b i) (b j) := by
      funext i j
      change C (i, j) q = _
      rw [hC, components_apply]
      rfl
    obtain ⟨hSymm, hRicci⟩ := hk (b q.1) (b q.2)
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [hEntry]
      exact hSymm (b i) (b j)
    · rw [hEntry, show G = FiberMetric.contravariant g (hn x) b from
        receivingBackgroundInverse_in_fiber B c hs hn x hp,
        show ξ = FiberMetric.covector b η from atlasChartUnitCovector_in_fiber c p hp,
        ← complexFiberRicciSymbol_eq_basis g (hn x) η S b]
      change complexFiberRicciSymbol g (hn x) η S = 0 at hRicci
      rw [hRicci]
      rfl
  have hSymm : IsSymmetricComplexTensor k := by
    intro i j
    change (∑ q, C (i, j) q * v q) = ∑ q, C (j, i) q * v q
    exact Finset.sum_congr rfl (fun q _ => congrArg (· * v q) ((hColumn q).1 i j))
  have hImage : C *ᵥ v = ∑ q : OrderedPair, v q • C.col q := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, mul_comm]
  have hL (q : OrderedPair) : L (C.col q) = 0 := by
    funext s
    change ricciJetLinear G ξ (Eξ *ᵥ C.col q) s = 0
    rw [ricciJetLinear_apply, ricciJetSymbol_gradient G ξ _ hG (hColumn q).1]
    exact (hColumn q).2 s.1 s.2
  have hLv : L (C *ᵥ v) = 0 := by
    rw [hImage, map_sum]
    simp only [map_smul, hL, smul_zero, Finset.sum_const_zero]
  refine ⟨hSymm, fun i j => ?_⟩
  have hz := congrFun hLv (i, j)
  change ricciJetLinear G ξ (Eξ *ᵥ (C *ᵥ v)) (i, j) = 0 at hz
  rw [ricciJetLinear_apply, ricciJetSymbol_gradient G ξ _ hG hSymm] at hz
  exact hz

theorem receivingQuarterDensity_eq_intrinsicPhysicalWeight {r : Metric (M := M)}
    (B : Field (M := M)) (c : AtlasChart M) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (J : AmplitudeCovarianceDensity r) (p : Cosphere r) (hp : projection p ∈ c.chart.source) :
    quarterDensity (fun q => receivingBackgroundInverse B c (projection q))
      (fun _ => (1 : Matrix OrderedPair OrderedPair ℂ)) (atlasAmplitudeMatrix c J) p = intrinsicPhysicalWeight B hn J p := by
  let x := projection p
  let b := chartTangentBasis c x hp
  letI : FiniteDimensional ℝ (TangentSpace Model x) := Module.Finite.of_basis b
  have hG (i j : Index) :
      inverseMetricTensor B hn x (b.dualBasis i) (b.dualBasis j) = receivingBackgroundInverse B c x i j := by
    change fiberInverseForm (covariantForm B x) (hn x) (b.dualBasis i) (b.dualBasis j) = _
    rw [fiberInverseForm_eq_contravariant (covariantForm B x) (hn x) b]
    exact congrFun (congrFun (receivingBackgroundInverse_in_fiber B c hs hn x hp).symm i) j
  rw [intrinsicPhysicalWeight_eq_basis B hn J p b, quarterDensity, atlasAmplitudeMatrix_of_mem c J p hp]
  simp only [coordinateCovariance, Matrix.conjTranspose_one, one_mul, mul_one,
    quarterContractionInBasis, physicalContraction, Complex.re_sum, Fintype.sum_prod_type,
    physicalCoefficient_mul_re, chartComponents, components_apply, hG, b, x]

theorem receivingNullDensityData_of_intrinsic {r : Metric (M := M)} (B : Field (M := M)) (c : AtlasChart M)
    (hSig : HasLorentzSignature B) (J : AmplitudeCovarianceDensity r) (p : Cosphere r) (hp : projection p ∈ c.chart.source)
    (hPos : ∀ b : Basis Index ℝ (TangentSpace Model (projection p)), (components b (J p)).PosSemidef)
    (hk : HasIntrinsicAmplitudeRicciKernel r B hSig.isNondegenerate J p) :
    NullDensityData (fun q => receivingBackgroundInverse B c (projection q)) (atlasChartUnitCovector c)
      (fun _ => (1 : Matrix OrderedPair OrderedPair ℂ)) (atlasAmplitudeMatrix c J) p := by
  refine ⟨?_, atlasChartUnitCovector_ne_zero c p hp, ?_, ?_⟩
  · change Nonempty (TensorFrame.LorentzFrame (receivingBackgroundInverse B c (projection p)))
    rw [receivingBackgroundInverse_in_fiber B c hSig.isSymmetric hSig.isNondegenerate _ hp]
    obtain ⟨e, he⟩ := hSig (projection p)
    exact ⟨BasisFrame.lorentzFrame (covariantForm B (projection p)) (hSig.isNondegenerate (projection p))
      (chartTangentBasis c (projection p) hp) e he⟩
  · rw [atlasAmplitudeMatrix_of_mem c J p hp]
    exact hPos (chartTangentBasis c (projection p) hp)
  · rintro _ ⟨v, rfl⟩
    simpa only [Matrix.one_mulVec] using atlasAmplitudeMatrix_receiving_ricciKernel B c
      hSig.isSymmetric hSig.isNondegenerate J p hp hk v

end Burnett.P01
