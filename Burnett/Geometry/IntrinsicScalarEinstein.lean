import Burnett.Geometry.ContravariantTensor

/-! The actual inverse metric, scalar curvature and Einstein tensor in preferred charts. -/

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.IntrinsicScalarEinstein

open Bundle Set Module Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricTransition
open BackgroundConnection ContravariantTensor IntrinsicRicciTrace UnitNullCompactness
open Burnett.Geometry.CurvatureDifference (coordinateRicci)
open Burnett.Geometry.InverseField (matrixInverse)
open scoped BigOperators ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

def covariantForm (B : Field (M := M)) (x : M) : LinearMap.BilinForm ℝ (TangentSpace Model x) :=
  LinearMap.mk₂ ℝ (fun u v => B x u v)
    (by intros; simp [map_add]) (by intros; simp [map_smul])
    (by intros; simp [map_add]) (by intros; simp [map_smul])

private theorem covariantForm_inChart (B : Field (M := M)) (c x : M)
    (hx : x ∈ (chartAt CoordinateSpace c).source) :
    FiberMetric.covariant (covariantForm B x) (tensorTangentBasis c x hx) =
      metricComponents (coordinateBilinear B c) (chartAt CoordinateSpace c x) := by
  funext i j
  rw [metricComponents, FiberMetric.covariant, coordinateBilinear, (chartAt CoordinateSpace c).left_inv hx]
  simp [tensorTangentBasis_apply, frameBilinear, covariantForm]
  rfl

/-- The actual inverse metric, applied to two covectors in the same fiber. -/
def inverseMetricTensor (B : Field (M := M)) (hn : IsNondegenerate B) : ContravariantTwoTensor M :=
  fun x =>
    let sharp := FiberMetric.sharp (covariantForm B x) (hn x)
      (tensorTangentBasis x x (mem_chart_source CoordinateSpace x))
    (covariantForm B x).compl₁₂ sharp.toLinearMap sharp.toLinearMap

theorem inverseMetricTensor_isSymmetric (B : Field (M := M)) (hn : IsNondegenerate B)
    (hs : IsSymmetric B) (x : M) : (inverseMetricTensor B hn x).IsSymm := by
  constructor
  intro ξ η
  exact hs x _ _

theorem inverseMetricTensor_components (B : Field (M := M)) (hn : IsNondegenerate B) (hs : IsSymmetric B)
    (c x : M) (hx : x ∈ (chartAt CoordinateSpace c).source) (i j : Index) :
    contravariantComponents (inverseMetricTensor B hn) c (chartAt CoordinateSpace c x) i j =
      matrixInverse (metricComponents (coordinateBilinear B c) (chartAt CoordinateSpace c x)) i j := by
  let b := tensorTangentBasis c x hx
  let g := covariantForm B x
  have hcov : FiberMetric.covariant g b = metricComponents (coordinateBilinear B c) (chartAt CoordinateSpace c x) :=
    covariantForm_inChart B c x hx
  rw [contravariantComponents_chart (inverseMetricTensor B hn) c x hx,
    ← hcov, InverseField.matrixInverse_covariant g (hn x) (⟨hs x⟩ : g.IsSymm) b]
  change g _ _ = g _ _
  simp only [LinearMap.BilinForm.dualBasis, Basis.map_apply, FiberMetric.sharp]
  rfl

theorem intrinsicTensorPhase_inverseMetric (B : Field (M := M)) (hn : IsNondegenerate B)
    (hs : IsSymmetric B) (p : CotangentBundle M) :
    intrinsicTensorPhase (inverseMetricTensor B hn) p = dualEnergy B hn p := by
  have hp : p.proj ∈ (chartAt CoordinateSpace p.proj).source := mem_chart_source CoordinateSpace p.proj
  rw [intrinsicTensorPhase_eq_components _ p.proj p hp, dualEnergy_chart B hn hs p.proj p hp]
  simp only [inverseMetricTensor_components B hn hs p.proj p.proj hp, symbolNorm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def intrinsicScalar (B : Field (M := M)) (hn : IsNondegenerate B) (x : M) : ℝ :=
  intrinsicTensorBase B (inverseMetricTensor B hn) x

/-- Ricci minus half the scalar curvature times the actual background metric. -/
def intrinsicEinstein (B : Field (M := M)) (hn : IsNondegenerate B) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace Model x) :=
  ricciBilinearForm B x - (intrinsicScalar B hn x / 2) • covariantForm B x

def einsteinPair (B : Field (M := M)) (hn : IsNondegenerate B) (Q : ContravariantTwoTensor M) (x : M) : ℝ :=
  contractAt x (Q x) (intrinsicEinstein B hn x)

theorem intrinsicEinstein_eq_ricci_of_scalar_zero (B : Field (M := M))
    (hn : IsNondegenerate B) (x : M) (hzero : intrinsicScalar B hn x = 0) :
    intrinsicEinstein B hn x = ricciBilinearForm B x := by
  ext u v
  change ricciBilinearForm B x u v - (intrinsicScalar B hn x / 2) * covariantForm B x u v =
    ricciBilinearForm B x u v
  rw [hzero, zero_div, zero_mul, sub_zero]

theorem einsteinPair_eq_intrinsicTensorBase_of_scalar_zero (B : Field (M := M))
    (hn : IsNondegenerate B) (Q : ContravariantTwoTensor M) (x : M)
    (hzero : intrinsicScalar B hn x = 0) :
    einsteinPair B hn Q x = intrinsicTensorBase B Q x := by
  rw [einsteinPair, intrinsicEinstein_eq_ricci_of_scalar_zero B hn x hzero, intrinsicTensorBase]

def chartScalarCurvature (B : Field (M := M)) (c : M) (y : CoordinateSpace) : ℝ :=
  metricTrace (matrixInverse (metricComponents (coordinateBilinear B c) y))
    (coordinateRicci (computedConnection (coordinateBilinear B c)) y)

def chartEinstein (B : Field (M := M)) (c : M) (y : CoordinateSpace) : Tensor2 :=
  fun i j => coordinateRicci (computedConnection (coordinateBilinear B c)) y i j -
    (chartScalarCurvature B c y / 2) * metricComponents (coordinateBilinear B c) y i j

theorem intrinsicScalar_chart [T2Space M] (B : Field (M := M)) (hB : IsSmooth B)
    (hs : IsSymmetric B) (hn : IsNondegenerate B) (c x : M)
    (hx : x ∈ (chartAt CoordinateSpace c).source) :
    intrinsicScalar B hn x = chartScalarCurvature B c (chartAt CoordinateSpace c x) := by
  rw [intrinsicScalar, intrinsicTensorBase_eq_components B hB hs hn _ c x hx]
  simp only [inverseMetricTensor_components B hn hs c x hx]
  rfl

theorem intrinsicEinstein_components [T2Space M] (B : Field (M := M)) (hB : IsSmooth B)
    (hs : IsSymmetric B) (hn : IsNondegenerate B) (c x : M)
    (hx : x ∈ (chartAt CoordinateSpace c).source) (i j : Index) :
    intrinsicEinstein B hn x (tensorTangentBasis c x hx i) (tensorTangentBasis c x hx j) =
      chartEinstein B c (chartAt CoordinateSpace c x) i j := by
  let b := tensorTangentBasis c x hx
  have hRicci : ricciBilinearForm B x (b i) (b j) =
      coordinateRicci (computedConnection (coordinateBilinear B c)) (chartAt CoordinateSpace c x) i j := by
    change ricci B x (tensorTangentBasis c x hx i) (tensorTangentBasis c x hx j) = _
    rw [tensorTangentBasis_apply, tensorTangentBasis_apply,
      show coordinateBasis i = EuclideanSpace.single i 1 from EuclideanSpace.basisFun_apply _ _ i,
      show coordinateBasis j = EuclideanSpace.single j 1 from EuclideanSpace.basisFun_apply _ _ j,
      ricci_coordinate_basis B hB hs hn c x hx]
  have hMetric : covariantForm B x (b i) (b j) =
      metricComponents (coordinateBilinear B c) (chartAt CoordinateSpace c x) i j :=
    congrFun (congrFun (covariantForm_inChart B c x hx) i) j
  change ricciBilinearForm B x (b i) (b j) - (intrinsicScalar B hn x / 2) *
    covariantForm B x (b i) (b j) = _
  rw [hRicci, intrinsicScalar_chart B hB hs hn c x hx, hMetric]
  rfl

theorem einsteinPair_eq_components [T2Space M] (B : Field (M := M)) (hB : IsSmooth B)
    (hs : IsSymmetric B) (hn : IsNondegenerate B) (Q : ContravariantTwoTensor M) (c x : M)
    (hx : x ∈ (chartAt CoordinateSpace c).source) :
    einsteinPair B hn Q x = ∑ i, ∑ j,
      contravariantComponents Q c (chartAt CoordinateSpace c x) i j *
        chartEinstein B c (chartAt CoordinateSpace c x) i j := by
  rw [einsteinPair, contractAt_eq_sum x (tensorTangentBasis c x hx)]
  simp only [← contravariantComponents_chart Q c x hx, intrinsicEinstein_components B hB hs hn c x hx]

end Burnett.Geometry.IntrinsicScalarEinstein
