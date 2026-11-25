import Burnett.Geometry.ChartVectorField
import Burnett.Geometry.ContravariantTensor
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

/-! Compact smooth contravariant tests made from the actual tangent frame of one chart. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 2700000

noncomputable section
namespace Burnett.F08.IntrinsicBaseMarginal

open Set Module Bundle Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric IntrinsicRicciTrace ContravariantTensor
open scoped ContDiff Manifold

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The symmetric dyad, evaluated on two actual algebraic covectors. -/
def symmetricTangentDyad (u v : V) : LinearMap.BilinForm ℝ (Dual ℝ V) :=
  LinearMap.mk₂ ℝ (fun η ζ => (η u * ζ v + η v * ζ u) / 2)
    (by intros; simp only [LinearMap.add_apply]; ring)
    (by intros; simp only [LinearMap.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [LinearMap.add_apply]; ring)
    (by intros; simp only [LinearMap.smul_apply, smul_eq_mul]; ring)

theorem symmetricTangentDyad_apply (u v : V) (η ζ : Dual ℝ V) :
    symmetricTangentDyad u v η ζ = (η u * ζ v + η v * ζ u) / 2 := rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def supportedFrameVector (c : M) (φ : M → ℝ) (i : Index) (x : M) : TangentSpace Model x :=
  φ x • tangentFrame c x (coordinateBasis i)

theorem isSmooth_supportedFrameVector (c : M) (φ : M → ℝ) (i : Index)
    (hφ : ContMDiff Model 𝓘(ℝ) ∞ φ) (hSupport : tsupport φ ⊆ (chartAt CoordinateSpace c).source) :
    ChartVectorField.IsSmooth (supportedFrameVector c φ i) := by
  exact hφ.contMDiffOn.smul_section_of_tsupport (chartAt CoordinateSpace c).open_source hSupport
    (ManifoldMetric.contMDiffOn_frame c (coordinateBasis i))

private theorem coordinateCovectorBasis_eval_frame (W : ChartVectorField.Field (M := M))
    (c x : M) (hx : x ∈ (chartAt CoordinateSpace c).source) (i : Index) :
    coordinateCovectorBasis c x i (W x) = ChartVectorField.frameVector W c x i := by
  rw [coordinateCovectorBasis_eq_dualBasis c x hx, Basis.dualBasis_apply]
  rw [tensorTangentBasis, Basis.map_repr]
  exact EuclideanSpace.basisFun_repr Index ℝ (ChartVectorField.frameVector W c x) i

/-- A chart-frame test built from the same fixed compact scalar window in both slots. -/
def supportedFrameTensorTest (c : M) (φ : M → ℝ) (i j : Index) : ContravariantTwoTensor M :=
  fun x => symmetricTangentDyad (supportedFrameVector c φ i x) (supportedFrameVector c φ j x)

theorem isTensorTest_supportedFrameTensorTest (c : M) (φ : M → ℝ) (i j : Index)
    (hφ : ContMDiff Model 𝓘(ℝ) ∞ φ) (hC : HasCompactSupport φ)
    (hSupport : tsupport φ ⊆ (chartAt CoordinateSpace c).source) :
    IsTensorTest (supportedFrameTensorTest c φ i j) := by
  let U := supportedFrameVector c φ i
  let W := supportedFrameVector c φ j
  refine ⟨fun x => ⟨fun a b => ?_⟩, ?_, ?_⟩
  · simp only [supportedFrameTensorTest, symmetricTangentDyad_apply]
    ring
  · apply hC.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro x hx
    change φ x ≠ 0
    intro hz
    apply hx
    ext a b
    simp only [supportedFrameTensorTest, supportedFrameVector, hz, zero_smul, symmetricTangentDyad_apply,
      map_zero, mul_zero, add_zero, zero_div, LinearMap.zero_apply]
  · intro d a b
    let e := chartAt CoordinateSpace d
    have hu := ChartVectorField.contDiffOn_coordinateVector U (isSmooth_supportedFrameVector c φ i hφ hSupport) d
    have hw := ChartVectorField.contDiffOn_coordinateVector W (isSmooth_supportedFrameVector c φ j hφ hSupport) d
    have hU (k : Index) : ContDiffOn ℝ ∞ (fun y => ChartVectorField.coordinateVector U d y k) e.target :=
      (EuclideanSpace.proj k : CoordinateSpace →L[ℝ] ℝ).contDiff.comp_contDiffOn hu
    have hW (k : Index) : ContDiffOn ℝ ∞ (fun y => ChartVectorField.coordinateVector W d y k) e.target :=
      (EuclideanSpace.proj k : CoordinateSpace →L[ℝ] ℝ).contDiff.comp_contDiffOn hw
    refine (((hU a).mul (hW b)).add ((hW a).mul (hU b))).div_const 2 |>.congr (fun y hy => ?_)
    let x := e.symm y
    have hx : x ∈ e.source := e.symm_mapsTo hy
    change symmetricTangentDyad (U x) (W x) (coordinateCovectorBasis d x a) (coordinateCovectorBasis d x b) = _
    rw [symmetricTangentDyad_apply, coordinateCovectorBasis_eval_frame U d x hx a,
      coordinateCovectorBasis_eval_frame W d x hx b, coordinateCovectorBasis_eval_frame W d x hx a,
      coordinateCovectorBasis_eval_frame U d x hx b]
    rfl

theorem supportedFrameTensorTest_eq_at_plateau (c x : M) (φ : M → ℝ) (i j : Index)
    (hx : x ∈ (chartAt CoordinateSpace c).source) (hφ : φ x = 1) :
    supportedFrameTensorTest c φ i j x =
      symmetricTangentDyad (tensorTangentBasis c x hx i) (tensorTangentBasis c x hx j) := by
  rw [supportedFrameTensorTest, supportedFrameVector, supportedFrameVector, hφ, one_smul, one_smul,
    tensorTangentBasis_apply, tensorTangentBasis_apply]

end Burnett.F08.IntrinsicBaseMarginal
