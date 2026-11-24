import Burnett.Analysis.Microlocal.Overlap.AtlasAngularPhaseEncoding
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! The intrinsic jet covariance tensor obtained by inserting the covector in both slots. -/

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1100000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set Matrix Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric MaximalChart
open UnitCosphere (Cosphere projection)
open FixedCotangentChart (fixedCovector)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeTensor AmplitudeCovarianceDensity
  chartTangentBasis chartTangentBasis_apply components components_apply)
open Burnett.Microlocal.CurlDensity (JetSlot gradientEmbedding gradient_factor_entry)
open scoped ComplexOrder ContDiff Manifold Matrix

/-- The two derivative slots and the four amplitude slots are actual tangent
arguments in the same real vector space. -/
abbrev JetAmplitudeTensor (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  MultilinearMap ℝ (fun _ : Fin 2 ⊕ Fin 4 => V) ℂ

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The covector is inserted into each derivative slot of one covariance. -/
def insertJetCovectors (ξ : V →ₗ[ℝ] ℝ) (A : AmplitudeTensor V) : JetAmplitudeTensor V :=
  (((MultilinearMap.mkPiRing ℝ (Fin 2) (1 : ℝ)).compLinearMap fun _ => ξ).smulRight A).uncurrySum

theorem insertJetCovectors_apply (ξ : V →ₗ[ℝ] ℝ) (A : AmplitudeTensor V)
    (v : Fin 2 ⊕ Fin 4 → V) :
    insertJetCovectors ξ A v =
      (ξ (v (.inl 0)) * ξ (v (.inl 1))) • A (fun i => v (.inr i)) := by
  simp only [insertJetCovectors, MultilinearMap.uncurrySum_apply, MultilinearMap.smulRight_apply,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply, Fin.prod_univ_two,
    smul_eq_mul, mul_one, MultilinearMap.smul_apply]

/-- Ordered components evaluate both derivative slots and both tensor pairs
on actual vectors of one basis in the tangent fiber. -/
def jetAmplitudeComponents (b : Module.Basis Index ℝ V) (J : JetAmplitudeTensor V) :
    Matrix JetSlot JetSlot ℂ :=
  fun i j => J (Sum.elim ![b i.1, b j.1] ![b i.2.1, b i.2.2, b j.2.1, b j.2.2])

theorem jetAmplitudeComponents_insertJetCovectors (b : Module.Basis Index ℝ V)
    (ξ : V →ₗ[ℝ] ℝ) (A : AmplitudeTensor V) :
    let E := gradientEmbedding (fun i => ξ (b i))
    jetAmplitudeComponents b (insertJetCovectors ξ A) = E * components b A * Eᴴ := by
  intro E
  ext i j
  rw [jetAmplitudeComponents, insertJetCovectors_apply, gradient_factor_entry, components_apply]
  change ((ξ (b i.1) * ξ (b j.1)) : ℝ) • A ![b i.2.1, b i.2.2, b j.2.1, b j.2.2] = _
  simp only [Complex.real_smul, Complex.ofReal_mul]

theorem jetAmplitudeComponents_posSemidef (b : Module.Basis Index ℝ V)
    (ξ : V →ₗ[ℝ] ℝ) (A : AmplitudeTensor V) (h : (components b A).PosSemidef) :
    (jetAmplitudeComponents b (insertJetCovectors ξ A)).PosSemidef := by
  rw [jetAmplitudeComponents_insertJetCovectors]
  exact h.mul_mul_conjTranspose_same _

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The global jet density at the same auxiliary unit covector, defined on
the actual tangent fiber with both derivatives from that covector. -/
def intrinsicJetAmplitude {r : Metric (M := M)} (A : AmplitudeCovarianceDensity r) (p : Cosphere r) :
    JetAmplitudeTensor (TangentSpace Model (projection p)) :=
  insertJetCovectors p.val.2.toLinearMap (A p)

/-- The receiving-chart jet entries are those of this same global tensor.
The order of the two matrix indices matches the second-linear pairing. -/
theorem atlasOrderedJetEntry_eq_intrinsicJetComponents {r : Metric (M := M)}
    (c : AtlasChart M) (A : AmplitudeCovarianceDensity r) (p : Cosphere r)
    (hp : projection p ∈ c.chart.source) (i j : JetSlot) :
    atlasOrderedJetEntry c A p i j =
      jetAmplitudeComponents (chartTangentBasis c (projection p) hp) (intrinsicJetAmplitude A p) j i := by
  let b := chartTangentBasis c (projection p) hp
  have hCoords (k : Index) : atlasChartUnitCovector c p k = p.val.2 (b k) := by
    rw [atlasChartUnitCovector_of_mem c p hp k, chartTangentBasis_apply]
    rfl
  rw [atlasOrderedJetEntry, atlasAmplitudeMatrix_of_mem c A p hp, intrinsicJetAmplitude,
    jetAmplitudeComponents_insertJetCovectors, gradient_factor_entry, hCoords, hCoords]
  change (p.val.2 (b i.1) : ℂ) * (p.val.2 (b j.1) : ℂ) * components b (A p) j.2 i.2 =
    (p.val.2 (b j.1) : ℂ) * (p.val.2 (b i.1) : ℂ) * components b (A p) j.2 i.2
  ring

end Burnett.Microlocal.Overlap
