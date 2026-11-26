import Burnett.Geometry.Cotangent.TensorPhaseTests
import Burnett.Geometry.Cotangent.OpenRegion.TestExtension

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.Geometry.OpenRegion

open Set Filter Bundle
open TopologicalSpace (Opens)
open scoped BigOperators ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ContravariantTensor Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.UnitNullAngular (Phase)

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

private theorem extendCotangentTest_contMDiff [T2Space M] (U : Opens M) (a : CotangentBundle U → ℝ)
    (ha : ContMDiff CotangentModelWithCorners 𝓘(ℝ) ∞ a)
    {K : Set U} (hK : IsCompact K) (hSupp : tsupport a ⊆ (fun p => p.1) ⁻¹' K) :
    ContMDiff CotangentModelWithCorners 𝓘(ℝ) ∞ (extendCotangentTest U a) := by
  intro p
  by_cases hp : p ∈ cotangentOver U
  · let q : cotangentOverOpen U := ⟨p, hp⟩
    have hEq : (fun z : cotangentOverOpen U => extendCotangentTest U a z.val) =
        a ∘ (cotangentOpenHomeomorph U).symm := by
      funext z
      exact dif_pos z.property
    have hc := (ha.comp (contMDiff_cotangentOpenHomeomorph_inv U)).contMDiffAt (x := q)
    rw [← hEq] at hc
    exact contMDiffAt_subtype_iff.mp hc
  · have hOut : p.1 ∉ Subtype.val '' K := by
      rintro ⟨x, _, hx⟩
      exact hp (show p.1 ∈ U from hx ▸ x.property)
    have hClosed : IsClosed (Subtype.val '' K : Set M) := (hK.image continuous_subtype_val).isClosed
    have hNear : ∀ᶠ q : CotangentBundle M in 𝓝 p, q.1 ∉ (Subtype.val '' K : Set M) :=
      continuous_cotangent_projection.continuousAt.preimage_mem_nhds (hClosed.isOpen_compl.mem_nhds hOut)
    have hEq : extendCotangentTest U a =ᶠ[𝓝 p] (fun _ => 0) := hNear.mono fun q hq =>
      image_eq_zero_of_notMem_tsupport (fun hz => hq (extendCotangentTest_support U a hK hSupp hz))
    exact hEq.contMDiffAt_iff.mpr contMDiffAt_const

/-- Extend an actual contravariant test by zero outside its open base region. -/
def extendContravariantTest (U : Opens M) (Q : ContravariantTwoTensor U) : ContravariantTwoTensor M := by
  classical
  exact fun x => if h : x ∈ U then Q ⟨x, h⟩ else 0

theorem extendContravariantTest_in_region (U : Opens M) (Q : ContravariantTwoTensor U) (x : U) :
    extendContravariantTest U Q x.val = Q x := dif_pos x.property

theorem intrinsicTensorPhase_extendContravariantTest (U : Opens M) (Q : ContravariantTwoTensor U) :
    intrinsicTensorPhase (extendContravariantTest U Q) = extendCotangentTest U (intrinsicTensorPhase Q) := by
  funext p
  by_cases hp : p.1 ∈ U
  · rw [extendCotangentTest, dif_pos (show p ∈ cotangentOver U from hp)]
    change extendContravariantTest U Q p.1 p.2.toLinearMap p.2.toLinearMap = _
    rw [extendContravariantTest, dif_pos hp]
    rfl
  · rw [extendCotangentTest, dif_neg (show p ∉ cotangentOver U from hp)]
    simp only [intrinsicTensorPhase, extendContravariantTest, dif_neg hp, LinearMap.zero_apply]

private theorem covectorCLM_add (ξ η : Covector) : covectorCLM (ξ + η) = covectorCLM ξ + covectorCLM η := by
  unfold covectorCLM
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- A symmetric tensor's coordinate components are recovered smoothly by
polarizing its quadratic evaluation. -/
theorem isSmoothContravariant_of_contMDiff_tensorPhase (Q : ContravariantTwoTensor M)
    (hs : ∀ x, (Q x).IsSymm)
    (hQ : ContMDiff CotangentModelWithCorners 𝓘(ℝ) ∞ (intrinsicTensorPhase Q)) : IsSmoothContravariant Q := by
  intro c i j
  let e := chartAt E c
  let φ (ξ : Covector) (y : E) := intrinsicTensorPhase Q (cotangentChartInverse c (y, ξ))
  have hφ (ξ : Covector) : ContDiffOn ℝ ∞ (φ ξ) e.target := by
    have hL : ContMDiff Model CoordinatePhaseModel ∞ (fun y : E => (y, ξ)) := contMDiff_id.prodMk contMDiff_const
    have hI := (contMDiffOn_cotangentChartInverse c).comp hL.contMDiffOn
      (show MapsTo (fun y : E => (y, ξ)) e.target (phaseTarget c) from fun _ h => ⟨h, trivial⟩)
    exact (hQ.comp_contMDiffOn hI).contDiffOn
  let ξ : Covector := fun k => if k = i then 1 else 0
  let η : Covector := fun k => if k = j then 1 else 0
  have hPolar (y : E) (_hy : y ∈ e.target) :
      contravariantComponents Q c y i j = (φ (ξ + η) y - φ ξ y - φ η y) / 2 := by
    let x := e.symm y
    let a := coordinateCovectorBasis c x i
    let b := coordinateCovectorBasis c x j
    letI : (cotangentTrivialization c).IsLinear ℝ := by
      unfold cotangentTrivialization
      infer_instance
    let T := (cotangentTrivialization c).symmL ℝ x
    have hξ : (T (covectorCLM ξ)).toLinearMap = a := rfl
    have hη : (T (covectorCLM η)).toLinearMap = b := rfl
    have hAdd : (T (covectorCLM (ξ + η))).toLinearMap = a + b := by
      rw [covectorCLM_add, map_add]
      exact congrArg₂ (· + ·) hξ hη
    change Q x a b = (Q x (T (covectorCLM (ξ + η))).toLinearMap (T (covectorCLM (ξ + η))).toLinearMap -
      Q x (T (covectorCLM ξ)).toLinearMap (T (covectorCLM ξ)).toLinearMap -
      Q x (T (covectorCLM η)).toLinearMap (T (covectorCLM η)).toLinearMap) / 2
    rw [hAdd, hξ, hη]
    simp only [map_add, LinearMap.add_apply, (hs x).eq b a]
    ring
  exact ((((hφ (ξ + η)).sub (hφ ξ)).sub (hφ η)).div_const 2).congr hPolar

theorem extendContravariantTest_isTensorTest [T2Space M] (U : Opens M) (Q : ContravariantTwoTensor U)
    (hQ : IsTensorTest Q) : IsTensorTest (extendContravariantTest U Q) := by
  have hs (x : M) : (extendContravariantTest U Q x).IsSymm := by
    by_cases hx : x ∈ U
    · rw [extendContravariantTest, dif_pos hx]
      exact hQ.1 ⟨x, hx⟩
    · rw [extendContravariantTest, dif_neg hx]
      exact ⟨fun u v => by simp⟩
  let K := closure {x | Q x ≠ 0}
  have hK : IsCompact K := hQ.2.1
  have hK' := hK.image (continuous_subtype_val : Continuous (Subtype.val : U → M))
  have hSupp : closure {x | extendContravariantTest U Q x ≠ 0} ⊆ Subtype.val '' K := by
    apply closure_minimal _ hK'.isClosed
    intro x hx
    by_cases h : x ∈ U
    · refine ⟨⟨x, h⟩, subset_closure ?_, rfl⟩
      simpa only [mem_setOf_eq, extendContravariantTest, dif_pos h] using hx
    · exact (hx (dif_neg h)).elim
  refine ⟨hs, hK'.of_isClosed_subset isClosed_closure hSupp, isSmoothContravariant_of_contMDiff_tensorPhase _ hs ?_⟩
  rw [intrinsicTensorPhase_extendContravariantTest]
  exact extendCotangentTest_contMDiff U _ (contMDiff_intrinsicTensorPhase Q hQ.2.2) hK (intrinsicTensorPhase_tsupport Q)

end Burnett.Geometry.OpenRegion
