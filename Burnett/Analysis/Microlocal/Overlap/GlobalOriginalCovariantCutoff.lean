import Burnett.Analysis.Microlocal.Overlap.OriginalSymmetricJetTestSections
import Burnett.Analysis.Microlocal.Overlap.ReceivingOriginalSymmetricJet
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartCovariantGradient
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! One physical compact cutoff of the intrinsic covariant jet in every receiving chart. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 6900000
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set Filter Classical Burnett.Fourier Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.AtlasVolumeGradient
  (fixedHalfDensity fixedVolumeCovariantGradientSchwartz fixedVolumeCovariantGradientSchwartz_intrinsic)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Topology

open private fixedCovariantJet_component_smoothOn
  from Burnett.Analysis.Microlocal.Overlap.ReceivingChartCovariantGradient

local notation "E" => CoordinateSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

private def curryJet {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : MultilinearMap ℝ (fun _ : Fin 3 => V) ℂ) : ComplexCovariantJet V where
  toFun v :=
    { toFun := fun u =>
        { toFun := fun w => T ![v, u, w]
          map_add' := fun w z => ((T.curryLeft v).curryLeft u).cons_add ![] w z
          map_smul' := fun b w => ((T.curryLeft v).curryLeft u).cons_smul ![] b w }
      map_add' := fun u z => by
        ext w
        exact (T.curryLeft v).cons_add ![w] u z
      map_smul' := fun b u => by
        ext w
        exact (T.curryLeft v).cons_smul ![w] b u }
  map_add' v z := by
    ext u w
    exact T.cons_add ![u, w] v z
  map_smul' b v := by
    ext u w
    exact T.cons_smul ![u, w] b v

/-- The original intrinsic real tensor, viewed as a complex symmetric jet.
Symmetry holds for the actual tensor before any coordinate projection. -/
def intrinsicSymmetricCovariantJet (r : Metric (M := M)) (H : Field (M := M))
    (hH : IsSmooth H) (hS : IsSymmetric H) (p : M) : complexSymmetricJet (TangentSpace Model p) := by
  let A := curryJet (Complex.ofRealCLM.toLinearMap.compMultilinearMap
    (IntrinsicCov2.tensor r.inner H p).toMultilinearMap)
  let c := AtlasChart.atPoint p
  have hp : p ∈ c.chart.source := mem_chart_source E p
  let b := chartTangentBasis c p hp
  refine ⟨A, mem_complexSymmetricJet_of_coordinates b A ?_⟩
  intro i j k
  change (IntrinsicCov2.tensor r.inner H p ![b i, b j, b k] : ℂ) =
    (IntrinsicCov2.tensor r.inner H p ![b i, b k, b j] : ℂ)
  rw [← fixedCovariantJet_intrinsic_components r H hH c p hp i j k,
    ← fixedCovariantJet_intrinsic_components r H hH c p hp i k j]
  exact congrArg (fun x : ℝ => (x : ℂ))
    (fixedCovariantJet_symmetric r.inner H hS c (c.chart p) i j k)

theorem intrinsicSymmetricCovariantJet_apply (r : Metric (M := M)) (H : Field (M := M))
    (hH : IsSmooth H) (hS : IsSymmetric H) (p : M)
    (v u w : TangentSpace Model p) :
    (intrinsicSymmetricCovariantJet r H hH hS p).val v u w =
      (IntrinsicCov2.tensor r.inner H p ![v, u, w] : ℂ) := rfl

/-- Smooth compact scalar multiplication of the same intrinsic jet, with no
assumption that the support fits in one chart. -/
def globalCutoffSymmetricJetTest (r : Metric (M := M)) (H : Field (M := M))
    (hH : IsSmooth H) (hS : IsSymmetric H) (β : M → ℝ)
    (hβ : ContMDiff Model 𝓘(ℝ) ∞ β) (hβc : HasCompactSupport β) : smoothCompactSymmetricJet M := by
  let s : SymmetricJetSection M := fun p => (β p : ℂ) • intrinsicSymmetricCovariantJet r H hH hS p
  refine ⟨s, ?_, ⟨tsupport β, hβc, ?_⟩⟩
  · intro c i
    have hCoef : ContDiffOn ℝ ∞ (fun y => (β (c.chart.symm y) : ℂ)) c.chart.target := by
      intro y hy
      have hh := hβ.contMDiffAt.comp y (contMDiffAt_symm_of_mem_maximalAtlas c.compatible hy)
      exact (Complex.ofRealCLM.contDiff.contDiffAt.comp y (contMDiffAt_iff_contDiffAt.mp hh)).contDiffWithinAt
    have hJet : ContDiffOn ℝ ∞ (fun y => (fixedCovariantJet r.inner H c y i.1 i.2.1 i.2.2 : ℂ))
        c.chart.target :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (fixedCovariantJet_component_smoothOn r H hH c i)
    refine (hCoef.mul hJet).congr ?_
    intro y hy
    let p := c.chart.symm y
    have hp : p ∈ c.chart.source := c.chart.symm_mapsTo hy
    have hx : c.chart p = y := c.chart.right_inv hy
    rw [symmetricJetComponent_of_mem c s i p hp]
    change jetFiberCoordinates (chartTangentBasis c p hp)
      ((β p : ℂ) • (intrinsicSymmetricCovariantJet r H hH hS p).val) i =
        (β p : ℂ) * (fixedCovariantJet r.inner H c y i.1 i.2.1 i.2.2 : ℂ)
    rw [map_smul, Pi.smul_apply, smul_eq_mul, ← hx]
    rw [jetFiberCoordinates_apply, intrinsicSymmetricCovariantJet_apply,
      fixedCovariantJet_intrinsic_components r H hH c p hp]
  · intro p hp
    apply subset_tsupport
    intro hz
    exact hp (by simp [s, hz])

theorem globalCutoffSymmetricJetTest_apply (r : Metric (M := M)) (H : Field (M := M))
    (hH : IsSmooth H) (hS : IsSymmetric H) (β : M → ℝ)
    (hβ : ContMDiff Model 𝓘(ℝ) ∞ β) (hβc : HasCompactSupport β) (p : M) :
    (globalCutoffSymmetricJetTest r H hH hS β hβ hβc).val p =
      (β p : ℂ) • intrinsicSymmetricCovariantJet r H hH hS p := rfl

omit [IsManifold Model ∞ M] [SecondCountableTopology M] in
private theorem originalDifference_symmetric (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n)) (n : ℕ) :
    IsSymmetric (fun p => g n p - B p) := by
  intro p v w
  change g n p v w - B p v w = g n p w v - B p w v
  rw [hsB p v w, hsG n p v w]

/-- The compact original jet cut by one actual global scalar field. -/
def originalCovariantGlobalCutoffTest (r : Metric (M := M)) (B : Field (M := M))
    (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (β : M → ℝ) (hβ : ContMDiff Model 𝓘(ℝ) ∞ β) (hβc : HasCompactSupport β) (n : ℕ) :
    smoothCompactSymmetricJet M :=
  globalCutoffSymmetricJetTest r (fun p => g n p - B p)
    (IntrinsicCov2.isSmooth_difference (g n) B (hg n) hB)
    (originalDifference_symmetric B g hsB hsG n) β hβ hβc

theorem originalCovariantGlobalCutoffTest_support (r : Metric (M := M)) (B : Field (M := M))
    (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (β : M → ℝ) (hβ : ContMDiff Model 𝓘(ℝ) ∞ β) (hβc : HasCompactSupport β) (n : ℕ) :
    symmetricJetSectionSupport (originalCovariantGlobalCutoffTest r B g hB hg hsB hsG β hβ hβc n).val
      ⊆ tsupport β := by
  intro p hp
  apply subset_tsupport
  intro hz
  exact hp (by simp [originalCovariantGlobalCutoffTest, globalCutoffSymmetricJetTest_apply, hz])

omit [SecondCountableTopology M] in
/-- A global supported scalar cutoff has a genuine Euclidean smooth compact
representative in every chart containing its topological support. -/
theorem exists_chartCutoff_of_globalScalar (c : AtlasChart M) (β : M → ℝ)
    (hβ : ContMDiff Model 𝓘(ℝ) ∞ β) (hβc : HasCompactSupport β)
    (hβs : tsupport β ⊆ c.chart.source) :
    ∃ χ : D, tsupport (χ : E → ℝ) ⊆ c.chart '' tsupport β ∧
      ∀ p ∈ c.chart.source, (χ : E → ℝ) (c.chart p) = β p := by
  let f : E → ℝ := c.chart.target.indicator (fun y => β (c.chart.symm y))
  let W := c.chart '' tsupport β
  have hW : IsCompact W := hβc.image_of_continuousOn (c.chart.continuousOn.mono hβs)
  have hWT : W ⊆ c.chart.target := image_subset_iff.mpr (c.chart.mapsTo.mono_left hβs)
  have hfW : tsupport f ⊆ W := by
    apply closure_minimal _ hW.isClosed
    intro y hy
    have ht : y ∈ c.chart.target := by
      by_contra ht
      exact hy (by simp [f, ht])
    have ht' : β (c.chart.symm y) ≠ 0 := by
      change f y ≠ 0 at hy
      simpa only [f, indicator_of_mem ht] using hy
    exact ⟨c.chart.symm y, subset_tsupport _ ht', c.chart.right_inv ht⟩
  have hf : ContDiff ℝ ∞ f := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ c.chart.target
    · have hLoc : ContDiffOn ℝ ∞ f c.chart.target := by
        have hd : ContDiffOn ℝ ∞ (fun z => β (c.chart.symm z)) c.chart.target := by
          intro z hz
          exact (contMDiffAt_iff_contDiffAt.mp
            (hβ.contMDiffAt.comp z (contMDiffAt_symm_of_mem_maximalAtlas c.compatible hz))).contDiffWithinAt
        exact hd.congr (fun z hz => indicator_of_mem hz _)
      exact hLoc.contDiffAt (c.chart.open_target.mem_nhds hy)
    · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℝ)) y).congr_of_eventuallyEq
      exact notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (hWT (hfW h)))
  refine ⟨⟨f, hf, hW.of_isClosed_subset isClosed_closure hfW⟩, hfW, ?_⟩
  intro p hp
  change c.chart.target.indicator (fun y => β (c.chart.symm y)) (c.chart p) = β p
  rw [indicator_of_mem (c.chart.mapsTo hp), c.chart.left_inv hp]

variable [T2Space M]

/-- Exact equality of the two compact tests, on the full manifold. The
coordinate input includes the same background volume half-density. -/
theorem originalCovariantGlobalCutoffTest_eq_chartTest
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (c : AtlasChart M) (β : M → ℝ) (hβ : ContMDiff Model 𝓘(ℝ) ∞ β)
    (hβc : HasCompactSupport β) (hβs : tsupport β ⊆ c.chart.source)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (hCut : ∀ p ∈ c.chart.source, (χ : E → ℝ) (c.chart p) = β p) (n : ℕ) :
    originalCovariantGlobalCutoffTest r B g hB hg hsB hsG β hβ hβc n =
      originalCovariantSymmetricJetTest r B g hB hg hn c χ hχ n := by
  let v := originalCovariantGlobalCutoffTest r B g hB hg hsB hsG β hβ hβc n
  let w := originalCovariantSymmetricJetTest r B g hB hg hn c χ hχ n
  change v = w
  apply Subtype.ext
  funext p
  by_cases hp : p ∈ c.chart.source
  · let b := chartTangentBasis c p hp
    let W := jetFiberCoordinates b
    apply Subtype.ext
    apply W.injective
    funext i
    have hRead := congrFun
      (originalCovariantSymmetricJetTest_halfDensity r B g hB hg hn hsB hsG c χ hχ n i) (c.chart p)
    change symmetricJetHalfDensity B c w.val i (c.chart p) = _ at hRead
    unfold symmetricJetHalfDensity receivingScalarTestHalfDensity at hRead
    rw [indicator_of_mem (c.chart.mapsTo hp), c.chart.left_inv hp,
      symmetricJetComponent_of_mem c w.val i p hp] at hRead
    have ha : (fixedHalfDensity B c (c.chart p) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (fixedHalfDensity_pos B hn c _ (c.chart.mapsTo hp)).ne'
    apply mul_left_cancel₀ ha
    rw [show (fixedHalfDensity B c (c.chart p) : ℂ) * W (w.val p).val i = _ from hRead,
      fixedVolumeCovariantGradientSchwartz_intrinsic r B g hB hg hn c χ hχ n i p hp, hCut p hp]
    change (fixedHalfDensity B c (c.chart p) : ℂ) * W
      ((β p : ℂ) • (intrinsicSymmetricCovariantJet r (fun q => g n q - B q)
        (IntrinsicCov2.isSmooth_difference (g n) B (hg n) hB)
        (originalDifference_symmetric B g hsB hsG n) p).val) i = _
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    change (fixedHalfDensity B c (c.chart p) : ℂ) * ((β p : ℂ) *
      (IntrinsicCov2.tensor r.inner (fun q => g n q - B q) p ![b i.1, b i.2.1, b i.2.2] : ℂ)) = _
    simp only [Complex.ofReal_mul, b]
    ring
  · have hz : β p = 0 := by
      by_contra hh
      exact hp (hβs (subset_tsupport _ hh))
    change v.val p = w.val p
    have hV : v.val p = 0 := by
      simp [v, originalCovariantGlobalCutoffTest, globalCutoffSymmetricJetTest_apply, hz]
    rw [hV]
    change 0 = symmetricJetChartLift B c _ p
    unfold symmetricJetChartLift
    rw [dif_neg hp]

end Burnett.Microlocal.Overlap
