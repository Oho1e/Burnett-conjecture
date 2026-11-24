import Burnett.Analysis.Microlocal.Overlap.IntrinsicRicciFiberSymbol
import Burnett.Analysis.Microlocal.Overlap.GlobalIntrinsicAmplitudeAlmostEverywhere

set_option autoImplicit false
set_option maxRecDepth 3200
set_option maxHeartbeats 2400000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Module Matrix Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.ContravariantTensor (tensorTangentBasis tensorTangentBasis_apply)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.UnitNullCompactness (cotangentTrivialization_apply)
open Burnett.F05.ActualChartAuxiliarySection
  (chartAuxiliaryCosphere chartAuxiliaryInverse chartAuxiliaryRay chartAuxiliaryRay_coords)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeTensor AmplitudeCovarianceDensity components components_apply)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.FixedChartGeometricDensity (auxiliaryUnitCovector roundCovector)
open Burnett.Microlocal.RicciRow (backgroundInverse)
open Burnett.F07.IntrinsicAmplitude (chartAmplitudeTangentBasis chartInverse_entries orderedChartAmplitudeComponents)
open Burnett.Geometry.IntrinsicScalarEinstein (covariantForm)
open scoped BigOperators ContDiff Manifold Matrix


section LinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Fixing the last two slots applies the ordered covariance to the tensor
product of the coordinates of those two tangent vectors. -/
theorem amplitudeSlice_components_mulVec (b : Basis Index ℝ V) (F : AmplitudeTensor V) (s t : V) :
    (fun i j => amplitudeSlice F s t (b i) (b j)) =
      fun i j => (components b F *ᵥ (fun p : Pair => ((b.repr s p.1 * b.repr t p.2 : ℝ) : ℂ))) (i, j) := by
  classical
  funext i j
  let f := F.toLinearMap ![b i, b j, 0, t] (0 : Fin 2).succ.succ
  have hf (x : V) : f x = F ![b i, b j, x, t] := by
    change F (Function.update ![b i, b j, 0, t] (0 : Fin 2).succ.succ x) = _
    simp only [Matrix.vecCons, ← Fin.cons_update, Fin.update_cons_zero]
  have hs : F ![b i, b j, s, t] = ∑ a, b.repr s a • F ![b i, b j, b a, t] := by
    have h : f (∑ a, b.repr s a • b a) = f s := congrArg f (b.sum_repr s)
    simp only [map_sum, map_smul] at h
    simpa only [hf] using h.symm
  have ht (a : Index) : F ![b i, b j, b a, t] = ∑ c, b.repr t c • F ![b i, b j, b a, b c] := by
    let f := F.toLinearMap ![b i, b j, b a, 0] (0 : Fin 1).succ.succ.succ
    have hf (x : V) : f x = F ![b i, b j, b a, x] := by
      change F (Function.update ![b i, b j, b a, 0] (0 : Fin 1).succ.succ.succ x) = _
      simp only [Matrix.vecCons, ← Fin.cons_update, Fin.update_cons_zero]
    have h : f (∑ c, b.repr t c • b c) = f t := congrArg f (b.sum_repr t)
    simp only [map_sum, map_smul] at h
    simpa only [hf] using h.symm
  rw [amplitudeSlice_apply, hs, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [ht a, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [components_apply]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

variable [FiniteDimensional ℝ V]

/-- The actual bilinear Ricci symbol vanishes on every slice of the amplitude
if every complex vector gives a symmetric coordinate amplitude in its kernel. -/
theorem amplitudeSlice_ricciKernel_of_components
    (b : Basis Index ℝ V) (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate)
    (η : Dual ℝ V) (F : AmplitudeTensor V)
    (h : ∀ v : Pair → ℂ,
      let k (a c : Index) := (components b F *ᵥ v) (a, c)
      IsSymmetricComplexTensor k ∧
        ∀ i j, complexRicciSymbol (FiberMetric.contravariant g hg b) (FiberMetric.covector b η) k i j = 0) :
    ∀ s t : V,
      let k := amplitudeSlice F s t
      (∀ u w, k u w = k w u) ∧ complexFiberRicciSymbol g hg η k = 0 := by
  intro s t k
  let v (p : Pair) : ℂ := (b.repr s p.1 * b.repr t p.2 : ℝ)
  have hSlice : (fun i j => k (b i) (b j)) = fun i j => (components b F *ᵥ v) (i, j) :=
    amplitudeSlice_components_mulVec b F s t
  have hCoordinates : IsSymmetricComplexTensor (fun i j => k (b i) (b j)) ∧
      ∀ i j, complexRicciSymbol (FiberMetric.contravariant g hg b) (FiberMetric.covector b η)
        (fun a c => k (b a) (b c)) i j = 0 := by
    rw [hSlice]
    exact h v
  have hSymm : k = k.flip := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    exact hCoordinates.1 i j
  refine ⟨fun u w => LinearMap.congr_fun₂ hSymm u w, ?_⟩
  apply b.ext
  intro i
  apply b.ext
  intro j
  change complexFiberRicciSymbol g hg η k (b i) (b j) = 0
  rw [complexFiberRicciSymbol_eq_basis]
  exact hCoordinates.2 i j

end LinearAlgebra

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The symmetric Ricci kernel on the actual tangent fiber and actual covector.
Each choice of the last two tangent arguments of the covariance is allowed. -/
def HasIntrinsicAmplitudeRicciKernel (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (J : AmplitudeCovarianceDensity r) (p : Cosphere r) : Prop :=
  let x := projection p
  letI : FiniteDimensional ℝ (TangentSpace Model x) :=
    Module.Finite.of_basis (tensorTangentBasis x x (mem_chart_source CoordinateSpace x))
  ∀ s t : TangentSpace Model x,
    let k := amplitudeSlice (J p) s t
    (∀ u w, k u w = k w u) ∧
      complexFiberRicciSymbol (covariantForm B x) (hn x) p.val.2.toLinearMap k = 0

/-- At an actual represented point the background inverse and the auxiliary
unit covector give exactly the entries of the intrinsic fiber symbol. -/
theorem intrinsicAmplitudeRicciKernel_of_chart
    (r : Metric (M := M)) (B : Field (M := M)) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (q : CompactChartInput M) (J : AmplitudeCovarianceDensity r) (z : Chart q.ball)
    (h : ∀ v : Pair → ℂ,
      let k (a c : Index) := (orderedChartAmplitudeComponents r q J z *ᵥ v) (a, c)
      let η := auxiliaryUnitCovector (chartAuxiliaryInverse r q z.1) (roundCovector z)
      IsSymmetricComplexTensor k ∧
        ∀ i j, complexRicciSymbol (backgroundInverse B q.center z.1) η k i j = 0) :
    HasIntrinsicAmplitudeRicciKernel r B hn J (chartAuxiliaryCosphere r q z) := by
  let p := chartAuxiliaryCosphere r q z
  let x := projection p
  let b : Basis Index ℝ (TangentSpace Model x) := chartAmplitudeTangentBasis r q z
  let g := covariantForm B x
  let η : Dual ℝ (TangentSpace Model x) := p.val.2.toLinearMap
  letI : FiniteDimensional ℝ (TangentSpace Model x) := Module.Finite.of_basis b
  have hx : x ∈ (chartAt CoordinateSpace q.center).source :=
    (chartAt CoordinateSpace q.center).symm_mapsTo (q.ball_in_chart z.1.property)
  have hInv : FiberMetric.contravariant g (hn x) b = backgroundInverse B q.center z.1 := by
    funext i j
    rw [← fiberInverseForm_eq_contravariant]
    exact chartInverse_entries r B hs hn q z i j
  have hCov : FiberMetric.covector b η =
      auxiliaryUnitCovector (chartAuxiliaryInverse r q z.1) (roundCovector z) := by
    funext i
    change (chartAuxiliaryRay r q z).2 (tensorTangentBasis q.center x hx i) = _
    rw [tensorTangentBasis_apply]
    exact (cotangentTrivialization_apply q.center (chartAuxiliaryRay r q z) (coordinateBasis i)).symm.trans
      (congrFun (chartAuxiliaryRay_coords r q z) i)
  have hComponents : components b (J p) = orderedChartAmplitudeComponents r q J z := by
    ext i j
    exact components_apply b (J p) i j
  apply amplitudeSlice_ricciKernel_of_components b g (hn x) η (J p)
  intro v
  simpa only [hInv, hCov, hComponents] using h v

variable [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The original represented countable cover gives the actual fiber Ricci
kernel almost everywhere for the same global amplitude control. -/
theorem HasOriginalAmplitudeChartLaws.ae_intrinsicAmplitudeRicciKernel
    {r : Metric (M := M)} {B : Field (M := M)} {g : ℕ → Field (M := M)}
    {hB : IsSmooth B} {hg : ∀ n, IsSmooth (g n)} {hnB : IsNondegenerate B}
    {σ : ℕ → ℕ} {A : IntrinsicAmplitudeCovariance r}
    (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (hσ : StrictMono σ)
    (q : ℕ → CompactChartInput M) (cover : ⋃ i, (q i).cutoffLocusAbove (1 / 2) = univ)
    (ν : ∀ i, (JetSlot → ℂ) → Measure (Chart (q i).ball))
    (hf : ∀ i v, IsFiniteMeasure (ν i v))
    (hRep : ∀ i, let a := q i
      RepresentsCompactJetPairings a.ball
        (originalGradient_volumeWeightedL2 B g hB hg hnB a.center a.cutoff
          (a.cutoff_support.trans a.ball_in_chart)) σ (ν i) (hf i)) :
    ∀ᵐ p ∂A.control, HasIntrinsicAmplitudeRicciKernel r B hnB A.density p := by
  filter_upwards [hA.ae_global_positive_unitTrace_ricciKernel hsB hsG hnG hconv hb hv hσ q cover ν hf hRep]
    with p hp
  obtain ⟨_, _, i, z, _, rfl, _, _, _, hKernel⟩ := hp
  exact intrinsicAmplitudeRicciKernel_of_chart r B hsB hnB (q i) A.density z hKernel

end Burnett.Microlocal.Overlap
