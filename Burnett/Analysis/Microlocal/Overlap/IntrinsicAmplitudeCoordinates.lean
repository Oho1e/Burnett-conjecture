import Burnett.Analysis.Microlocal.Overlap.AmplitudeTransition
import Burnett.Geometry.Cotangent.CosphereMeasure
import Burnett.Geometry.Cotangent.FixedChartNaturality
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! Ordered amplitude entries determine a genuine four-slot tensor in each tangent fiber. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Burnett.F07.IntrinsicAmplitudeCoordinates

open Bundle Matrix Module Set Burnett.RicciSymbol
open Burnett.F05.OverlapCovectors (tensorPairTransition)
open Burnett.Microlocal.CurlDensity (Pair)
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.ChartVolume (derivativeMatrix)
open Burnett.Geometry.FixedCotangentChart (inverseFrame inverseFrame_change)
open scoped BigOperators ContDiff Manifold Matrix

/-- The real multilinearity is in the tangent slots. The coefficients are complex. -/
abbrev AmplitudeTensor (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  MultilinearMap ℝ (fun _ : Fin 4 => V) ℂ

section OrderedEntries

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private def orderedSlots (p q : Pair) : Fin 4 → Index := ![p.1, p.2, q.1, q.2]

private def slotsToPairs : (Fin 4 → Index) ≃ Pair × Pair where
  toFun i := ((i 0, i 1), (i 2, i 3))
  invFun p := orderedSlots p.1 p.2
  left_inv i := by
    funext s
    fin_cases s <;> rfl
  right_inv p := by
    rcases p with ⟨⟨_, _⟩, ⟨_, _⟩⟩
    rfl

/-- The ordered matrix entry is the value on four actual basis vectors. -/
def components (b : Basis Index ℝ V) (F : AmplitudeTensor V) : Matrix Pair Pair ℂ :=
  fun p q => F (fun s => b (orderedSlots p q s))

/-- Extend arbitrary ordered entries by real multilinearity in the four slots. -/
def fromComponents (b : Basis Index ℝ V) (A : Matrix Pair Pair ℂ) : AmplitudeTensor V :=
  ∑ i : Fin 4 → Index,
    (MultilinearMap.mkPiRing ℝ (Fin 4) (A (i 0, i 1) (i 2, i 3))).compLinearMap
      (fun s => b.coord (i s))

theorem fromComponents_apply_basis (b : Basis Index ℝ V) (A : Matrix Pair Pair ℂ)
    (i : Fin 4 → Index) :
    fromComponents b A (fun s => b (i s)) = A (i 0, i 1) (i 2, i 3) := by
  classical
  rw [fromComponents, MultilinearMap.sum_apply, Finset.sum_eq_single i]
  · simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply, Basis.coord_apply,
      Basis.repr_self_apply, if_true, Finset.prod_const_one, one_smul]
  · intro j _ hj
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hj
    have hzero : b.coord (j s) (b (i s)) = 0 := by
      rw [Basis.coord_apply, Basis.repr_self_apply, if_neg (Ne.symm hs)]
    simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply]
    rw [Finset.prod_eq_zero (Finset.mem_univ s) hzero, zero_smul]
  · simp

theorem components_fromComponents (b : Basis Index ℝ V) (A : Matrix Pair Pair ℂ) :
    components b (fromComponents b A) = A := by
  ext p q
  exact fromComponents_apply_basis b A (orderedSlots p q)

theorem components_injective (b : Basis Index ℝ V) : Function.Injective (components b) := by
  intro F G h
  apply Module.Basis.ext_multilinear (fun _ : Fin 4 => b)
  intro i
  have h' := congrArg (fun A : Matrix Pair Pair ℂ => A (i 0, i 1) (i 2, i 3)) h
  change F (fun s => b (orderedSlots (i 0, i 1) (i 2, i 3) s)) =
    G (fun s => b (orderedSlots (i 0, i 1) (i 2, i 3) s)) at h'
  rw [show orderedSlots (i 0, i 1) (i 2, i 3) = i from slotsToPairs.left_inv i] at h'
  exact h'

theorem fromComponents_components (b : Basis Index ℝ V) (F : AmplitudeTensor V) :
    fromComponents b (components b F) = F :=
  components_injective b (components_fromComponents b (components b F))

theorem components_apply (b : Basis Index ℝ V) (F : AmplitudeTensor V) (p q : Pair) :
    components b F p q = F ![b p.1, b p.2, b q.1, b q.2] := by
  apply congrArg F
  funext s
  fin_cases s <;> rfl

private theorem tensorPairTransition_apply (T : Matrix Index Index ℝ) (p q : Pair) :
    tensorPairTransition T p q = (T p.1 q.1 : ℂ) * (T p.2 q.2 : ℂ) := rfl

theorem tensorPairTransition_conjTranspose (T : Matrix Index Index ℝ) :
    (tensorPairTransition T)ᴴ = (tensorPairTransition T)ᵀ := by
  ext p q
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, tensorPairTransition_apply,
    Complex.star_def, map_mul, Complex.conj_ofReal]

private theorem slotProduct (T : Matrix Index Index ℝ) (p q u v : Pair)
    (z : ℂ) :
    (∏ s : Fin 4, T (orderedSlots p q s) (orderedSlots u v s)) • z =
      tensorPairTransition T p u * z * tensorPairTransition T q v := by
  simp only [Fin.prod_univ_four, Complex.real_smul, Complex.ofReal_mul, tensorPairTransition_apply]
  change ((T p.1 u.1 : ℂ) * (T p.2 u.2 : ℂ) * (T q.1 v.1 : ℂ) * (T q.2 v.2 : ℂ)) * z = _
  ring

/-- If the rows of the real matrix give the new basis vectors in the old basis,
the ordered entries transform in both pairs by the existing tensor pair transition. -/
theorem components_change (b b' : Basis Index ℝ V) (T : Matrix Index Index ℝ)
    (hb : ∀ i, b' i = ∑ j, T i j • b j) (F : AmplitudeTensor V) :
    components b' F = tensorPairTransition T * components b F * (tensorPairTransition T)ᴴ := by
  classical
  ext p q
  let D := tensorPairTransition T
  let w (j : Fin 4 → Index) :=
    (∏ s : Fin 4, T (orderedSlots p q s) (j s)) • (F fun s => b (j s))
  have hnew :
      (fun s : Fin 4 => b' (orderedSlots p q s)) = fun s => ∑ i, T (orderedSlots p q s) i • b i := by
    funext s
    exact hb (orderedSlots p q s)
  calc
    components b' F p q = ∑ j : Fin 4 → Index, w j := by
      unfold components
      rw [hnew, F.map_sum]
      simp only [w, F.map_smul_univ]
    _ = ∑ uv : Pair × Pair, D p uv.1 * components b F uv.1 uv.2 * D q uv.2 := by
      apply Fintype.sum_equiv slotsToPairs
      intro j
      have hj : orderedSlots (slotsToPairs j).1 (slotsToPairs j).2 = j := slotsToPairs.left_inv j
      change w j = D p (slotsToPairs j).1 * components b F (slotsToPairs j).1 (slotsToPairs j).2 *
        D q (slotsToPairs j).2
      conv_lhs => rw [← hj]
      exact slotProduct T p q _ _ _
    _ = (D * components b F * Dᴴ) p q := by
      have hD : Dᴴ = Dᵀ := tensorPairTransition_conjTranspose T
      rw [Fintype.sum_prod_type_right, hD]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]

end OrderedEntries

section ActualFibers

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

abbrev AmplitudeFiber (x : M) := AmplitudeTensor (TangentSpace Model x)

/-- This field is defined on the actual auxiliary unit cosphere at the base projection. -/
abbrev AmplitudeCovarianceDensity (r : Metric (M := M)) :=
  (p : UnitCosphere.Cosphere r) → AmplitudeFiber (UnitCosphere.projection p)

theorem inverseFrame_preferred (c x : M) (hx : x ∈ (chartAt CoordinateSpace c).source) :
    inverseFrame (.atPoint c) x = tangentFrame c x :=
  (ChartDifferential.tangentFrame_eq_mfderiv_symm c x hx).symm

private theorem inverseFrame_bijective (c : AtlasChart M) (x : M) (hx : x ∈ c.chart.source) :
    Function.Bijective (inverseFrame c x) := by
  let d : AtlasChart M := .atPoint x
  have hd : x ∈ d.chart.source := mem_chart_source CoordinateSpace x
  have hy : c.chart x ∈ (c.transition d).source := by
    refine ⟨c.chart.mapsTo hx, ?_⟩
    change c.chart.symm (c.chart x) ∈ d.chart.source
    rwa [c.chart.left_inv hx]
  let L := fderiv ℝ (c.transition d) (c.chart x)
  have hLdet : IsUnit (LinearMap.toMatrix coordinateBasis coordinateBasis L.toLinearMap).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (fixedDerivativeMatrix_isUnit c d hy)
  have hL : Function.Bijective L := (LinearEquiv.ofIsUnitDet hLdet).bijective
  rw [inverseFrame_change d c x hd hx, inverseFrame_preferred x x hd]
  have hframe : Function.Bijective (tangentFrame x x) :=
    ⟨tangentFrame_injective x x hd, tangentFrame_surjective x x hd⟩
  change Function.Bijective ((tangentFrame x x) ∘ L)
  exact Function.Bijective.comp hframe hL

/-- The coordinate basis carried to the actual fiber by the derivative of the inverse chart. -/
def chartTangentBasis (c : AtlasChart M) (x : M) (hx : x ∈ c.chart.source) :
    Basis Index ℝ (TangentSpace Model x) :=
  coordinateBasis.map (LinearEquiv.ofBijective (inverseFrame c x).toLinearMap
    (inverseFrame_bijective c x hx))

theorem chartTangentBasis_apply (c : AtlasChart M) (x : M) (hx : x ∈ c.chart.source) (i : Index) :
    chartTangentBasis c x hx i = inverseFrame c x (coordinateBasis i) := by
  rw [chartTangentBasis, Basis.map_apply]
  rfl

theorem chartTangentBasis_preferred (c x : M) (hx : x ∈ (chartAt CoordinateSpace c).source) (i : Index) :
    chartTangentBasis (.atPoint c) x hx i = tangentFrame c x (coordinateBasis i) := by
  rw [chartTangentBasis_apply, inverseFrame_preferred c x hx]

/-- The actual matrix taking c-covector components to d-covector components at x. -/
def fixedCotangentTransitionMatrix (c d : AtlasChart M) (x : M) : Matrix Index Index ℝ :=
  (derivativeMatrix (fderiv ℝ (d.transition c) (d.chart x)))ᵀ

theorem fixedCotangentTransitionMatrix_preferred (c d x : M) :
    fixedCotangentTransitionMatrix (.atPoint c) (.atPoint d) x =
      UnitNullCompactness.cotangentTransitionMatrix c d x := rfl

theorem chartTangentBasis_change (c d : AtlasChart M) (x : M)
    (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source) (i : Index) :
    chartTangentBasis d x hd i = ∑ j,
      fixedCotangentTransitionMatrix c d x i j • chartTangentBasis c x hc j := by
  let L := fderiv ℝ (d.transition c) (d.chart x)
  simp only [chartTangentBasis_apply, inverseFrame_change c d x hc hd, ContinuousLinearMap.comp_apply,
    fixedCotangentTransitionMatrix, Matrix.transpose_apply, derivativeMatrix, LinearMap.toMatrix_apply]
  simpa only [map_sum, map_smul] using
    (congrArg (inverseFrame c x) (coordinateBasis.sum_repr (L (coordinateBasis i)))).symm

/-- Construct the actual amplitude tensor at a point from its ordered chart entries. -/
def chartAmplitude (c : AtlasChart M) (x : M) (hx : x ∈ c.chart.source)
    (A : Matrix Pair Pair ℂ) : AmplitudeFiber x :=
  fromComponents (chartTangentBasis c x hx) A

def chartComponents (c : AtlasChart M) (x : M) (hx : x ∈ c.chart.source)
    (F : AmplitudeFiber x) : Matrix Pair Pair ℂ :=
  components (chartTangentBasis c x hx) F

/-- Assemble a pointwise field from matrices supplied in charts covering their actual base points. -/
def densityFromChartMatrices {r : Metric (M := M)}
    (c : UnitCosphere.Cosphere r → AtlasChart M)
    (hc : ∀ p, UnitCosphere.projection p ∈ (c p).chart.source)
    (A : UnitCosphere.Cosphere r → Matrix Pair Pair ℂ) : AmplitudeCovarianceDensity r :=
  fun p => chartAmplitude (c p) (UnitCosphere.projection p) (hc p) (A p)

theorem chartComponents_chartAmplitude (c : AtlasChart M) (x : M) (hx : x ∈ c.chart.source)
    (A : Matrix Pair Pair ℂ) :
    chartComponents c x hx (chartAmplitude c x hx A) = A :=
  components_fromComponents _ _

set_option maxRecDepth 2048 in
theorem chartAmplitude_apply_basis (c : AtlasChart M) (x : M) (hx : x ∈ c.chart.source)
    (A : Matrix Pair Pair ℂ) (a b d e : Index) :
    let v := chartTangentBasis c x hx
    chartAmplitude c x hx A ![v a, v b, v d, v e] = A (a, b) (d, e) := by
  intro v
  have h := congrArg (fun W : Matrix Pair Pair ℂ => W (a, b) (d, e))
    (chartComponents_chartAmplitude c x hx A)
  change components v (chartAmplitude c x hx A) (a, b) (d, e) = A (a, b) (d, e) at h
  rw [components_apply] at h
  exact h

theorem chartComponents_injective (c : AtlasChart M) (x : M) (hx : x ∈ c.chart.source) :
    Function.Injective (chartComponents c x hx) :=
  components_injective _

theorem chartComponents_change (c d : AtlasChart M) (x : M)
    (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source) (F : AmplitudeFiber x) :
    let D := tensorPairTransition (fixedCotangentTransitionMatrix c d x)
    chartComponents d x hd F = D * chartComponents c x hc F * Dᴴ :=
  components_change _ _ _ (chartTangentBasis_change c d x hc hd) F

/-- Congruent ordered matrices reconstruct literally the same actual fiber tensor. -/
theorem chartAmplitude_change (c d : AtlasChart M) (x : M)
    (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source) (A : Matrix Pair Pair ℂ) :
    let D := tensorPairTransition (fixedCotangentTransitionMatrix c d x)
    chartAmplitude d x hd (D * A * Dᴴ) = chartAmplitude c x hc A := by
  intro D
  apply chartComponents_injective d x hd
  rw [chartComponents_chartAmplitude, chartComponents_change c d x hc hd,
    chartComponents_chartAmplitude]

end ActualFibers

end Burnett.F07.IntrinsicAmplitudeCoordinates
