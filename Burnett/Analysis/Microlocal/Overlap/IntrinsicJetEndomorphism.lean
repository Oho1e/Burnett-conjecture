import Burnett.Analysis.Microlocal.Overlap.AtlasJetOperatorNaturality

/-! The chart matrices represent an actual endomorphism of the complexified jet fiber. -/
set_option autoImplicit false
set_option maxRecDepth 3900
set_option maxHeartbeats 2200000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Module Matrix Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity chartTangentBasis chartTangentBasis_change
  fixedCotangentTransitionMatrix)
open Burnett.F05.OverlapCovectors (tensorJetTransition tensorPairTransition)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open scoped BigOperators ContDiff Kronecker Manifold Matrix

/-- A complex-valued real trilinear jet on an actual tangent fiber. -/
abbrev ComplexCovariantJet (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℂ

section LinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Evaluation on a real tangent basis identifies the complex jet with its ordered coordinates. -/
def jetFiberCoordinates (b : Basis Index ℝ V) : ComplexCovariantJet V ≃ₗ[ℂ] (JetSlot → ℂ) where
  toFun F := fun k => F (b k.1) (b k.2.1) (b k.2.2)
  invFun F := b.constr ℝ (fun i => b.constr ℝ (fun j => b.constr ℝ (fun k => F (i, j, k))))
  left_inv := by
    intro F
    apply b.ext
    intro i
    apply b.ext
    intro j
    apply b.ext
    intro k
    simp only [Basis.constr_basis]
  right_inv := by
    intro F
    funext k
    simp only [Basis.constr_basis]
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem jetFiberCoordinates_apply (b : Basis Index ℝ V) (F : ComplexCovariantJet V) (k : JetSlot) :
    jetFiberCoordinates b F k = F (b k.1) (b k.2.1) (b k.2.2) := rfl

/-- The same cotangent transition on all three ordered slots of a genuine jet. -/
theorem jetFiberCoordinates_change (b d : Basis Index ℝ V) (T : Matrix Index Index ℝ)
    (h : ∀ i, d i = ∑ j, T i j • b j) (F : ComplexCovariantJet V) :
    jetFiberCoordinates d F = tensorJetTransition T *ᵥ jetFiberCoordinates b F := by
  classical
  funext k
  rcases k with ⟨i, j, k⟩
  simp only [jetFiberCoordinates_apply, h i, h j, h k, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, Complex.real_smul, Finset.mul_sum,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type, tensorJetTransition, tensorPairTransition,
    Matrix.kronecker_apply, Matrix.map_apply]
  let f (a l t : Index) : ℂ :=
    (T k a : ℂ) * ((T j l : ℂ) * ((T i t : ℂ) * F (b t) (b l) (b a)))
  change (∑ a, ∑ l, ∑ t, f a l t) = _
  calc
    _ = ∑ l, ∑ a, ∑ t, f a l t := Finset.sum_comm
    _ = ∑ l, ∑ t, ∑ a, f a l t := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ t, ∑ l, ∑ a, f a l t := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro a _
      dsimp [f]
      ring

end LinearAlgebra

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem jetFiberCoordinates_atlasChange {x : M} (c d : AtlasChart M)
    (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source) (F : ComplexCovariantJet (TangentSpace Model x)) :
    jetFiberCoordinates (chartTangentBasis d x hd) F =
      atlasJetTransition c d x *ᵥ jetFiberCoordinates (chartTangentBasis c x hc) F :=
  jetFiberCoordinates_change _ _ (fixedCotangentTransitionMatrix c d x) (chartTangentBasis_change c d x hc hd) F

/-- One endomorphism on the actual jet fiber. The chart law below identifies
its coordinates in every compatible chart at the same base point. -/
def intrinsicJetCovarianceEndomorphism {r : Metric (M := M)}
    (A : AmplitudeCovarianceDensity r) (p : Cosphere r) :
    Module.End ℂ (ComplexCovariantJet (TangentSpace Model (projection p))) :=
  let x := projection p
  let c := AtlasChart.atPoint x
  let b := chartTangentBasis c x (mem_chart_source CoordinateSpace x)
  let W := jetFiberCoordinates b
  W.symm.toLinearMap.comp ((Matrix.mulVecLin (atlasJetCovarianceOperator c A p)).comp W.toLinearMap)

theorem intrinsicJetCovarianceEndomorphism_coordinates {r : Metric (M := M)}
    (A : AmplitudeCovarianceDensity r) (p : Cosphere r) (c : AtlasChart M) (hc : projection p ∈ c.chart.source)
    (F : ComplexCovariantJet (TangentSpace Model (projection p))) :
    let W := jetFiberCoordinates (chartTangentBasis c (projection p) hc)
    W (intrinsicJetCovarianceEndomorphism A p F) = atlasJetCovarianceOperator c A p *ᵥ W F := by
  intro W
  let x := projection p
  let d := AtlasChart.atPoint x
  have hd : x ∈ d.chart.source := mem_chart_source CoordinateSpace x
  let W₀ := jetFiberCoordinates (chartTangentBasis d x hd)
  let U := atlasJetTransition d c x
  have hCoords (G : ComplexCovariantJet (TangentSpace Model x)) : W G = U *ᵥ W₀ G :=
    jetFiberCoordinates_atlasChange d c hd hc G
  have hPreferred : W₀ (intrinsicJetCovarianceEndomorphism A p F) = atlasJetCovarianceOperator d A p *ᵥ W₀ F := by
    change W₀ (W₀.symm (atlasJetCovarianceOperator d A p *ᵥ W₀ F)) = _
    exact W₀.apply_symm_apply _
  have hU : atlasJetCovarianceOperator c A p * U = U * atlasJetCovarianceOperator d A p :=
    atlasJetCovarianceOperator_intertwine d c A p hd hc
  rw [hCoords (intrinsicJetCovarianceEndomorphism A p F), hPreferred, hCoords F, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hU]

end Burnett.Microlocal.Overlap
