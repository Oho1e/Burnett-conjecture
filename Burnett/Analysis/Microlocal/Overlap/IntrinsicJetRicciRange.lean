import Burnett.Analysis.Microlocal.Overlap.IntrinsicJetEndomorphism
import Burnett.Analysis.Microlocal.Overlap.OriginalVacuumIntrinsicAmplitude
import Burnett.Analysis.Microlocal.RicciJetSymbol

/-! The range of the original jet endomorphism satisfies the intrinsic principal constraints. -/
set_option autoImplicit false
set_option maxRecDepth 4400
set_option maxHeartbeats 2900000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Module Matrix MeasureTheory Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.IntrinsicScalarEinstein (covariantForm)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity chartTangentBasis components components_apply)
open Burnett.Microlocal.CurlDensity
open scoped ComplexOrder ContDiff Manifold Matrix Kronecker

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A rank-one gradient jet is the actual covector in the first slot times the amplitude. -/
def insertCovariantJet (ξ : Dual ℝ V) (k : ComplexBilinearForm V) : ComplexCovariantJet V := ξ.smulRight k

theorem jetFiberCoordinates_insertCovariantJet (b : Basis Index ℝ V) (ξ : Dual ℝ V) (k : ComplexBilinearForm V) :
    jetFiberCoordinates b (insertCovariantJet ξ k) =
      gradientEmbedding (FiberMetric.covector b ξ) *ᵥ (fun q : Pair => k (b q.1) (b q.2)) := by
  funext q
  rw [gradientEmbedding_mulVec]
  exact Complex.real_smul

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Every vector in the range on the true jet fiber is the unit covector
inserted in an actual symmetric amplitude in the intrinsic Ricci symbol kernel. -/
theorem intrinsicJetCovarianceEndomorphism_range_gradientRicci {r : Metric (M := M)}
    {B : Field (M := M)} {hn : IsNondegenerate B} {A : AmplitudeCovarianceDensity r} {p : Cosphere r}
    (hs : IsSymmetric B) (h : HasIntrinsicAmplitudeRicciKernel r B hn A p)
    (F : ComplexCovariantJet (TangentSpace Model (projection p))) :
    let x := projection p
    let b := chartTangentBasis (AtlasChart.atPoint x) x (mem_chart_source CoordinateSpace x)
    letI : FiniteDimensional ℝ (TangentSpace Model x) := Module.Finite.of_basis b
    ∃ k : ComplexBilinearForm (TangentSpace Model x),
      (∀ u v, k u v = k v u) ∧
      complexFiberRicciSymbol (covariantForm B x) (hn x) p.val.2.toLinearMap k = 0 ∧
      intrinsicJetCovarianceEndomorphism A p F = insertCovariantJet p.val.2.toLinearMap k := by
  intro x b
  letI : FiniteDimensional ℝ (TangentSpace Model x) := Module.Finite.of_basis b
  let c := AtlasChart.atPoint x
  have hc : x ∈ c.chart.source := mem_chart_source CoordinateSpace x
  let W := jetFiberCoordinates b
  let η := p.val.2.toLinearMap
  let ξ := FiberMetric.covector b η
  let J := gradientEmbedding ξ
  let C := components b (A p)
  let R := unitCosphereCovectorGram r p b
  let H := R ⊗ₖ (R ⊗ₖ R)
  let w := Jᴴ *ᵥ (H *ᵥ W F)
  let slice (q : Pair) := amplitudeSlice (A p) (b q.1) (b q.2)
  let k : ComplexBilinearForm (TangentSpace Model x) := ∑ q : Pair, w q • slice q
  let G := FiberMetric.contravariant (covariantForm B x) (hn x) b
  have hG : IsSymmetricTensor G := FiberMetric.contravariant_symmetric (covariantForm B x) (hn x)
    ⟨fun u v => hs x u v⟩ b
  have hkEval (u v : TangentSpace Model x) : k u v = ∑ q : Pair, w q * slice q u v := by
    let e : ComplexBilinearForm (TangentSpace Model x) →ₗ[ℂ] ℂ :=
      (LinearMap.applyₗ' ℂ v).comp (LinearMap.applyₗ' ℂ u)
    change e (∑ q, w q • slice q) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => (map_smul e (w q) (slice q))
  have hk (u v : TangentSpace Model x) : k u v = k v u := by
    rw [hkEval, hkEval]
    exact Finset.sum_congr rfl fun q _ => congrArg (w q * ·) ((h (b q.1) (b q.2)).1 u v)
  have hCoord (q : Pair) : (fun i : Pair => slice q (b i.1) (b i.2)) = fun i => C i q :=
    funext fun i => (components_apply b (A p) i q).symm
  have hkCoord : (fun i : Pair => k (b i.1) (b i.2)) = C *ᵥ w := by
    funext i
    simp only [hkEval, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun q _ => (congrArg (w q * ·) (congrFun (hCoord q) i)).trans (mul_comm _ _)
  have hCols : C *ᵥ w = ∑ q : Pair, w q • (fun i : Pair => C i q) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hRow0 (q : Pair) : ricciJetLinear G ξ (J *ᵥ (fun i : Pair => C i q)) = 0 := by
    funext i
    rw [ricciJetLinear_apply, ← hCoord q]
    change ricciJetSymbol G ξ (gradientEmbedding ξ *ᵥ (fun j : Pair => slice q (b j.1) (b j.2))) i = 0
    rw [ricciJetSymbol_gradient G ξ _ hG (fun u v => (h (b q.1) (b q.2)).1 (b u) (b v))]
    rw [← complexFiberRicciSymbol_eq_basis (covariantForm B x) (hn x) η (slice q) b]
    rw [(h (b q.1) (b q.2)).2]
    rfl
  have hRow : ricciJetLinear G ξ (J *ᵥ (C *ᵥ w)) = 0 := by
    change (ricciJetLinear G ξ).comp (Matrix.mulVecLin J) (C *ᵥ w) = 0
    rw [hCols, map_sum]
    simp only [map_smul, LinearMap.comp_apply, Matrix.mulVecLin_apply, hRow0, smul_zero, Finset.sum_const_zero]
  have hRicci : complexFiberRicciSymbol (covariantForm B x) (hn x) η k = 0 := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    have he := congrFun hRow (i, j)
    rw [ricciJetLinear_apply, ← hkCoord, ricciJetSymbol_gradient G ξ _ hG (fun u v => hk (b u) (b v)),
      ← complexFiberRicciSymbol_eq_basis (covariantForm B x) (hn x) η k b] at he
    exact he
  refine ⟨k, hk, hRicci, ?_⟩
  apply W.injective
  have hO := intrinsicJetCovarianceEndomorphism_coordinates A p c hc F
  have hO' := atlasJetCovarianceOperator_in_fiber c A p hc
  change W (intrinsicJetCovarianceEndomorphism A p F) = W (insertCovariantJet η k)
  change W (intrinsicJetCovarianceEndomorphism A p F) = _ at hO
  rw [hO, hO', intrinsicJetAmplitude, jetAmplitudeComponents_insertJetCovectors,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change J *ᵥ (C *ᵥ w) = jetFiberCoordinates b (insertCovariantJet η k)
  rw [jetFiberCoordinates_insertCovariantJet, hkCoord]

end Burnett.Microlocal.Overlap
