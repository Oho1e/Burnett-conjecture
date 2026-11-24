import Burnett.Analysis.Microlocal.Overlap.AtlasCovectorGramNaturality

/-! The jet covariance endomorphism satisfies the actual chart similarity law. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Matrix Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity fixedCotangentTransitionMatrix)
open Burnett.F05.OverlapCovectors (tensorJetTransition)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ComplexConjugate ContDiff Kronecker Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The actual derivative and two covariant tensor slots change together. -/
abbrev atlasJetTransition (c d : AtlasChart M) (x : M) : Matrix JetSlot JetSlot ℂ :=
  tensorJetTransition (fixedCotangentTransitionMatrix c d x)

theorem atlasJetTransition_mul_reverse (c d : AtlasChart M) (x : M)
    (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source) :
    atlasJetTransition c d x * atlasJetTransition d c x = 1 := by
  let T := Complex.ofRealHom.mapMatrix (fixedCotangentTransitionMatrix c d x)
  let S := Complex.ofRealHom.mapMatrix (fixedCotangentTransitionMatrix d c x)
  have h : T * S = 1 := by
    rw [show T * S = Complex.ofRealHom.mapMatrix
      (fixedCotangentTransitionMatrix c d x * fixedCotangentTransitionMatrix d c x) from
        (map_mul Complex.ofRealHom.mapMatrix _ _).symm,
      fixedCotangentTransitionMatrix_mul_reverse c d x hc hd, map_one]
  change (T ⊗ₖ (T ⊗ₖ T)) * (S ⊗ₖ (S ⊗ₖ S)) = 1
  simp only [← Matrix.mul_kronecker_mul, h, Matrix.one_kronecker_one]

variable [IsManifold Model ∞ M]

/-- The actual inner product matrix on three ordered covector slots. -/
abbrev atlasJetGram (r : Metric (M := M)) (c : AtlasChart M) (x : M) : Matrix JetSlot JetSlot ℂ :=
  let R := atlasCovectorGram r c x
  R ⊗ₖ (R ⊗ₖ R)

theorem atlasJetGram_transition (r : Metric (M := M)) (c d : AtlasChart M) (x : M)
    (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source) :
    let U := atlasJetTransition c d x
    Uᴴ * atlasJetGram r d x * U = atlasJetGram r c x := by
  intro U
  let T := Complex.ofRealHom.mapMatrix (fixedCotangentTransitionMatrix c d x)
  let R := atlasCovectorGram r d x
  let S := atlasCovectorGram r c x
  have h : Tᴴ * R * T = S := atlasCovectorGram_transition r c d x hc hd
  change (T ⊗ₖ (T ⊗ₖ T))ᴴ * (R ⊗ₖ (R ⊗ₖ R)) * (T ⊗ₖ (T ⊗ₖ T)) = S ⊗ₖ (S ⊗ₖ S)
  simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, h]

abbrev atlasJetCovarianceMatrix {r : Metric (M := M)} (c : AtlasChart M)
    (A : AmplitudeCovarianceDensity r) (p : Cosphere r) : Matrix JetSlot JetSlot ℂ :=
  fun i j => atlasIntrinsicJetComponent c A p i j

theorem atlasJetCovarianceMatrix_change {r : Metric (M := M)} (c d : AtlasChart M)
    (A : AmplitudeCovarianceDensity r) (p : Cosphere r)
    (hc : projection p ∈ c.chart.source) (hd : projection p ∈ d.chart.source) :
    let U := atlasJetTransition c d (projection p)
    atlasJetCovarianceMatrix d A p = U * atlasJetCovarianceMatrix c A p * Uᴴ := by
  intro U
  let N : Matrix JetSlot JetSlot ℂ := fun i j => atlasOrderedJetEntry c A p i j
  have hN : Nᵀ = atlasJetCovarianceMatrix c A p := by
    ext i j
    exact (atlasIntrinsicJetComponent_eq_ordered c A p hc i j).symm
  ext i j
  change atlasIntrinsicJetComponent d A p i j = (U * atlasJetCovarianceMatrix c A p * Uᴴ) i j
  rw [atlasIntrinsicJetComponent_eq_ordered d A p hd]
  have h := atlasOrderedJetEntry_change c d A p hc hd j i
  change _ = ∑ k : JetSlot, ∑ l : JetSlot, conj (U j k) * U i l * N k l at h
  rw [h]
  simpa only [one_mul, hN] using orderedJet_congruence_entry U N 1 i j

/-- Raising the input indices gives the natural endomorphism on the jet fiber. -/
theorem atlasJetCovarianceOperator_intertwine {r : Metric (M := M)} (c d : AtlasChart M)
    (A : AmplitudeCovarianceDensity r) (p : Cosphere r)
    (hc : projection p ∈ c.chart.source) (hd : projection p ∈ d.chart.source) :
    let U := atlasJetTransition c d (projection p)
    atlasJetCovarianceOperator d A p * U = U * atlasJetCovarianceOperator c A p := by
  intro U
  let C := atlasJetCovarianceMatrix c A p
  let H := atlasJetGram r c (projection p)
  let H' := atlasJetGram r d (projection p)
  have hC : atlasJetCovarianceMatrix d A p = U * C * Uᴴ := atlasJetCovarianceMatrix_change c d A p hc hd
  have hH : Uᴴ * H' * U = H := atlasJetGram_transition r c d (projection p) hc hd
  change atlasJetCovarianceMatrix d A p * H' * U = U * (C * H)
  rw [hC]
  calc
    _ = U * (C * (Uᴴ * H' * U)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hH]

theorem atlasJetCovarianceOperator_change {r : Metric (M := M)} (c d : AtlasChart M)
    (A : AmplitudeCovarianceDensity r) (p : Cosphere r)
    (hc : projection p ∈ c.chart.source) (hd : projection p ∈ d.chart.source) :
    let U := atlasJetTransition c d (projection p)
    let V := atlasJetTransition d c (projection p)
    atlasJetCovarianceOperator d A p = U * atlasJetCovarianceOperator c A p * V := by
  intro U V
  have hUV : U * V = 1 := atlasJetTransition_mul_reverse c d (projection p) hc hd
  have h := atlasJetCovarianceOperator_intertwine c d A p hc hd
  change atlasJetCovarianceOperator d A p * U = U * atlasJetCovarianceOperator c A p at h
  calc
    _ = (atlasJetCovarianceOperator d A p * U) * V := by rw [Matrix.mul_assoc, hUV, Matrix.mul_one]
    _ = _ := by rw [h]

end Burnett.Microlocal.Overlap
