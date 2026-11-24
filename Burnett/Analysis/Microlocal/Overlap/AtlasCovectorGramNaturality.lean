import Burnett.Analysis.Microlocal.Overlap.ReceivingJetOperatorEntries
import Burnett.Geometry.MaximalChart.UniformMetric

/-! Invariance of the inverse auxiliary metric under the genuine cotangent transition. -/
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Matrix Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric MaximalChart
open Burnett.Geometry.ChartVolume (derivativeMatrix)
open Burnett.F07.IntrinsicAmplitudeCoordinates (fixedCotangentTransitionMatrix)
open scoped ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

private theorem coordinate_in_transition (c d : AtlasChart M) (x : M)
    (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source) :
    c.chart x ∈ (c.transition d).source := by
  refine ⟨c.chart.mapsTo hc, ?_⟩
  change c.chart.symm (c.chart x) ∈ d.chart.source
  rwa [c.chart.left_inv hc]

private theorem transition_at_coordinate (c d : AtlasChart M) (x : M)
    (hc : x ∈ c.chart.source) : c.transition d (c.chart x) = d.chart x := by
  change d.chart (c.chart.symm (c.chart x)) = d.chart x
  rw [c.chart.left_inv hc]

/-- The two actual cotangent changes on an overlap are inverse matrices. -/
theorem fixedCotangentTransitionMatrix_mul_reverse (c d : AtlasChart M) (x : M)
    (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source) :
    fixedCotangentTransitionMatrix c d x * fixedCotangentTransitionMatrix d c x = 1 := by
  let D := fderiv ℝ (d.transition c) (d.chart x)
  let E := fderiv ℝ (c.transition d) (c.chart x)
  have h := chartTransition_fderiv_leftInverse d c (coordinate_in_transition d c x hd hc)
  rw [transition_at_coordinate d c x hd] at h
  have hLinear : E.toLinearMap.comp D.toLinearMap = LinearMap.id :=
    congrArg ContinuousLinearMap.toLinearMap h
  have hMatrix : derivativeMatrix E * derivativeMatrix D = 1 := by
    unfold derivativeMatrix
    rw [← LinearMap.toMatrix_comp, hLinear, LinearMap.toMatrix_id]
  change (derivativeMatrix D)ᵀ * (derivativeMatrix E)ᵀ = 1
  rw [← Matrix.transpose_mul, hMatrix, Matrix.transpose_one]

theorem complexified_realMatrix_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) :
    (Complex.ofRealHom.mapMatrix H)ᴴ = Complex.ofRealHom.mapMatrix Hᵀ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.transpose_apply, Complex.star_def]
  exact Complex.conj_ofReal (H j i)

variable [IsManifold Model ∞ M]

/-- The chart change is an isometry for the actual auxiliary covector Gram. -/
theorem atlasCovectorGram_transition (r : Metric (M := M)) (c d : AtlasChart M) (x : M)
    (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source) :
    let T := Complex.ofRealHom.mapMatrix (fixedCotangentTransitionMatrix c d x)
    Tᴴ * atlasCovectorGram r d x * T = atlasCovectorGram r c x := by
  intro T
  let D := derivativeMatrix (fderiv ℝ (d.transition c) (d.chart x))
  let Rc : Matrix Index Index ℝ := metricComponents (fixedForm r.inner c) (c.chart x)
  let Rd : Matrix Index Index ℝ := metricComponents (fixedForm r.inner d) (d.chart x)
  have hSource := coordinate_in_transition d c x hd hc
  have hRd : Rd = TensorCoordinateChange.pullbackMetric Rc D := by
    simpa only [Rd, Rc, D, transition_at_coordinate d c x hd] using
      fixedForm_matrix_change r.inner d c hSource
  have hD : IsUnit D := fixedDerivativeMatrix_isUnit d c hSource
  change (Complex.ofRealHom.mapMatrix Dᵀ)ᴴ * Complex.ofRealHom.mapMatrix Rd⁻¹ *
    Complex.ofRealHom.mapMatrix Dᵀ = Complex.ofRealHom.mapMatrix Rc⁻¹
  rw [complexified_realMatrix_conjTranspose, Matrix.transpose_transpose, ← map_mul, ← map_mul,
    hRd, TensorCoordinateChange.inverse_pullback_cancel Rc D hD]

end Burnett.Microlocal.Overlap
