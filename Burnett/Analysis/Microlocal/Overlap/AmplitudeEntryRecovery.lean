import Burnett.Analysis.Microlocal.Overlap.AmplitudeTransition
import Burnett.Analysis.Microlocal.Overlap.NormalizedEntryTransport
import Burnett.Analysis.Microlocal.OriginalVolumeAuxiliaryAmplitude

/-! Recover the ordered amplitude entries from the same true auxiliary-unit jet entries. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Matrix MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric
open Burnett.Geometry.ChartVolume (chartTransition derivativeMatrix)
open Burnett.Geometry.UnitNullCompactness (cotangentCoords continuousOn_cotangentCoords cotangentTransitionMatrix)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude)
open Burnett.F05.OverlapCovariantGradient (overlapJetCoefficient)
open Burnett.F05.OverlapCovectors
open Burnett.Microlocal.FixedChartGeometricDensity
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.OverlapGradient (overlapTransition overlapTransition_eq)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open scoped BigOperators ComplexConjugate ContDiff Manifold Matrix

/-- A covariance congruence evaluated on a jet density in operator-second entry order. -/
theorem orderedJet_congruence_entry {I : Type*}
    (C : Matrix I JetSlot ℂ) (ρ : Matrix JetSlot JetSlot ℂ) (s : ℂ) (u v : I) :
    (∑ i : JetSlot, ∑ j : JetSlot, conj (C v i) * C u j * (s * ρ i j)) =
      s * (C * ρᵀ * Cᴴ) u v := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- For physical amplitude entry (u,v), the operator-second jet (i,j) contributes
the dual derivative coefficient in j to u and the coefficient in i to v. -/
def amplitudeRecoveryCoefficient (ζ : Covector) (u v : Pair) (i j : JetSlot) : ℂ :=
  conj (gradientContraction ζ v i) * gradientContraction ζ u j

theorem amplitudeRecoveryCoefficient_factor (η ζ : Covector) (hpair : ∑ a, ζ a * η a = 1)
    (ρ : Matrix JetSlot JetSlot ℂ) (A : Matrix Pair Pair ℂ)
    (hρ : ρᵀ = gradientEmbedding η * A * (gradientEmbedding η)ᴴ) (s : ℂ) (u v : Pair) :
    (∑ i : JetSlot, ∑ j : JetSlot, amplitudeRecoveryCoefficient ζ u v i j * (s * ρ i j)) =
      s * A u v := by
  unfold amplitudeRecoveryCoefficient
  rw [orderedJet_congruence_entry, hρ]
  exact congrArg (fun B : Matrix Pair Pair ℂ => s * B u v) (amplitudeCovariance_unique η ζ hpair A)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Components of the actual r-unit covector on a preferred chart's round phase space. -/
def chartUnitCovector (r : Metric (M := M)) (q : CompactChartInput M) (z : Chart q.ball) : Covector :=
  auxiliaryUnitCovector (chartAuxiliaryInverse r q z.1) (roundCovector z)

theorem continuous_chartUnitCovector (r : Metric (M := M)) (q : CompactChartInput M) :
    Continuous (chartUnitCovector r q) := by
  let U := (fun z : UnitNullCompactness.CotangentBundle M => z.proj) ⁻¹'
    (chartAt CoordinateSpace q.center).source
  have hC : ContinuousOn (cotangentCoords q.center) U := continuousOn_cotangentCoords q.center
  apply continuousOn_univ.mp
  refine (hC.comp (continuous_chartAuxiliaryRay r q).continuousOn ?_).congr ?_
  · intro z _
    exact (chartAt CoordinateSpace q.center).symm_mapsTo (q.ball_in_chart z.1.property)
  · intro z _
    exact (chartAuxiliaryRay_coords r q z).symm

/-- The real dual used to recover an amplitude on the chart's true unit section. -/
def chartUnitDual (r : Metric (M := M)) (q : CompactChartInput M) (z : Chart q.ball) : Covector :=
  raiseCovector (chartAuxiliaryInverse r q z.1) (chartUnitCovector r q z)

theorem chartUnitDual_pairing (r : Metric (M := M)) (q : CompactChartInput M) (z : Chart q.ball) :
    ∑ a, chartUnitDual r q z a * chartUnitCovector r q z a = 1 :=
  raised_auxiliary_pairing_of_unit _ _ (auxiliaryUnitCovector_unit _ _ (chartAuxiliaryNorm_pos r q z))

theorem continuous_chartUnitDual_entry (r : Metric (M := M)) (q : CompactChartInput M) (a : Index) :
    Continuous (fun z => chartUnitDual r q z a) := by
  unfold chartUnitDual raiseCovector
  apply continuous_finset_sum _
  intro b _
  have h : Continuous (fun z : Chart q.ball => chartAuxiliaryInverse r q z.1 a b) :=
    (continuous_apply b).comp ((continuous_apply a).comp
      ((continuous_chartAuxiliaryInverse r q).comp continuous_fst))
  exact h.mul ((continuous_apply b).comp (continuous_chartUnitCovector r q))

theorem continuous_chartAmplitudeRecoveryCoefficient (r : Metric (M := M)) (q : CompactChartInput M)
    (u v : Pair) (i j : JetSlot) :
    Continuous (fun z => amplitudeRecoveryCoefficient (chartUnitDual r q z) u v i j) := by
  have h (a : Pair) (k : JetSlot) :
      Continuous (fun z => gradientContraction (chartUnitDual r q z) a k) := by
    by_cases ha : k.2 = a
    · simpa only [gradientContraction, if_pos ha] using
        Complex.continuous_ofReal.comp (continuous_chartUnitDual_entry r q k.1)
    · simpa only [gradientContraction, if_neg ha] using
        (continuous_const : Continuous (fun _ : Chart q.ball => (0 : ℂ)))
  exact (Complex.continuous_conj.comp (h v i)).mul (h u j)

/-- This is the covector change from d components back to q components. -/
def receivingToSourceCotangent (q d : CompactChartInput M) (y : CoordinateSpace) :
    Matrix Index Index ℝ :=
  (derivativeMatrix (fderiv ℝ (chartTransition q.center d.center)
    (overlapTransition d.center q.center y)))ᵀ

omit [IsManifold Model ∞ M] in
theorem receivingToSourceCotangent_actual (q d : CompactChartInput M) (y : roundOverlap d q) :
    receivingToSourceCotangent q d y.1.1 =
      cotangentTransitionMatrix d.center q.center ((chartAt CoordinateSpace d.center).symm y.1.1) := by
  rw [receivingToSourceCotangent, overlapTransition_eq _ _ y.2.1]
  rfl

omit [IsManifold Model ∞ M] in
theorem overlapJetCoefficient_eq_tensorJetTransition (q d : CompactChartInput M)
    (y : CoordinateSpace) (i j : JetSlot) :
    (overlapJetCoefficient q.center d.center i j y : ℂ) =
      tensorJetTransition (receivingToSourceCotangent q d y) i j := by
  simp only [overlapJetCoefficient, receivingToSourceCotangent, tensorJetTransition, tensorPairTransition,
    Matrix.kroneckerMap_apply, Matrix.map_apply, Matrix.transpose_apply, Complex.ofReal_mul]
  ring

variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)

/-- The original source amplitude after the source cutoff is divided out on the plateau. -/
def sourceNormalizedAmplitudeDensity (r : Metric (M := M))
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (u v : Pair) (z : Chart q.ball) : ℂ :=
  (((p.sourceFactor : CoordinateSpace → ℝ) z.1 ^ 2 : ℝ) : ℂ) *
    chartAuxiliaryAmplitude r q νq hfq z u v

/-- The original target amplitude in source coordinates, with the target cutoff divided out. -/
def targetTransformedAmplitudeDensity (r : Metric (M := M))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (u v : Pair) (y : Chart d.ball) : ℂ :=
  let D := tensorPairTransition (receivingToSourceCotangent q d y.1)
  (((p.targetFactor : CoordinateSpace → ℝ) y.1 ^ 2 : ℝ) : ℂ) *
    (D * chartAuxiliaryAmplitude r d νd hfd y * Dᴴ) u v

theorem sourceNormalizedAmplitudeDensity_recovery (r : Metric (M := M))
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (u v : Pair) (z : Chart q.ball) :
    (∑ i : JetSlot, ∑ j : JetSlot, amplitudeRecoveryCoefficient (chartUnitDual r q z) u v i j *
      sourceNormalizedDensity p νq hfq i j z) =
      sourceNormalizedAmplitudeDensity p r νq hfq u v z :=
  orderedJet_congruence_entry (gradientContraction (chartUnitDual r q z)) (density νq hfq z) _ u v

/-- On the actual overlap, the two transported derivative slots are the true
source unit covector and the remaining slots carry the two-pair congruence. -/
theorem targetTransformedDensity_factor (r : Metric (M := M))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (y : roundOverlap d q)
    (hFact : ∀ i j : JetSlot, chartPhysicalCovariance d.ball νd hfd y.1 i j =
      (chartUnitCovector r d y.1 i.1 : ℂ) * (chartUnitCovector r d y.1 j.1 : ℂ) *
        chartAuxiliaryAmplitude r d νd hfd y.1 i.2 j.2)
    (i j : JetSlot) :
    let z := (roundOverlapTransition d q y).1
    targetTransformedDensity p νd hfd i j y.1 =
      (chartUnitCovector r q z j.1 : ℂ) * (chartUnitCovector r q z i.1 : ℂ) *
        targetTransformedAmplitudeDensity p r νd hfd j.2 i.2 y.1 := by
  intro z
  let T := receivingToSourceCotangent q d y.1.1
  let s := (((p.targetFactor : CoordinateSpace → ℝ) y.1.1 ^ 2 : ℝ) : ℂ)
  let A := chartAuxiliaryAmplitude r d νd hfd y.1
  let η := chartUnitCovector r d y.1
  have hη : T *ᵥ η = chartUnitCovector r q z := by
    rw [show T = receivingToSourceCotangent q d y.1.1 from rfl, receivingToSourceCotangent_actual q d y]
    exact (auxiliaryUnitCovector_roundOverlapTransition r d q y).symm
  have hN : (density νd hfd y.1)ᵀ = gradientEmbedding η * A * (gradientEmbedding η)ᴴ := by
    ext a b
    exact (hFact a b).trans (gradient_factor_entry η A a b).symm
  calc
    targetTransformedDensity p νd hfd i j y.1 =
        s * (tensorJetTransition T * (density νd hfd y.1)ᵀ * (tensorJetTransition T)ᴴ) j i := by
      simpa only [targetTransformedDensity, overlapJetCoefficient_eq_tensorJetTransition, mul_assoc, T, s]
        using orderedJet_congruence_entry (tensorJetTransition T) (density νd hfd y.1) s j i
    _ = s * (gradientEmbedding (T *ᵥ η) * (tensorPairTransition T * A * (tensorPairTransition T)ᴴ) *
        (gradientEmbedding (T *ᵥ η))ᴴ) j i := by
      rw [hN, jetCovariance_tensor_transition]
    _ = _ := by
      rw [gradient_factor_entry, hη]
      change s * ((chartUnitCovector r q z j.1 : ℂ) * (chartUnitCovector r q z i.1 : ℂ) *
        (tensorPairTransition T * A * (tensorPairTransition T)ᴴ) j.2 i.2) =
          (chartUnitCovector r q z j.1 : ℂ) * (chartUnitCovector r q z i.1 : ℂ) *
            (s * (tensorPairTransition T * A * (tensorPairTransition T)ᴴ) j.2 i.2)
      ring

theorem targetTransformedAmplitudeDensity_recovery (r : Metric (M := M))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (y : roundOverlap d q)
    (hFact : ∀ i j : JetSlot, chartPhysicalCovariance d.ball νd hfd y.1 i j =
      (chartUnitCovector r d y.1 i.1 : ℂ) * (chartUnitCovector r d y.1 j.1 : ℂ) *
        chartAuxiliaryAmplitude r d νd hfd y.1 i.2 j.2) (u v : Pair) :
    let z := (roundOverlapTransition d q y).1
    (∑ i : JetSlot, ∑ j : JetSlot, amplitudeRecoveryCoefficient (chartUnitDual r q z) u v i j *
      targetTransformedDensity p νd hfd i j y.1) =
      targetTransformedAmplitudeDensity p r νd hfd u v y.1 := by
  intro z
  let ρ : Matrix JetSlot JetSlot ℂ := fun i j => targetTransformedDensity p νd hfd i j y.1
  let A : Matrix Pair Pair ℂ := fun u v => targetTransformedAmplitudeDensity p r νd hfd u v y.1
  let η := chartUnitCovector r q z
  have hρ : ρᵀ = gradientEmbedding η * A * (gradientEmbedding η)ᴴ := by
    ext i j
    exact (targetTransformedDensity_factor p r νd hfd y hFact j i).trans
      (gradient_factor_entry η A i j).symm
  simpa only [ρ, A, one_mul] using
    amplitudeRecoveryCoefficient_factor η (chartUnitDual r q z) (chartUnitDual_pairing r q z) ρ A hρ 1 u v

end Burnett.Microlocal.Overlap
