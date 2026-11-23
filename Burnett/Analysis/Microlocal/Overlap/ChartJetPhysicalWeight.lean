import Burnett.Analysis.Microlocal.Overlap.AuxiliaryRay
import Burnett.Analysis.Microlocal.Overlap.TransportedJetCoefficients
import Burnett.Analysis.Microlocal.PhysicalDensity
import Burnett.Analysis.Microlocal.CoordinateRicciPrincipalRow
import Burnett.Geometry.Cotangent.SmoothExtension
import Burnett.Geometry.ManifoldTensorNorm
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! The physical contraction of a coordinate jet uses the actual inverse metrics. -/

set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Matrix Set Burnett.RicciSymbol Burnett.Geometry
open ChartVolume ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricTransition
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryRay continuous_chartAuxiliaryRay)
open Burnett.F05.OverlapCovariantGradient (overlapJetCoefficient)
open Burnett.F05.OverlapCovectors (roundOverlap roundOverlapTransition chartAuxiliaryRay_roundOverlapTransition)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.OverlapGradient (overlapTransition)
open Burnett.Microlocal.OverlapKernel (overlapTransition_reverse_apply)
open Burnett.Microlocal.RicciRow (backgroundInverse)
open Burnett.Geometry.UnitNullCompactness (dualEnergy)
open Burnett.Geometry.CotangentAngularExtension (contMDiff_dualEnergy)
open scoped BigOperators ComplexConjugate ContDiff Kronecker Manifold

private def flattenJetMetric (G : Matrix Index Index ℝ) (p : Pair) : ℝ := G p.1 p.2

private theorem flattenJetMetric_change (J G : Matrix Index Index ℝ) :
    (J ⊗ₖ J) *ᵥ flattenJetMetric G = flattenJetMetric (J * G * Jᵀ) := by
  funext p
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    flattenJetMetric, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private def physicalMatrix (G : Matrix Index Index ℝ) : Matrix Pair Pair ℝ :=
  G ⊗ₖ G - (1 / 2 : ℝ) • Matrix.vecMulVec (flattenJetMetric G) (flattenJetMetric G)

private theorem kron_transpose {m n u v : Type*} (A : Matrix m n ℝ) (B : Matrix u v ℝ) :
    (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := rfl

private theorem physicalMatrix_change (J G : Matrix Index Index ℝ) :
    (J ⊗ₖ J) * physicalMatrix G * (J ⊗ₖ J)ᵀ = physicalMatrix (J * G * Jᵀ) := by
  unfold physicalMatrix
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, flattenJetMetric_change,
    kron_transpose, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

/-- The two amplitude pairs occur in reverse order in the jet covariance density
with the operator applied in the second slot. -/
def orderedPhysicalJetWeight (R G : Matrix Index Index ℝ) : Matrix JetSlot JetSlot ℝ :=
  (1 / 4 : ℝ) • (R ⊗ₖ (physicalMatrix G)ᵀ)

theorem orderedPhysicalJetWeight_apply (R G : Matrix Index Index ℝ) (i j : JetSlot) :
    orderedPhysicalJetWeight R G i j = (1 / 4 : ℝ) * R i.1 j.1 *
      (G j.2.1 i.2.1 * G j.2.2 i.2.2 - G j.2.1 j.2.2 * G i.2.1 i.2.2 / 2) := by
  simp only [orderedPhysicalJetWeight, physicalMatrix, Matrix.smul_apply, smul_eq_mul,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply, flattenJetMetric]
  ring

private theorem orderedPhysicalJetWeight_change (J R G : Matrix Index Index ℝ) :
    (J ⊗ₖ (J ⊗ₖ J)) * orderedPhysicalJetWeight R G * (J ⊗ₖ (J ⊗ₖ J))ᵀ =
      orderedPhysicalJetWeight (J * R * Jᵀ) (J * G * Jᵀ) := by
  have h := congrArg Matrix.transpose (physicalMatrix_change J G)
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h
  unfold orderedPhysicalJetWeight
  rw [Matrix.mul_smul, Matrix.smul_mul, kron_transpose,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem inverse_chart_congruence (B : Field (M := M)) (c d : M)
    {x : CoordinateSpace} (hx : x ∈ (chartTransition c d).source) :
    let J := derivativeMatrix (fderiv ℝ (chartTransition c d) x)
    J * Matrix.of (backgroundInverse B c x) * Jᵀ =
      Matrix.of (backgroundInverse B d (chartTransition c d x)) := by
  have hJ := ManifoldTensorNorm.transitionMatrix_isUnit c d ((chartAt CoordinateSpace c).symm x)
    ((chartAt CoordinateSpace c).map_target hx.1) hx.2
  rw [(chartAt CoordinateSpace c).right_inv hx.1] at hJ
  let J := derivativeMatrix (fderiv ℝ (chartTransition c d) x)
  let Bc : Matrix Index Index ℝ := metricComponents (coordinateBilinear B c) x
  let Bd : Matrix Index Index ℝ := metricComponents (coordinateBilinear B d) (chartTransition c d x)
  change J * Bc⁻¹ * Jᵀ = Bd⁻¹
  have hB : Bc = TensorCoordinateChange.pullbackMetric Bd J := coordinateBilinear_matrix_change B c d hx
  rw [hB]
  exact TensorCoordinateChange.inverse_pullback_cancel _ _ hJ

/-- The coefficient of a jet entry in the actual physical scalar density. -/
def chartPhysicalJetWeight (r : Metric (M := M)) (B : Field (M := M)) (c : M)
    (x : CoordinateSpace) : Matrix JetSlot JetSlot ℝ :=
  orderedPhysicalJetWeight (backgroundInverse r.inner c x) (backgroundInverse B c x)

private theorem chartPhysicalJetWeight_change (r : Metric (M := M)) (B : Field (M := M))
    (c d : M) {x : CoordinateSpace} (hx : x ∈ (chartTransition c d).source) (k l : JetSlot) :
    ∑ i : JetSlot, ∑ j : JetSlot, chartPhysicalJetWeight r B c x i j *
        overlapJetCoefficient c d i k (chartTransition c d x) *
          overlapJetCoefficient c d j l (chartTransition c d x) =
      chartPhysicalJetWeight r B d (chartTransition c d x) k l := by
  let J := derivativeMatrix (fderiv ℝ (chartTransition c d) x)
  have h := orderedPhysicalJetWeight_change J (backgroundInverse r.inner c x) (backgroundInverse B c x)
  have hEnd := h.trans (congrArg₂ orderedPhysicalJetWeight
    (inverse_chart_congruence r.inner c d hx) (inverse_chart_congruence B c d hx))
  have hEntry := congrArg (fun T : Matrix JetSlot JetSlot ℝ => T k l) hEnd
  refine Eq.trans ?_ hEntry
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
    Matrix.kroneckerMap_apply, overlapJetCoefficient, overlapTransition_reverse_apply c d hx,
    chartPhysicalJetWeight, J]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Contracting the two Jacobian-transformed slots in the source coordinates
is the same as physical contraction in the receiving coordinates. -/
theorem chartPhysicalJetWeight_contraction_change (r : Metric (M := M)) (B : Field (M := M))
    (c d : M) {x : CoordinateSpace} (hx : x ∈ (chartTransition c d).source)
    (ρ : JetSlot → JetSlot → ℂ) :
    let y := chartTransition c d x
    ∑ i : JetSlot, ∑ j : JetSlot, (chartPhysicalJetWeight r B c x i j : ℂ) *
      (∑ k : JetSlot, ∑ l : JetSlot, conj (↑(overlapJetCoefficient c d i k y) : ℂ) *
        (↑(overlapJetCoefficient c d j l y) : ℂ) * ρ k l) =
      ∑ k : JetSlot, ∑ l : JetSlot, (chartPhysicalJetWeight r B d y k l : ℂ) * ρ k l := by
  intro y
  let f (p u : JetSlot × JetSlot) : ℂ := (chartPhysicalJetWeight r B c x p.1 p.2 : ℂ) *
    ((overlapJetCoefficient c d p.1 u.1 y : ℂ) * (overlapJetCoefficient c d p.2 u.2 y : ℂ) * ρ u.1 u.2)
  have swap (t : (JetSlot × JetSlot) → (JetSlot × JetSlot) → ℂ) :
      (∑ i, ∑ j, ∑ k, ∑ l, t (i,j) (k,l)) = ∑ k, ∑ l, ∑ i, ∑ j, t (i,j) (k,l) := by
    calc
      _ = ∑ p, ∑ u, t p u := by simp only [Fintype.sum_prod_type]
      _ = ∑ u, ∑ p, t p u := Finset.sum_comm
      _ = _ := by simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l, f (i,j) (k,l) := by
      simp only [f, Finset.mul_sum, Complex.conj_ofReal]
    _ = ∑ k, ∑ l, ∑ i, ∑ j, f (i,j) (k,l) := swap f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [← chartPhysicalJetWeight_change r B c d hx k l]
      simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, f]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The Lorentz shell in a chart of the actual auxiliary unit cotangent rays. -/
def chartAuxiliaryNull (r : Metric (M := M)) (B : Field (M := M)) (hn : IsNondegenerate B)
    (q : CompactChartInput M) : Set (Chart q.ball) :=
  {z | dualEnergy B hn (chartAuxiliaryRay r q z) = 0}

theorem measurableSet_chartAuxiliaryNull (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hs : IsSymmetric B) (hn : IsNondegenerate B) (q : CompactChartInput M) :
    MeasurableSet (chartAuxiliaryNull r B hn q) :=
  (isClosed_eq ((contMDiff_dualEnergy B hB hn hs).continuous.comp (continuous_chartAuxiliaryRay r q))
    continuous_const).measurableSet

theorem chartAuxiliaryNull_roundTransition (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (q d : CompactChartInput M) (z : roundOverlap q d) :
    (roundOverlapTransition q d z).1 ∈ chartAuxiliaryNull r B hn d ↔
      z.1 ∈ chartAuxiliaryNull r B hn q := by
  simp only [chartAuxiliaryNull, mem_setOf_eq, chartAuxiliaryRay_roundOverlapTransition]

end Burnett.Microlocal.Overlap
