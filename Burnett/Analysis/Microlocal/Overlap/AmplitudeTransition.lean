import Burnett.Analysis.Microlocal.Overlap.AuxiliaryRay
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Transforming the ordered components of an amplitude

The Kronecker matrix for the three jet slots intertwines the gradient
embedding with the two-slot change of tensor coordinates. The resulting
amplitude congruence applies when the two jet covariances are related by
this coordinate change.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.F05.OverlapCovectors

open Matrix
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Geometry.UnitNullCompactness (cotangentTransitionMatrix)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.Microlocal.CountableAuxiliaryCharts Burnett.Microlocal.CurlDensity
open Burnett.Microlocal.FixedChartGeometricDensity
open scoped BigOperators ContDiff Kronecker Manifold Matrix

/-- Change of coordinates for both covariant tensor slots. -/
def tensorPairTransition (T : Matrix Index Index ℝ) : Matrix Pair Pair ℂ :=
  (T.map Complex.ofReal) ⊗ₖ (T.map Complex.ofReal)

/-- The derivative slot is followed by the two ordered tensor slots. -/
def tensorJetTransition (T : Matrix Index Index ℝ) : Matrix JetSlot JetSlot ℂ :=
  (T.map Complex.ofReal) ⊗ₖ tensorPairTransition T

theorem gradientEmbedding_tensor_transition (T : Matrix Index Index ℝ) (ξ : Covector) :
    tensorJetTransition T * gradientEmbedding ξ =
      gradientEmbedding (T *ᵥ ξ) * tensorPairTransition T := by
  classical
  ext i j
  let B := tensorPairTransition T
  have hRight : (gradientEmbedding (T *ᵥ ξ) * B) i j =
      ((T *ᵥ ξ) i.1 : ℂ) * B i.2 j :=
    gradientEmbedding_mulVec _ (fun k => B k j) i
  change (tensorJetTransition T * gradientEmbedding ξ) i j =
    (gradientEmbedding (T *ᵥ ξ) * B) i j
  rw [hRight]
  simp only [tensorJetTransition, Matrix.mul_apply,
    Fintype.sum_prod_type (α₁ := Index) (α₂ := Pair), gradientEmbedding, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.mulVec, dotProduct, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  change (T i.1 k : ℂ) * B i.2 j * (ξ k : ℂ) = (T i.1 k : ℂ) * (ξ k : ℂ) * B i.2 j
  ring

theorem jetCovariance_tensor_transition
    (T : Matrix Index Index ℝ) (ξ : Covector) (A : Matrix Pair Pair ℂ) :
    let E := gradientEmbedding ξ
    let E' := gradientEmbedding (T *ᵥ ξ)
    let J := tensorJetTransition T
    let D := tensorPairTransition T
    J * (E * A * Eᴴ) * Jᴴ = E' * (D * A * Dᴴ) * E'ᴴ := by
  dsimp only
  calc
    _ = (tensorJetTransition T * gradientEmbedding ξ) * A *
        (tensorJetTransition T * gradientEmbedding ξ)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [gradientEmbedding_tensor_transition, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]

theorem auxiliaryAmplitudeCovariance_tensor_transition (T : Matrix Index Index ℝ)
    (Q : Tensor2) (ξ : Covector) (hξ : symbolNorm Q (T *ᵥ ξ) = 1)
    (N : Matrix JetSlot JetSlot ℂ) (A : Matrix Pair Pair ℂ)
    (hN : N = gradientEmbedding ξ * A * (gradientEmbedding ξ)ᴴ) :
    auxiliaryAmplitudeCovariance Q (T *ᵥ ξ) (tensorJetTransition T * N * (tensorJetTransition T)ᴴ) =
      tensorPairTransition T * A * (tensorPairTransition T)ᴴ := by
  rw [hN, jetCovariance_tensor_transition]
  exact amplitudeCovariance_unique (T *ᵥ ξ) (raiseCovector Q (T *ᵥ ξ))
    (raised_auxiliary_pairing_of_unit Q _ hξ) _

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- At a genuine overlap phase point, a transported factored jet covariance
has the corresponding two-slot covariance on the same auxiliary unit ray. -/
theorem auxiliaryAmplitudeCovariance_roundOverlapTransition
    (r : Burnett.Geometry.ManifoldMetric.Metric (M := M)) (q d : CompactChartInput M)
    (p : roundOverlap q d) (N : Matrix JetSlot JetSlot ℂ) (A : Matrix Pair Pair ℂ)
    (hN : let η := auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1.1) (roundCovector p.1)
      N = gradientEmbedding η * A * (gradientEmbedding η)ᴴ) :
    let p' := (roundOverlapTransition q d p).1
    let Q := chartAuxiliaryInverse r d p'.1
    let η' := auxiliaryUnitCovector Q (roundCovector p')
    let T := cotangentTransitionMatrix q.center d.center ((chartAt CoordinateSpace q.center).symm p.1.1)
    auxiliaryAmplitudeCovariance Q η' (tensorJetTransition T * N * (tensorJetTransition T)ᴴ) =
      tensorPairTransition T * A * (tensorPairTransition T)ᴴ := by
  dsimp only
  have h := auxiliaryUnitCovector_roundOverlapTransition r q d p
  have hunit := auxiliaryUnitCovector_unit (chartAuxiliaryInverse r d (roundOverlapTransition q d p).1.1)
    (roundCovector (roundOverlapTransition q d p).1)
    (chartAuxiliaryNorm_pos r d (roundOverlapTransition q d p).1)
  dsimp only at h
  rw [h] at hunit ⊢
  exact auxiliaryAmplitudeCovariance_tensor_transition _ _ _ hunit N A hN

end Burnett.F05.OverlapCovectors
