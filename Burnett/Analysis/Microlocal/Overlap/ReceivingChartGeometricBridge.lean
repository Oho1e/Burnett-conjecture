import Burnett.Analysis.Microlocal.Overlap.AtlasChartAmplitudeBorelChange
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The moving frequency and the ordered inverse Jacobians of a fixed
maximal-atlas chart transition agree with the intrinsic fields. -/

set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Burnett.RicciSymbol Burnett.Geometry ConnectionDifference ManifoldMetric
open Burnett.Geometry.ChartVolume (derivativeMatrix)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase fixedPhaseTransition
  fixedChartPhase_of_mem fixedPhaseTransition_fixedChartPhase)
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Geometry.UnitNullCompactness (CotangentBundle covectorCLM)
open Burnett.F05.OverlapCovectors (tensorJetTransition tensorPairTransition)
open Burnett.F07.IntrinsicAmplitudeCoordinates (fixedCotangentTransitionMatrix)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped BigOperators ContDiff InnerProduct Manifold Kronecker

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The adjoint of the true reverse chart derivative transports cotangent
frequencies to the receiving chart. -/
def receivingFrequency (c d : AtlasChart M) (x : E) : E →L[ℝ] E :=
  (fderiv ℝ (d.transition c) (c.transition d x)).adjoint

/-- The three inverse Jacobian factors used to change a covariant metric jet. -/
def inverseJetEntry (c d : AtlasChart M) (i j : JetSlot) (x : E) : ℝ :=
  let J := derivativeMatrix (fderiv ℝ (d.transition c) (c.transition d x))
  J j.1 i.1 * J j.2.1 i.2.1 * J j.2.2 i.2.2

/-- Each ordered jet coefficient is the exact corresponding entry of the
intrinsic three-slot change matrix. -/
theorem inverseJetEntry_eq_tensorJetTransition (c d : AtlasChart M)
    {x : M} (hc : x ∈ c.chart.source) (i j : JetSlot) :
    (inverseJetEntry c d i j (c.chart x) : ℂ) =
      tensorJetTransition (fixedCotangentTransitionMatrix c d x) i j := by
  have hBase : c.transition d (c.chart x) = d.chart x := by
    change d.chart (c.chart.symm (c.chart x)) = d.chart x
    rw [c.chart.left_inv hc]
  simp only [inverseJetEntry, hBase, tensorJetTransition, tensorPairTransition,
    Matrix.kroneckerMap_apply, Matrix.map_apply, fixedCotangentTransitionMatrix, Matrix.transpose_apply,
    Complex.ofReal_mul]
  ring

private theorem inner_eq_covectorCLM (ξ v : E) :
    inner ℝ ξ v = covectorCLM (fun i => ξ i) v := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', covectorCLM,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

variable [IsManifold Model ∞ M]

/-- The receiving Fourier covector is the coordinate of the same intrinsic
cotangent vector, with its actual norm and before any round normalization. -/
theorem receivingFrequency_eq_fixedChartPhase (c d : AtlasChart M)
    (p : CotangentBundle M) (hc : p.proj ∈ c.chart.source) (hd : p.proj ∈ d.chart.source) :
    receivingFrequency c d (c.chart p.proj) (WithLp.toLp 2 (fixedChartPhase c p).2) =
      WithLp.toLp 2 (fixedChartPhase d p).2 := by
  let ξ : E := WithLp.toLp 2 (fixedChartPhase c p).2
  have hBase : c.transition d (c.chart p.proj) = d.chart p.proj := by
    change d.chart (c.chart.symm (c.chart p.proj)) = d.chart p.proj
    rw [c.chart.left_inv hc]
  have hPhase := congrArg Prod.snd (fixedPhaseTransition_fixedChartPhase c d p hc hd)
  have hPhaseEntry (i : Index) : covectorCLM (fixedChartPhase c p).2
      (fderiv ℝ (d.transition c) (d.chart p.proj) (coordinateBasis i)) =
      (fixedChartPhase d p).2 i := by
    have hSource : (fixedChartPhase c p).1 = c.chart p.proj :=
      congrArg Prod.fst (fixedChartPhase_of_mem c p hc)
    have h := congrFun hPhase i
    change covectorCLM (fixedChartPhase c p).2
      (fderiv ℝ (d.transition c) (c.transition d (fixedChartPhase c p).1) (coordinateBasis i)) = _ at h
    rwa [hSource, hBase] at h
  ext i
  change (receivingFrequency c d (c.chart p.proj) ξ) i = (fixedChartPhase d p).2 i
  rw [← EuclideanSpace.inner_basisFun_real Index (receivingFrequency c d (c.chart p.proj) ξ) i, receivingFrequency,
    ContinuousLinearMap.adjoint_inner_left, inner_eq_covectorCLM, hBase]
  exact hPhaseEntry i

end Burnett.Microlocal.AtlasOverlapKernel
