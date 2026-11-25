import Burnett.Analysis.Microlocal.Overlap.AtlasJetOperatorNaturality
import Burnett.Analysis.Microlocal.Overlap.ReceivingPaperConvention

/-! The principal form is paired with the same actual covariance in every chart. -/
set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 5300000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Set Matrix MeasureTheory Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open Burnett.Geometry.ManifoldMetric (Metric Model)
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity components)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped BigOperators ComplexConjugate ComplexOrder ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- A principal sesquilinear form changes by the inverse congruence to the
covariance tensor. Their trace is the same scalar on the actual overlap. -/
theorem trace_atlasJetCovariance_form_change {r : Metric (M := M)}
    (c d : AtlasChart M) (A : AmplitudeCovarianceDensity r) (p : Cosphere r)
    (hc : projection p ∈ c.chart.source) (hd : projection p ∈ d.chart.source)
    (P Q : Matrix JetSlot JetSlot ℂ)
    (hP : P = (atlasJetTransition c d (projection p))ᴴ * Q * atlasJetTransition c d (projection p)) :
    (P * atlasJetCovarianceMatrix c A p).trace = (Q * atlasJetCovarianceMatrix d A p).trace := by
  let U := atlasJetTransition c d (projection p)
  let C := atlasJetCovarianceMatrix c A p
  have hC : atlasJetCovarianceMatrix d A p = U * C * Uᴴ :=
    atlasJetCovarianceMatrix_change c d A p hc hd
  change P = Uᴴ * Q * U at hP
  rw [hP, hC]
  change ((Uᴴ * Q * U) * C).trace = (Q * (U * C * Uᴴ)).trace
  calc
    _ = (Uᴴ * (Q * (U * C))).trace := by simp only [Matrix.mul_assoc]
    _ = ((Q * (U * C)) * Uᴴ).trace := Matrix.trace_mul_comm _ _
    _ = (Q * (U * C * Uᴴ)).trace := by simp only [Matrix.mul_assoc]

variable [MeasurableSpace M] [BorelSpace M]

/-- The paper's conjugate-linear-in-operator convention is visible for any
actual principal-form matrix, on the same restricted control measure. -/
theorem ae_receivingClassicalFormDensity_eq_trace {r : Metric (M := M)}
    (A : IntrinsicAmplitudeCovariance r) (c : AtlasChart M)
    (hPos : ∀ᵐ p ∂A.control, ∀ b : Module.Basis Index ℝ (TangentSpace Model (projection p)),
      (components b (A.density p)).PosSemidef)
    (K : Set M) (hK : MeasurableSet K) (hKc : K ⊆ c.chart.source)
    (P : Cosphere r → Matrix JetSlot JetSlot ℂ) :
    ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K),
      (∑ i, ∑ j, conj (P p i j) * atlasOrderedJetEntry c A.density p j i) =
        conj ((P p * atlasJetCovarianceMatrix c A.density p).trace) := by
  let τ := A.control.restrict (amplitudeCosphereWindow r K)
  have hSwap : ∀ᵐ p ∂τ, ∀ i ∈ (Finset.univ : Finset JetSlot), ∀ j ∈ (Finset.univ : Finset JetSlot),
      conj (atlasOrderedJetEntry c A.density p i j) = atlasOrderedJetEntry c A.density p j i := by
    rw [eventually_all_finset]
    intro i _
    rw [eventually_all_finset]
    exact fun j _ => ae_atlasOrderedJetEntry_conj_swap A c hPos hK hKc i j
  filter_upwards [ae_restrict_mem (μ := A.control) (measurableSet_amplitudeCosphereWindow r hK), hSwap]
    with p hp hs
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
  rw [show atlasJetCovarianceMatrix c A.density p j i = atlasOrderedJetEntry c A.density p i j from
    atlasIntrinsicJetComponent_eq_ordered c A.density p (hKc hp) j i, hs i hi j hj]

/-- Two actual congruent principal forms have equal local scalar densities,
including the paper's conjugation, against the original single covariance. -/
theorem ae_receivingClassicalFormDensity_change {r : Metric (M := M)}
    (A : IntrinsicAmplitudeCovariance r) (c d : AtlasChart M)
    (hPos : ∀ᵐ p ∂A.control, ∀ b : Module.Basis Index ℝ (TangentSpace Model (projection p)),
      (components b (A.density p)).PosSemidef)
    (K : Set M) (hK : MeasurableSet K) (hKc : K ⊆ c.chart.source) (hKd : K ⊆ d.chart.source)
    (P Q : Cosphere r → Matrix JetSlot JetSlot ℂ)
    (hChange : ∀ p : Cosphere r, projection p ∈ K →
      P p = (atlasJetTransition c d (projection p))ᴴ * Q p * atlasJetTransition c d (projection p)) :
    ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K),
      (∑ i, ∑ j, conj (P p i j) * atlasOrderedJetEntry c A.density p j i) =
        (∑ i, ∑ j, conj (Q p i j) * atlasOrderedJetEntry d A.density p j i) := by
  filter_upwards [ae_restrict_mem (μ := A.control) (measurableSet_amplitudeCosphereWindow r hK),
    ae_receivingClassicalFormDensity_eq_trace A c hPos K hK hKc P,
    ae_receivingClassicalFormDensity_eq_trace A d hPos K hK hKd Q] with p hp hc hd
  rw [hc, hd, trace_atlasJetCovariance_form_change c d A.density p (hKc hp) (hKd hp) _ _ (hChange p hp)]

end Burnett.Microlocal.Overlap
