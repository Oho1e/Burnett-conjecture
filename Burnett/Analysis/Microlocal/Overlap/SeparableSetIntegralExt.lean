import Burnett.Analysis.Microlocal.CompactJetMatrixMeasure
import Burnett.Analysis.Microlocal.Overlap.WeightedSetIntegralExt

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CompactOrderedFunctional (orderedFunctional_eq_of_sameListValues)
open Burnett.Microlocal.CompactFunctionalProducer (TestSpace)
open Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.SmoothAngularTests (complexRationalAngularSymbol)

private def weightedPullbackTestFunctional
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (φ : X → Y) (hφ : Measurable φ) (f : X → ℂ) (hf : Integrable f μ) :
    C(Y, ℂ) →L[ℂ] ℂ := by
  have hI (a : C(Y, ℂ)) : Integrable (fun x => a (φ x) * f x) μ :=
    hf.bdd_mul (a.continuous.measurable.comp hφ).aestronglyMeasurable ⟨‖a‖, fun x => a.norm_coe_le_norm (φ x)⟩
  let L : C(Y, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun a => ∫ x, a (φ x) * f x ∂μ
      map_add' := by
        intro a b
        change (∫ x, (a (φ x) + b (φ x)) * f x ∂μ) = _
        simpa only [add_mul] using integral_add (hI a) (hI b)
      map_smul' := by
        intro c a
        change (∫ x, (c * a (φ x)) * f x ∂μ) = c * ∫ x, a (φ x) * f x ∂μ
        simp only [mul_assoc, integral_const_mul] }
  refine L.mkContinuous (∫ x, ‖f x‖ ∂μ) (fun a => ?_)
  change ‖∫ x, a (φ x) * f x ∂μ‖ ≤ (∫ x, ‖f x‖ ∂μ) * ‖a‖
  have hNorm := norm_integral_le_of_norm_le (hf.norm.const_mul ‖a‖)
    (Filter.Eventually.of_forall fun x => show ‖a (φ x) * f x‖ ≤ ‖a‖ * ‖f x‖ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (a.norm_coe_le_norm (φ x)) (norm_nonneg _))
  rw [integral_const_mul, mul_comm ‖a‖] at hNorm
  exact hNorm

/-- On the compact chart phase space, the dense separated restrictions
determine all measurable-set entries of any integrable complex weights. -/
theorem setIntegral_preimage_eq_of_separable_weighted_tests
    {X : Type*} [MeasurableSpace X] (K : BallData)
    (μ : Measure X) (ν : Measure (Chart K)) (φ : X → Chart K) (hφ : Measurable φ)
    (f : X → ℂ) (g : Chart K → ℂ) (hf : Integrable f μ) (hg : Integrable g ν)
    (h : ∀ ps : SeparableParameters,
      (∫ x, separableRestriction K ps (φ x) * f x ∂μ) =
        ∫ y, separableRestriction K ps y * g y ∂ν)
    (S : Set (Chart K)) (hS : MeasurableSet S) :
    (∫ x in φ ⁻¹' S, f x ∂μ) = ∫ y in S, g y ∂ν := by
  let F : TestSpace K →L[ℂ] ℂ := weightedPullbackTestFunctional μ φ hφ f hf
  let G : TestSpace K →L[ℂ] ℂ := weightedPullbackTestFunctional ν id measurable_id g hg
  have hFG : F = G := orderedFunctional_eq_of_sameListValues K F G fun ps => by
    change (∫ x, separableRestriction K ps (φ x) * f x ∂μ) =
        ∫ y, separableRestriction K ps y * g y ∂ν
    exact h ps
  exact setIntegral_preimage_eq_of_continuous_weighted_tests μ ν φ hφ f g hf hg
    (fun a => by
      have hA := congrArg (fun L : TestSpace K →L[ℂ] ℂ => L a) hFG
      change (∫ x, a (φ x) * f x ∂μ) = ∫ y, a y * g y ∂ν at hA
      exact hA) S hS

/-- Agreement for individual base/angular separated terms supplies exactly
the dense list tests used to identify compact chart measure entries. -/
theorem setIntegral_preimage_eq_of_weightedChartTerms
    {X : Type*} [MeasurableSpace X] (K : BallData)
    (μ : Measure X) (ν : Measure (Chart K)) (φ : X → Chart K) (hφ : Measurable φ)
    (f : X → ℂ) (g : Chart K → ℂ) (hf : Integrable f μ) (hg : Integrable g ν)
    (h : ∀ t : TermParameters,
      (∫ x, (baseSymbol K t.1 (φ x).1 * complexRationalAngularSymbol t.2 (φ x).2) * f x ∂μ) =
        ∫ y, (baseSymbol K t.1 y.1 * complexRationalAngularSymbol t.2 y.2) * g y ∂ν)
    (S : Set (Chart K)) (hS : MeasurableSet S) :
    (∫ x in φ ⁻¹' S, f x ∂μ) = ∫ y in S, g y ∂ν := by
  have hIf (ps : SeparableParameters) : Integrable (fun x => separableRestriction K ps (φ x) * f x) μ :=
    hf.bdd_mul ((separableRestriction K ps).continuous.measurable.comp hφ).aestronglyMeasurable
      ⟨‖separableRestriction K ps‖, fun x => (separableRestriction K ps).norm_coe_le_norm (φ x)⟩
  have hIg (ps : SeparableParameters) : Integrable (fun x => separableRestriction K ps x * g x) ν :=
    hg.bdd_mul (separableRestriction K ps).continuous.measurable.aestronglyMeasurable
      ⟨‖separableRestriction K ps‖, (separableRestriction K ps).norm_coe_le_norm⟩
  have hOne (t : TermParameters) (y : Chart K) :
      separableRestriction K [t] y = baseSymbol K t.1 y.1 * complexRationalAngularSymbol t.2 y.2 := by
    rcases y with ⟨x, ξ⟩
    simp only [separableRestriction_apply, separableValue, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
  apply setIntegral_preimage_eq_of_separable_weighted_tests K μ ν φ hφ f g hf hg _ S hS
  intro ps
  induction ps with
  | nil =>
      simp only [separableRestriction, List.map_nil, List.sum_nil, ContinuousMap.zero_apply, zero_mul, integral_zero]
  | cons t ps ih =>
      have hAdd (p : Chart K) :
          separableRestriction K (t :: ps) p = separableRestriction K [t] p + separableRestriction K ps p := by
        rcases p with ⟨x, ξ⟩
        simp only [separableRestriction_apply, separableValue, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero]
      simp_rw [hAdd, add_mul]
      rw [integral_add (hIf [t]) (hIf ps), integral_add (hIg [t]) (hIg ps), ih]
      simp_rw [hOne]
      rw [h t]

end Burnett.Microlocal.Overlap
