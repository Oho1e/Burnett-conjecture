import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option maxHeartbeats 3600000

noncomputable section

namespace Burnett.Analysis

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

universe u

variable {A Z F : Type u}
variable [NormedAddCommGroup A] [NormedSpace ℝ A]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative restricted to the first factor of the parameter product. -/
def parameterDerivative (G : A × Z → F) (p : A × Z) : A →L[ℝ] F :=
  (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ A Z)

private theorem contDiffOn_parameterDerivative {G : A × Z → F} {U : Set A}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (parameterDerivative G) (U ×ˢ univ) := by
  let compose := (ContinuousLinearMap.compL ℝ A (A × Z) F).flip (ContinuousLinearMap.inl ℝ A Z)
  exact compose.contDiff.comp_contDiffOn (hG.fderiv_of_isOpen (hU.prod isOpen_univ) (by simp))

variable [ProperSpace A] [MeasurableSpace Z] [BorelSpace Z] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem hasFDerivAt_integral_compact_parameter
    (μ : Measure Z) [IsLocallyFiniteMeasure μ] (K : Set Z) (hK : IsCompact K)
    (G : A × Z → F) (U : Set A) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G (U ×ˢ univ))
    {x : A} (hx : x ∈ U) :
    HasFDerivAt (fun a => ∫ z in K, G (a,z) ∂μ)
      (∫ z in K, parameterDerivative G (x,z) ∂μ) x := by
  obtain ⟨ε, hε, hBall⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let μ' := μ.restrict K
  letI : IsFiniteMeasure μ' := ⟨by
    dsimp [μ']
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact hK.measure_lt_top⟩
  have hPairDerivative := contDiffOn_parameterDerivative hU hG
  have hContinuous : ∀ a ∈ U, ContinuousOn (fun z => G (a,z)) K := by
    intro a ha
    exact hG.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z _ => ⟨ha, mem_univ z⟩)
  have hDerivAt (a : A) (ha : a ∈ U) (z : Z) :
      HasFDerivAt (fun b => G (b,z)) (parameterDerivative G (a,z)) a := by
    have hij : HasFDerivAt (fun b : A => (b,z)) (ContinuousLinearMap.inl ℝ A Z) a := by
      convert (hasFDerivAt_id a).prodMk (hasFDerivAt_const z a) using 1
    exact ((hG.differentiableOn (by simp) (a,z) ⟨ha, mem_univ z⟩).differentiableAt
      ((hU.prod isOpen_univ).mem_nhds ⟨ha, mem_univ z⟩)).hasFDerivAt.comp a hij
  have hSub : closedBall x ε ×ˢ K ⊆ U ×ˢ (univ : Set Z) :=
    fun p hp => ⟨hBall hp.1, mem_univ p.2⟩
  have hBounded : Bornology.IsBounded (parameterDerivative G '' (closedBall x ε ×ˢ K)) :=
    (((isCompact_closedBall x ε).prod hK).image_of_continuousOn
      (hPairDerivative.continuousOn.mono hSub)).isBounded
  obtain ⟨C, hC⟩ := hBounded.exists_norm_le
  have hNear : ∀ᶠ a in 𝓝 x, a ∈ U := hU.mem_nhds hx
  have hM : ∀ᶠ a in 𝓝 x, AEStronglyMeasurable (fun z => G (a,z)) μ' := hNear.mono
    fun a ha => ((hContinuous a ha).integrableOn_compact hK).aestronglyMeasurable
  have hDm : AEStronglyMeasurable (fun z => parameterDerivative G (x,z)) μ' := by
    have hCont : ContinuousOn (fun z => parameterDerivative G (x,z)) K :=
      hPairDerivative.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun z _ => ⟨hx, mem_univ z⟩)
    exact (hCont.integrableOn_compact hK).aestronglyMeasurable
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ') (x₀ := x)
    (F := fun a z => G (a,z)) (F' := fun a z => parameterDerivative G (a,z))
    (bound := fun _ : Z => C) hε hM
    ((hContinuous x hx).integrableOn_compact hK) hDm ?_ (integrable_const C) ?_
  · filter_upwards [ae_restrict_mem (μ := μ) hK.measurableSet] with z hz
    intro a ha
    exact hC _ (mem_image_of_mem _ ⟨ball_subset_closedBall ha, hz⟩)
  · exact Eventually.of_forall fun z a ha => hDerivAt a (hBall (ball_subset_closedBall ha)) z

private theorem contDiffOn_integral_compact_parameter_nat (n : ℕ)
    (μ : Measure Z) [IsLocallyFiniteMeasure μ] (K : Set Z) (hK : IsCompact K)
    (G : A × Z → F) (U : Set A) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G (U ×ˢ univ)) :
    ContDiffOn ℝ n (fun a => ∫ z in K, G (a,z) ∂μ) U := by
  induction n generalizing F with
  | zero =>
      apply contDiffOn_zero.mpr
      exact (show DifferentiableOn ℝ (fun a => ∫ z in K, G (a,z) ∂μ) U from
        fun a ha => (hasFDerivAt_integral_compact_parameter μ K hK G U hU hG ha).differentiableAt.differentiableWithinAt).continuousOn
  | succ n ih =>
      have hDiff : DifferentiableOn ℝ (fun a => ∫ z in K, G (a,z) ∂μ) U :=
        fun a ha => (hasFDerivAt_integral_compact_parameter μ K hK G U hU hG ha).differentiableAt.differentiableWithinAt
      change ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) (fun a => ∫ z in K, G (a,z) ∂μ) U
      refine (contDiffOn_succ_iff_fderiv_of_isOpen hU).mpr ⟨hDiff, by simp, ?_⟩
      apply (ih (parameterDerivative G) (contDiffOn_parameterDerivative hU hG)).congr
      intro a ha
      exact (hasFDerivAt_integral_compact_parameter μ K hK G U hU hG ha).fderiv

/-- Joint smoothness on an open parameter slice passes through integration
over a fixed compact base. -/
theorem contDiffOn_integral_compact_parameter
    (μ : Measure Z) [IsLocallyFiniteMeasure μ] (K : Set Z) (hK : IsCompact K)
    (G : A × Z → F) (U : Set A) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun a => ∫ z in K, G (a,z) ∂μ) U :=
  contDiffOn_infty.mpr fun n => contDiffOn_integral_compact_parameter_nat n μ K hK G U hU hG

end Burnett.Analysis
