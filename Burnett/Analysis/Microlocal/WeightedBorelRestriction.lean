import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section

namespace Burnett.Microlocal.LocalMeasureComparison

open Set MeasureTheory Filter
open scoped Topology

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

private theorem integrable_simple_mul (μ : Measure X) (F : X → Z) (hF : Measurable F)
    (a : X → ℂ) (ha : Integrable a μ) (v : SimpleFunc Z ℂ) :
    Integrable (fun x => v (F x) * a x) μ := by
  obtain ⟨C,hC⟩ := (v.map norm).exists_forall_le
  exact ha.bdd_mul' (v.measurable.comp hF).aestronglyMeasurable (Eventually.of_forall fun x => hC (F x))

private theorem simple_piece_integral (μ : Measure X) (F : X → Z) (hF : Measurable F) (a : X → ℂ)
    (s : Set Z) (hs : MeasurableSet s) (c : ℂ) :
    (∫ x, (SimpleFunc.piecewise s hs (SimpleFunc.const Z c) (SimpleFunc.const Z 0)) (F x) * a x ∂μ) =
      c * ∫ x in F ⁻¹' s, a x ∂μ := by
  rw [← integral_const_mul, ← integral_indicator (hF hs)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : F x ∈ s <;> simp [SimpleFunc.piecewise_apply, hx]

private theorem limit_weighted (μ : Measure X) (F : X → Z) (hF : Measurable F)
    (a : X → ℂ) (ha : Integrable a μ) (v : Z → ℂ) (hv : StronglyMeasurable v)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ z, ‖v z‖ ≤ C) :
    Tendsto (fun n => ∫ x, hv.approxBounded C n (F x) * a x ∂μ)
      atTop (𝓝 (∫ x, v (F x) * a x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => C * ‖a x‖)
  · intro n
    exact ((hv.approxBounded C n).measurable.comp hF).aestronglyMeasurable.mul ha.aestronglyMeasurable
  · exact ha.norm.const_mul C
  · exact fun n => Eventually.of_forall fun x => (norm_mul _ _).le.trans
      (mul_le_mul_of_nonneg_right (hv.norm_approxBounded_le hC n (F x)) (norm_nonneg _))
  · exact Eventually.of_forall fun x => (hv.tendsto_approxBounded_of_norm_le (hbound (F x))).mul tendsto_const_nhds

/-- Equality of all complex observations on sets passes to bounded Borel
weights; the underlying trace measures and their spaces may differ. -/
theorem integral_weight_eq_of_setIntegrals (μ : Measure X) (ν : Measure Y)
    (F : X → Z) (G : Y → Z) (hF : Measurable F) (hG : Measurable G)
    (a : X → ℂ) (b : Y → ℂ) (ha : Integrable a μ) (hb : Integrable b ν)
    (h : ∀ s : Set Z, MeasurableSet s → (∫ x in F ⁻¹' s, a x ∂μ) = ∫ y in G ⁻¹' s, b y ∂ν)
    (w : Z → ℂ) (hw : Measurable w) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ z, ‖w z‖ ≤ C) :
    (∫ x, w (F x) * a x ∂μ) = ∫ y, w (G y) * b y ∂ν := by
  have simple (v : SimpleFunc Z ℂ) : (∫ x, v (F x) * a x ∂μ) = ∫ y, v (G y) * b y ∂ν := by
    induction v using SimpleFunc.induction with
    | const c hs => rw [simple_piece_integral μ F hF, simple_piece_integral ν G hG, h _ hs]
    | @add f g _ hf hg =>
      simp only [SimpleFunc.coe_add, Pi.add_apply, add_mul]
      rw [integral_add (integrable_simple_mul μ F hF a ha f) (integrable_simple_mul μ F hF a ha g),
        integral_add (integrable_simple_mul ν G hG b hb f) (integrable_simple_mul ν G hG b hb g), hf, hg]
  apply tendsto_nhds_unique (limit_weighted μ F hF a ha w hw.stronglyMeasurable C hC hbound)
  exact (limit_weighted ν G hG b hb w hw.stronglyMeasurable C hC hbound).congr
    (fun n => (simple (hw.stronglyMeasurable.approxBounded C n)).symm)

/-- If the pushed complex entries agree on a window, multiplying them by
the same bounded measurable coordinate weight preserves this equality on
the window. This applies to the localized Jacobian coefficients. -/
theorem weighted_map_restrict_eq (μ : Measure X) (ν : Measure Y)
    (F : X → Z) (G : Y → Z) (hF : Measurable F) (hG : Measurable G)
    (a : X → ℂ) (b : Y → ℂ) (ha : Integrable a μ) (hb : Integrable b ν)
    (U : Set Z) (hU : MeasurableSet U)
    (h : ((μ.withDensityᵥ a).map F).restrict U = ((ν.withDensityᵥ b).map G).restrict U)
    (w : Z → ℂ) (hw : Measurable w) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ z, ‖w z‖ ≤ C) :
    ((μ.withDensityᵥ (fun x => w (F x) * a x)).map F).restrict U =
      ((ν.withDensityᵥ (fun y => w (G y) * b y)).map G).restrict U := by
  have hi : Integrable (fun x => w (F x) * a x) μ :=
    ha.bdd_mul' (hw.comp hF).aestronglyMeasurable (Eventually.of_forall fun x => hbound (F x))
  have hj : Integrable (fun y => w (G y) * b y) ν :=
    hb.bdd_mul' (hw.comp hG).aestronglyMeasurable (Eventually.of_forall fun y => hbound (G y))
  have localSet (t : Set Z) (ht : MeasurableSet t) (hsub : t ⊆ U) :
      (∫ x in F ⁻¹' t, a x ∂μ) = ∫ y in G ⁻¹' t, b y ∂ν := by
    have eq := congrArg (fun m : VectorMeasure Z ℂ => m t) h
    simpa only [VectorMeasure.restrict_eq_self _ hU ht hsub, VectorMeasure.map_apply _ hF ht,
      VectorMeasure.map_apply _ hG ht, withDensityᵥ_apply ha (hF ht), withDensityᵥ_apply hb (hG ht)] using eq
  apply VectorMeasure.ext
  intro s hs
  rw [VectorMeasure.restrict_apply _ hU hs, VectorMeasure.restrict_apply _ hU hs,
    VectorMeasure.map_apply _ hF (hs.inter hU), VectorMeasure.map_apply _ hG (hs.inter hU),
    withDensityᵥ_apply hi (hF (hs.inter hU)), withDensityᵥ_apply hj (hG (hs.inter hU))]
  apply integral_weight_eq_of_setIntegrals _ _ F G hF hG a b ha.integrableOn hb.integrableOn _ w hw C hC hbound
  intro t ht
  rw [Measure.restrict_restrict (hF ht), Measure.restrict_restrict (hG ht)]
  exact localSet (t ∩ (s ∩ U)) (ht.inter (hs.inter hU)) (inter_subset_right.trans inter_subset_right)

/-- A finite sum of integrable densities can be changed entry by entry
on a measurable window, even when the two trace measures differ. -/
theorem finset_map_restrict_eq {ι : Type*} (I : Finset ι)
    (μ : Measure X) (ν : Measure Y) (F : X → Z) (G : Y → Z)
    (hF : Measurable F) (hG : Measurable G) (a : ι → X → ℂ) (b : ι → Y → ℂ)
    (ha : ∀ i ∈ I, Integrable (a i) μ) (hb : ∀ i ∈ I, Integrable (b i) ν)
    (U : Set Z) (hU : MeasurableSet U)
    (h : ∀ i ∈ I, ((μ.withDensityᵥ (a i)).map F).restrict U = ((ν.withDensityᵥ (b i)).map G).restrict U) :
    ((μ.withDensityᵥ (fun x => ∑ i ∈ I, a i x)).map F).restrict U =
      ((ν.withDensityᵥ (fun y => ∑ i ∈ I, b i y)).map G).restrict U := by
  apply VectorMeasure.ext
  intro s hs
  have ht := hs.inter hU
  have row (i : ι) (hi : i ∈ I) :
      (∫ x in F ⁻¹' (s ∩ U), a i x ∂μ) = ∫ y in G ⁻¹' (s ∩ U), b i y ∂ν := by
    have eq := congrArg (fun m : VectorMeasure Z ℂ => m s) (h i hi)
    simpa only [VectorMeasure.restrict_apply _ hU hs, VectorMeasure.map_apply _ hF ht,
      VectorMeasure.map_apply _ hG ht, withDensityᵥ_apply (ha i hi) (hF ht),
      withDensityᵥ_apply (hb i hi) (hG ht)] using eq
  rw [VectorMeasure.restrict_apply _ hU hs, VectorMeasure.restrict_apply _ hU hs,
    VectorMeasure.map_apply _ hF ht, VectorMeasure.map_apply _ hG ht,
    withDensityᵥ_apply (integrable_finset_sum I ha) (hF ht),
    withDensityᵥ_apply (integrable_finset_sum I hb) (hG ht),
    integral_finset_sum I (fun i hi => (ha i hi).integrableOn),
    integral_finset_sum I (fun i hi => (hb i hi).integrableOn)]
  exact Finset.sum_congr rfl row

end Burnett.Microlocal.LocalMeasureComparison
