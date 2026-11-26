import Burnett.Geometry.Causality.FiniteCausalVolume
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [BorelSpace X]

/-- The section of a relation at its second argument. -/
def sectionAt (A : Set (X × Y)) (p : Y) : Set X := {x | (x, p) ∈ A}

/-- The volume of a section of the open chronological relation is continuous
where its containing closed relation has only a null excess. -/
theorem continuousAt_section_volume (μ : Measure X) [IsFiniteMeasure μ]
    [FirstCountableTopology Y] {I J : Set (X × Y)} (hI : IsOpen I) (hJ : IsClosed J)
    (hIJ : I ⊆ J) (p : Y) (hzero : μ (sectionAt J p \ sectionAt I p) = 0) :
    ContinuousAt (fun q => μ (sectionAt I q)) p := by
  have hsection (q : Y) : MeasurableSet (sectionAt I q) :=
    (hI.preimage (continuous_id.prodMk continuous_const)).measurableSet
  let F (q : Y) : X → ℝ≥0∞ := (sectionAt I q).indicator fun _ => 1
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun q => F q x) (𝓝 p) (𝓝 (F p x)) := by
    have hgood : ∀ᵐ x ∂μ, x ∈ (sectionAt J p \ sectionAt I p)ᶜ := compl_mem_ae_iff.mpr hzero
    filter_upwards [hgood] with x hx
    have hcont : Continuous (fun q : Y => (x, q)) := continuous_const.prodMk continuous_id
    by_cases hxI : x ∈ sectionAt I p
    · have hnear : ∀ᶠ q in 𝓝 p, x ∈ sectionAt I q :=
        (hI.preimage hcont).mem_nhds hxI
      have heq : (fun q => F q x) =ᶠ[𝓝 p] fun _ => F p x := by
        filter_upwards [hnear] with q hq
        simp only [F, indicator_of_mem hq, indicator_of_mem hxI]
      exact tendsto_const_nhds.congr' heq.symm
    · have hxJ : x ∉ sectionAt J p := fun hj => hx ⟨hj, hxI⟩
      have hnear : ∀ᶠ q in 𝓝 p, x ∉ sectionAt J q :=
        (hJ.isOpen_compl.preimage hcont).mem_nhds hxJ
      have heq : (fun q => F q x) =ᶠ[𝓝 p] fun _ => F p x := by
        filter_upwards [hnear] with q hq
        have hqI : x ∉ sectionAt I q := fun hi => hq (hIJ hi)
        simp only [F, indicator_of_notMem hqI, indicator_of_notMem hxI]
      exact tendsto_const_nhds.congr' heq.symm
  have hmeas : ∀ q, Measurable (F q) := fun q => measurable_const.indicator (hsection q)
  have hbound : ∀ q x, F q x ≤ 1 := by
    intro q x
    by_cases hx : x ∈ sectionAt I q <;> simp [F, hx]
  have hfin : (∫⁻ _ : X, 1 ∂μ) ≠ ∞ := by simp
  have hc := tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
    (Eventually.of_forall hmeas) (Eventually.of_forall fun q => Eventually.of_forall (hbound q)) hfin hlim
  have hIntegral (q : Y) : (∫⁻ x, F q x ∂μ) = μ (sectionAt I q) :=
    lintegral_indicator_one (hsection q)
  simp_rw [hIntegral] at hc
  exact hc

/-- Fubini's null-set criterion for a measurable set meeting each vertical
line in at most one point. -/
theorem measure_prod_zero_of_vertical_subsingleton {Z : Type*} {T : Type*}
    [MeasurableSpace Z] [MeasurableSpace T] (μ : Measure Z) (ν : Measure T) [NoAtoms ν]
    {A : Set (Z × T)} (hA : MeasurableSet A)
    (hline : ∀ z : Z, (Prod.mk z ⁻¹' A).Subsingleton) : μ.prod ν A = 0 :=
  Measure.measure_prod_null_of_ae_null hA (Eventually.of_forall fun z => (hline z).measure_zero ν)

end Burnett.Geometry.FiniteCausalVolume
