import Burnett.Analysis.GaugeProjection.StrongCompactness.ProjectedMeasureZero

/-! A nonnegative integrated projected energy detects exactly its positive-weight window. -/
set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 3700000

noncomputable section
namespace Burnett.P01

open Filter MeasureTheory Matrix Burnett.A02.FrequencySplit
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ComplexOrder Matrix MatrixOrder Topology

theorem integral_projectedWeight_trace_re_eq_zero_iff
    {X : Type*} [MeasurableSpace X] (τ : Measure X) (ξ : X → E)
    (N : X → Matrix OrderedPair OrderedPair ℂ) (w : X → ℝ)
    (hw : ∀ᵐ x ∂τ, 0 ≤ w x) (hN : ∀ᵐ x ∂τ, (N x).PosSemidef)
    (hInt : Integrable (fun x => w x *
      (principalGaugeProjectionMatrix (ξ x) * N x * (principalGaugeProjectionMatrix (ξ x))ᴴ).trace.re) τ) :
    (∫ x, w x * (principalGaugeProjectionMatrix (ξ x) * N x *
      (principalGaugeProjectionMatrix (ξ x))ᴴ).trace.re ∂τ) = 0 ↔
      ∀ᵐ x ∂τ, w x ≠ 0 → principalGaugeProjectionMatrix (ξ x) * N x *
        (principalGaugeProjectionMatrix (ξ x))ᴴ = 0 := by
  let Q x := principalGaugeProjectionMatrix (ξ x) * N x * (principalGaugeProjectionMatrix (ξ x))ᴴ
  have hQ : ∀ᵐ x ∂τ, (Q x).PosSemidef := hN.mono fun x h =>
    h.mul_mul_conjTranspose_same (principalGaugeProjectionMatrix (ξ x))
  have hNonneg : ∀ᵐ x ∂τ, 0 ≤ w x * (Q x).trace.re := by
    filter_upwards [hw, hQ] with x hx hp
    exact mul_nonneg hx (Complex.nonneg_iff.mp hp.trace_nonneg).1
  change (∫ x, w x * (Q x).trace.re ∂τ) = 0 ↔ ∀ᵐ x ∂τ, w x ≠ 0 → Q x = 0
  rw [integral_eq_zero_iff_of_nonneg_ae hNonneg hInt]
  constructor
  · intro h
    filter_upwards [h, hQ] with x hx hp hwx
    have hRe : (Q x).trace.re = 0 := (mul_eq_zero.mp hx).resolve_left hwx
    have hIm : (Q x).trace.im = 0 := (Complex.nonneg_iff.mp hp.trace_nonneg).2.symm
    apply hp.trace_eq_zero_iff.mp
    exact Complex.ext hRe hIm
  · intro h
    filter_upwards [h] with x hx
    change w x * (Q x).trace.re = 0
    by_cases hwx : w x = 0
    · rw [hwx, zero_mul]
    · rw [hx hwx, trace_zero, Complex.zero_re, mul_zero]

/-- If every subsequence admits a further subsequence converging to the same
value, the whole original sequence converges to that value. -/
theorem tendsto_of_strictMono_subsequence_refinements {X : Type*} [TopologicalSpace X]
    (f : ℕ → X) (y : X)
    (h : ∀ s : ℕ → ℕ, StrictMono s → ∃ t : ℕ → ℕ, StrictMono t ∧
      Tendsto (fun n => f (s (t n))) atTop (𝓝 y)) : Tendsto f atTop (𝓝 y) := by
  rw [tendsto_def]
  intro U hU
  change ∀ᶠ n in atTop, f n ∈ U
  by_contra hn
  obtain ⟨s, hs, hout⟩ := extraction_of_frequently_atTop (not_eventually.mp hn)
  obtain ⟨t, _, ht⟩ := h s hs
  obtain ⟨n, hn⟩ := (ht.eventually hU).exists
  exact hout (t n) hn

end Burnett.P01
