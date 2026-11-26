import Burnett.Geometry.ManifoldMetric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.Geometry.CausalOrbitPulse

open Set Filter MeasureTheory
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric

variable {X : Type*}

def pulseIntegral (f : X → ℝ) (γ : ℝ → X) (I : Set ℝ) : ℝ :=
  ∫ t : ℝ, I.indicator (f ∘ γ) t

/-- The integral in affine time is unchanged by changing the time origin. -/
theorem pulseIntegral_translate (f : X → ℝ) (γ : ℝ → X) (I : Set ℝ) (d : ℝ) :
    pulseIntegral f (fun t => γ (t + d)) ((fun t : ℝ => t + d) ⁻¹' I) = pulseIntegral f γ I := by
  have hEq : (fun t : ℝ => ((fun u : ℝ => u + d) ⁻¹' I).indicator (fun u => f (γ (u + d))) t) =
      fun t : ℝ => I.indicator (f ∘ γ) (t + d) := by
    funext t
    by_cases ht : t + d ∈ I <;> simp [Set.indicator, ht]
  simpa only [pulseIntegral, Function.comp_def, hEq] using
    (integral_add_right_eq_self (μ := (volume : Measure ℝ)) (I.indicator (f ∘ γ)) d)

/-- Positive affine dilation multiplies the orbit integral by the inverse
of the dilation. The base path is the same path with the changed parameter. -/
theorem pulseIntegral_positiveScale (f : X → ℝ) (γ : ℝ → X) (I : Set ℝ) {a : ℝ} (ha : 0 < a) :
    pulseIntegral f (fun t => γ (a * t)) ((fun t : ℝ => a * t) ⁻¹' I) = a⁻¹ * pulseIntegral f γ I := by
  have hEq : (fun t : ℝ => ((fun u : ℝ => a * u) ⁻¹' I).indicator (fun u => f (γ (a * u))) t) =
      fun t : ℝ => I.indicator (f ∘ γ) (a * t) := by
    funext t
    by_cases ht : a * t ∈ I <;> simp [Set.indicator, ht]
  simpa only [pulseIntegral, Function.comp_def, hEq, abs_of_pos (inv_pos.mpr ha), smul_eq_mul] using
    Measure.integral_comp_mul_left (I.indicator (f ∘ γ)) a

variable [TopologicalSpace X]

/-- A smooth nonnegative base weight can be supported exactly in an open
strip of any continuous time function. -/
theorem exists_smooth_timeStripPulse [ChartedSpace CoordinateSpace X] [IsManifold Model ∞ X]
    [T2Space X] [SecondCountableTopology X] (T : X → ℝ) (hT : Continuous T) (a b : ℝ) :
    ∃ f : X → ℝ, ContMDiff Model 𝓘(ℝ) ∞ f ∧ (∀ x, 0 ≤ f x) ∧
      ∀ x, 0 < f x ↔ T x ∈ Ioo a b := by
  letI := ChartedSpace.locallyCompactSpace CoordinateSpace X
  obtain ⟨f, hf, hs, hnonneg⟩ := (isOpen_Ioo.preimage hT).exists_msmooth_support_eq Model
  refine ⟨f, hs, hnonneg, fun x => ?_⟩
  have he : f x ≠ 0 ↔ T x ∈ Ioo a b := by
    change x ∈ Function.support f ↔ x ∈ T ⁻¹' Ioo a b
    rw [hf]
  exact ⟨fun hp => he.mp hp.ne', fun hp => lt_of_le_of_ne (hnonneg x) (he.mpr hp).symm⟩

/-- Once an affine orbit has left the time strip on both sides, the pulse
has compact parameter support and strictly positive mass. -/
theorem pulseIntegral_pos_of_parameters (f : X → ℝ) (hf : Continuous f) (hNonneg : ∀ x, 0 ≤ f x)
    (γ : ℝ → X) {I : Set ℝ} (hI : IsOpen I) (hγ : ContinuousOn γ I) {a b t₀ : ℝ}
    (hSub : Icc a b ⊆ I) (ht₀ : t₀ ∈ Icc a b) (h0 : f (γ t₀) ≠ 0)
    (hOutside : ∀ t ∈ I, t ∉ Icc a b → f (γ t) = 0) :
    let h := I.indicator (f ∘ γ)
    Continuous h ∧ HasCompactSupport h ∧ 0 < pulseIntegral f γ I := by
  intro h
  have hZero (t : ℝ) (ht : t ∉ Icc a b) : h t = 0 := by
    by_cases hIn : t ∈ I
    · rw [show h t = f (γ t) from indicator_of_mem hIn _]
      exact hOutside t hIn ht
    · exact indicator_of_notMem hIn _
  have hComp : HasCompactSupport h := isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal (fun t ht => by by_contra he; exact ht (hZero t he)) isClosed_Icc)
  have hCont : Continuous h := continuous_iff_continuousAt.mpr fun t => by
    by_cases ht : t ∈ I
    · have hNear : ∀ᶠ s in 𝓝 t, s ∈ I := hI.mem_nhds ht
      have hEq : h =ᶠ[𝓝 t] f ∘ γ := hNear.mono fun s hs => indicator_of_mem hs _
      exact (hf.continuousAt.comp ((hγ t ht).continuousAt (hI.mem_nhds ht))).congr hEq.symm
    · have hne : t ∉ Icc a b := fun hc => ht (hSub hc)
      have hNear : ∀ᶠ s in 𝓝 t, s ∉ Icc a b := isClosed_Icc.isOpen_compl.mem_nhds hne
      have hEq : h =ᶠ[𝓝 t] (fun _ => 0) := hNear.mono hZero
      exact continuousAt_const.congr hEq.symm
  have hh : 0 ≤ h := fun t => indicator_nonneg (fun t _ => hNonneg (γ t)) t
  have ht : h t₀ ≠ 0 := by simpa only [h, indicator_of_mem (hSub ht₀), Function.comp_apply] using h0
  exact ⟨hCont, hComp, hCont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hComp hh ht⟩

end Burnett.Geometry.CausalOrbitPulse
