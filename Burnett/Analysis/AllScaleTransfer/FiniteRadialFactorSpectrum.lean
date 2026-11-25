import Burnett.Analysis.AllScaleTransfer.WeightedIntegerRadialFactor

set_option autoImplicit false
noncomputable section

namespace Burnett.A05

open Set Metric Filter
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier (radialAnnularCutoff_nonzero)
open scoped Topology

/-- The actual finitely many closed annuli containing the cut input spectrum. -/
def finiteIntegerRadialFrequencySupport (J : Finset ℤ) : Set E :=
  ⋃ j ∈ J, {ξ | (2 : ℝ)^j / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * (2 : ℝ)^j}

theorem finiteIntegerRadialFrequencySupport_compact (J : Finset ℤ) :
    IsCompact (finiteIntegerRadialFrequencySupport J) := by
  apply J.isCompact_biUnion
  intro j _
  let K : Set E := {ξ | (2 : ℝ)^j / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * (2 : ℝ)^j}
  have hClosed : IsClosed K :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  exact (isCompact_closedBall (0 : E) (2 * (2 : ℝ)^j)).of_isClosed_subset hClosed
    (fun _ hx => mem_closedBall_zero_iff.mpr hx.2)

theorem zero_notMem_finiteIntegerRadialFrequencySupport (J : Finset ℤ) :
    (0 : E) ∉ finiteIntegerRadialFrequencySupport J := by
  intro hz
  simp only [finiteIntegerRadialFrequencySupport, mem_iUnion, mem_setOf_eq, norm_zero] at hz
  obtain ⟨j, _, hlo, _⟩ := hz
  exact (not_le_of_gt (by positivity : 0 < (2 : ℝ)^j / 2)) hlo

/-- The pointwise Fourier action puts the closed support of the finite
Schwartz truncation in exactly the finite family of annuli. -/
theorem tsupport_radianFourier_finiteIntegerRadialTruncation
    (J : Finset ℤ) (ε : ℤ → ℂ) (f : SchwartzMap E ℂ) :
    tsupport (radianFourier (finiteIntegerRadialTruncation J ε f : E → ℂ)) ⊆
      finiteIntegerRadialFrequencySupport J := by
  apply closure_minimal _ (finiteIntegerRadialFrequencySupport_compact J).isClosed
  intro ξ hξ
  by_contra hn
  have hWin (j : ℤ) (hj : j ∈ J) : integerRadialWindow j ξ = 0 := by
    by_contra ne
    have h := radialAnnularCutoff_nonzero (by positivity : 0 < (2 : ℝ)^j) ne
    exact hn (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hj, h.1.le, h.2.le⟩⟩)
  have hzero : radianFourier (finiteIntegerRadialTruncation J ε f : E → ℂ) ξ = 0 := by
    rw [finiteIntegerRadialTruncation_radianFourier]
    have hz : (∑ j ∈ J, ε j * (integerRadialWindow j ξ : ℂ)) = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hWin j hj, Complex.ofReal_zero, mul_zero]
    rw [hz, zero_mul]
  exact Function.mem_support.mp hξ hzero

theorem radianFourier_finiteIntegerRadialTruncation_eventually_zero
    (J : Finset ℤ) (ε : ℤ → ℂ) (f : SchwartzMap E ℂ) :
    radianFourier (finiteIntegerRadialTruncation J ε f : E → ℂ) =ᶠ[𝓝 (0 : E)] 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h =>
    zero_notMem_finiteIntegerRadialFrequencySupport J
      (tsupport_radianFourier_finiteIntegerRadialTruncation J ε f h))

end Burnett.A05
