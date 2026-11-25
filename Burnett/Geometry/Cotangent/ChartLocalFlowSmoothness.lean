import Burnett.Geometry.Cotangent.LocalChartFieldExtension
import Burnett.Geometry.Cotangent.ScaledPicardLocalFlow

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set Filter Metric
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E] [HasContDiffBump E]

/-- A local flow that solves the chart field remains the same after cutoff
extension on a smaller neighborhood, so its original phase map is smooth. -/
theorem eventually_contDiffAt_actual_chartLocalFlow {f : E → E} {V U : Set E} {x₀ : E}
    (hV : IsOpen V) (hx₀ : x₀ ∈ V) (hf : ContDiffOn ℝ ∞ f V) (hU : U ∈ 𝓝 x₀)
    {δ : ℝ} (hδ : 0 < δ) (Ψ : E × ℝ → E) (hΨ : ContinuousAt Ψ (x₀, 0))
    (hinit : ∀ x ∈ U, Ψ (x, 0) = x)
    (hODE : ∀ x ∈ U, ∀ t ∈ Ioo (-δ) δ, HasDerivAt (fun s => Ψ (x, s)) (f (Ψ (x, t))) t) :
    ∀ᶠ p in 𝓝 (x₀, (0 : ℝ)), ContDiffAt ℝ ∞ Ψ p := by
  obtain ⟨W, hW, hxW, _, F, hF, hEq⟩ := exists_smooth_chartField_extension hV hx₀ hf
  have hΨ₀ := hinit x₀ (mem_of_mem_nhds hU)
  have hNear : Ψ ⁻¹' W ∈ 𝓝 (x₀, (0 : ℝ)) :=
    hΨ.preimage_mem_nhds (hW.mem_nhds (hΨ₀.symm ▸ hxW))
  rw [nhds_prod_eq] at hNear
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_prod_iff.mp hNear
  obtain ⟨r, hr, hB'⟩ := Metric.mem_nhds_iff.mp hB
  let U' := U ∩ A
  let δ' := min δ r
  have hδ' : 0 < δ' := lt_min hδ hr
  have hU' : U' ∈ 𝓝 x₀ := inter_mem hU hA
  have hODE' : ∀ x ∈ U', ∀ t ∈ Ioo (-δ') δ',
      HasDerivAt (fun s => Ψ (x, s)) (F (Ψ (x, t))) t := by
    intro x hx t ht
    have htδ : t ∈ Ioo (-δ) δ :=
      ⟨(neg_le_neg (min_le_left δ r)).trans_lt ht.1, ht.2.trans_le (min_le_left δ r)⟩
    have htr : t ∈ ball (0 : ℝ) r := by
      rw [Real.ball_eq_Ioo, zero_sub, zero_add]
      exact ⟨(neg_le_neg (min_le_right δ r)).trans_lt ht.1, ht.2.trans_le (min_le_right δ r)⟩
    have hψW : Ψ (x, t) ∈ W := hAB ⟨hx.2, hB' htr⟩
    rw [hEq hψW]
    exact hODE x hx.1 t htδ
  exact eventually_contDiffAt_actual_localFlow hF hU' hδ' Ψ (fun x hx => hinit x hx.1) hODE'

end Burnett.Geometry.CotangentHamiltonInitialFamily
