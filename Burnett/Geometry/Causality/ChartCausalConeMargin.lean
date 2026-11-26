import Burnett.Geometry.Causality.ChartTimeOrientation
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.CotangentHamiltonCauchySlice

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

theorem chart_nonzero_causal_pairing {g : Field (M := M)} (hL : HasLorentzSignature g)
    (c : M) {y n v : E} (hy : y ∈ (chartAt E c).target)
    (hn : coordinateBilinear g c y n n < 0) (hv : v ≠ 0)
    (hvv : coordinateBilinear g c y v v ≤ 0) : coordinateBilinear g c y n v ≠ 0 := by
  let x := (chartAt E c).symm y
  let F := tangentFrame c x
  let B : LinearMap.BilinForm ℝ (TangentSpace Model x) := LinearMap.mk₂ ℝ
    (fun u z => g x u z) (by intros; simp [map_add]) (by intros; simp [map_smul])
    (by intros; simp [map_add]) (by intros; simp [map_smul])
  have hx : x ∈ (chartAt E c).source := (chartAt E c).symm_mapsTo hy
  have hv' : F v ≠ 0 := by
    intro h
    exact hv (tangentFrame_injective c x hx (h.trans F.map_zero.symm))
  obtain ⟨b, hb⟩ := hL x
  intro h
  exact (not_lt_of_ge hvv) (positive_of_timelike_orthogonal B b hb hn hv' h)

/-- The actual future cone has a strict angle with any fixed timelike chart
direction that remains timelike on a compact set. -/
theorem uniform_chart_causal_pairing {g : Field (M := M)} (hg : IsSmooth g)
    (hL : HasLorentzSignature g) (c : M) (n : E)
    {K : Set E} (hK : IsCompact K) (hKtarget : K ⊆ (chartAt E c).target)
    (hn : ∀ y ∈ K, coordinateBilinear g c y n n < 0) :
    ∃ a > (0 : ℝ), ∀ y ∈ K, ∀ v : E,
      coordinateBilinear g c y v v ≤ 0 → coordinateBilinear g c y n v ≤ 0 →
      coordinateBilinear g c y n v ≤ -a * ‖v‖ := by
  let B := coordinateBilinear g c
  let U := Metric.sphere (0 : E) 1
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : CompactSpace U := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  let P := K × U
  let Y : P → E := fun z => z.1.val
  let V : P → E := fun z => z.2.val
  let f : P → ℝ := fun z => B (Y z) (V z) (V z)
  let h : P → ℝ := fun z => B (Y z) n (V z)
  have hY : Continuous Y := continuous_subtype_val.comp continuous_fst
  have hV : Continuous V := continuous_subtype_val.comp continuous_snd
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun z =>
    continuousAt_actual_chart_pairing g hg c z Y V V hY.continuousAt hV.continuousAt
      hV.continuousAt (hKtarget z.1.property)
  have hh : Continuous h := continuous_iff_continuousAt.mpr fun z =>
    continuousAt_actual_chart_pairing g hg c z Y (fun _ => n) V hY.continuousAt
      continuousAt_const hV.continuousAt (hKtarget z.1.property)
  let S : Set P := {z | f z ≤ 0} ∩ {z | h z ≤ 0}
  have hS : IsCompact S := IsClosed.isCompact
    ((isClosed_le hf continuous_const).inter (isClosed_le hh continuous_const))
  have hBound : ∃ a > (0 : ℝ), ∀ z ∈ S, h z ≤ -a := by
    by_cases hSnonempty : S.Nonempty
    · obtain ⟨z, hz, hmax⟩ := hS.exists_isMaxOn hSnonempty hh.continuousOn
      have hv1 : ‖V z‖ = 1 := by
        have hzU : V z ∈ Metric.sphere (0 : E) 1 := z.2.property
        simpa only [Metric.mem_sphere, dist_zero_right] using hzU
      have hvne : V z ≠ 0 := by intro he; rw [he, norm_zero] at hv1; norm_num at hv1
      have hne : h z ≠ 0 := chart_nonzero_causal_pairing hL c (hKtarget z.1.property)
        (hn (Y z) z.1.property) hvne hz.1
      have hneg : h z < 0 := lt_of_le_of_ne hz.2 hne
      exact ⟨-h z, neg_pos.mpr hneg, fun w hw => (hmax hw).trans_eq (neg_neg _).symm⟩
    · exact ⟨1, zero_lt_one, fun z hz => (hSnonempty ⟨z, hz⟩).elim⟩
  obtain ⟨a, ha, hBound⟩ := hBound
  refine ⟨a, ha, fun y hy v hv hnV => ?_⟩
  by_cases hv0 : v = 0
  · simp [hv0]
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  let u := ‖v‖⁻¹ • v
  have hSphere : u ∈ U := by
    change u ∈ Metric.sphere (0 : E) 1
    rw [Metric.mem_sphere, dist_zero_right]
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnorm.le), inv_mul_cancel₀ hnorm.ne']
  let z : P := (⟨y, hy⟩, ⟨u, hSphere⟩)
  have hz : z ∈ S := by
    constructor
    · change B y u u ≤ 0
      simp only [u, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) hv)
    · change B y n u ≤ 0
      rw [show B y n u = ‖v‖⁻¹ * B y n v by simp [u, map_smul]]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hnV
  have hBnd : B y n u ≤ -a := hBound z hz
  rw [show B y n u = B y n v / ‖v‖ by simp [u, map_smul, div_eq_mul_inv, mul_comm]] at hBnd
  exact (div_le_iff₀ hnorm).mp hBnd

end Burnett.Geometry.FiniteCausalVolume
