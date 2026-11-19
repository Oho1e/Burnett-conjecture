import Burnett.Geometry.CompactCoordinateNorms
import Burnett.Geometry.IntrinsicRicciTrace

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.Geometry.AuxiliaryAdmissibility

open Set Filter Matrix MeasureTheory
open Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open Burnett.Geometry ManifoldMetricSequence ManifoldTensorNorm CovariantTensorNorm
open Burnett.Geometry BackgroundConnection ConnectionErrorSequence PerturbationJet IntrinsicDhMeasure
open scoped ContDiff Manifold Topology ENNReal

private theorem compact_uniform_comparison {X A : Type*} [TopologicalSpace X]
    (F G : X → A → ℝ) (hG : ∀ x a, 0 ≤ G x a)
    (hlocal : ∀ x, ∃ U ∈ 𝓝 x, ∃ C > 0, ∀ y ∈ U, ∀ a, F y a ≤ C * G y a)
    (K : Set X) (hK : IsCompact K) : ∃ C > 0, ∀ x ∈ K, ∀ a, F x a ≤ C * G x a := by
  refine IsCompact.induction_on (p := fun U =>
    ∃ C > 0, ∀ x ∈ U, ∀ a, F x a ≤ C * G x a) hK ?_ ?_ ?_ ?_
  · exact ⟨1, zero_lt_one, fun x hx => False.elim hx⟩
  · intro U V huv
    rintro ⟨C, hC, hb⟩
    exact ⟨C, hC, fun x hx a => hb x (huv hx) a⟩
  · intro U V
    rintro ⟨C, hC, hb⟩ ⟨D, hD, hd⟩
    refine ⟨max C D, hC.trans_le (le_max_left _ _), ?_⟩
    intro x hx a
    rcases hx with hx | hx
    · exact (hb x hx a).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hG _ _))
    · exact (hd x hx a).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hG _ _))
  · intro x _
    obtain ⟨U, hU, h⟩ := hlocal x
    exact ⟨U, nhdsWithin_le_nhds hU, h⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

omit [IsManifold Model ∞ M] in
private theorem exists_compact_chart_window (x : M) :
    ∃ (U : Set M), U ∈ 𝓝 x ∧ U ⊆ (chartAt CoordinateSpace x).source ∧
      ∃ K : Set CoordinateSpace, IsCompact K ∧ K ⊆ (chartAt CoordinateSpace x).target ∧
        MapsTo (chartAt CoordinateSpace x) U K := by
  let e := chartAt CoordinateSpace x
  have hx : x ∈ e.source := mem_chart_source _ x
  obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (e.open_target.mem_nhds (e.mapsTo hx))
  let U := e.source ∩ e ⁻¹' Metric.ball (e x) ε
  have hU : U ∈ 𝓝 x := inter_mem (e.open_source.mem_nhds hx)
    (e.continuousAt hx (Metric.ball_mem_nhds _ hε))
  exact ⟨U, hU, inter_subset_left, Metric.closedBall (e x) ε,
    isCompact_closedBall _ _, hsub, fun y hy => Metric.ball_subset_closedBall hy.2⟩

private theorem exists_chart_norm2_lower (r : Metric (M := M)) (c : M) (K : Set CoordinateSpace)
    (hK : IsCompact K) (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    ∃ C > 0, ∀ x ∈ K, ∀ T : Tensor2, ‖T‖ ≤ C * norm2 (metricComponents (coordinateMetric r c) x) T :=
  exists_uniform_norm2_control _ K hK
    (fun i => (ManifoldMetric.contDiffOn_metricComponents r c i i).continuousOn.mono hKt)
    (fun _ hy => ManifoldMetric.coordinateMetric_posDef r c (hKt hy))

private theorem exists_chart_norm3_lower (r : Metric (M := M)) (c : M) (K : Set CoordinateSpace)
    (hK : IsCompact K) (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    ∃ C > 0, ∀ x ∈ K, ∀ T : FirstJet, ‖T‖ ≤ C * norm3 (metricComponents (coordinateMetric r c) x) T :=
  exists_uniform_norm3_control _ K hK
    (fun i => (ManifoldMetric.contDiffOn_metricComponents r c i i).continuousOn.mono hKt)
    (fun _ hy => ManifoldMetric.coordinateMetric_posDef r c (hKt hy))

theorem physicalNorm2_compact_compare (r s : Metric (M := M)) (K : Set M) (hK : IsCompact K) :
    ∃ C > 0, ∀ x ∈ K, ∀ H : Field (M := M), physicalNorm2 s H x ≤ C * physicalNorm2 r H x := by
  apply compact_uniform_comparison (fun x H => physicalNorm2 s H x) (fun x H => physicalNorm2 r H x)
    (fun x H => physicalNorm2_nonneg r H x) _ K hK
  intro c
  obtain ⟨U, hU, hUs, L, hL, hLt, hUL⟩ := exists_compact_chart_window c
  obtain ⟨A, hA, hLow⟩ := exists_chart_norm2_lower r c L hL hLt
  obtain ⟨B, hB, hHigh⟩ := exists_chart_norm2_upper s c L hL hLt
  refine ⟨U, hU, B * A, mul_pos hB hA, ?_⟩
  intro x hx H
  let y := chartAt CoordinateSpace c x
  let e := chartAt CoordinateSpace c
  have hy : y ∈ L := hUL hx
  have hR := physicalNorm2_eq_coordinate r H c (hLt hy)
  have hS := physicalNorm2_eq_coordinate s H c (hLt hy)
  rw [e.left_inv (hUs hx)] at hR hS
  change physicalNorm2 s H x ≤ (B * A) * physicalNorm2 r H x
  rw [hR, hS, mul_assoc]
  exact (hHigh y hy _).trans (mul_le_mul_of_nonneg_left (hLow y hy _) hB.le)

theorem locallyUniformlyConverges_changeAuxiliary (r s : Metric (M := M))
    (g : ℕ → Field (M := M)) (B : Field (M := M)) (hr : LocallyUniformlyConverges r g B) :
    LocallyUniformlyConverges s g B := by
  intro K hK
  obtain ⟨C, hC, hcomp⟩ := physicalNorm2_compact_compare r s K hK
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hr K hK) (ε / C) (div_pos hε hC)] with n hn
  intro x hx
  have hsmall : physicalNorm2 r (g n - B) x < ε / C := by
    simpa only [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg (physicalNorm2_nonneg r (g n - B) x)]
      using hn x hx
  rw [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg (physicalNorm2_nonneg s (g n - B) x)]
  calc
    _ ≤ C * physicalNorm2 r (g n - B) x := hcomp x hx (g n - B)
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hsmall hC
    _ = ε := by field_simp

theorem normScalar_nonneg (r : Metric (M := M)) (H : Field (M := M)) (x : M) :
    0 ≤ normScalar r H x := ManifoldCov3Norm.physicalNorm3_nonneg r (IntrinsicCov2.tensor r.inner H) x

private theorem exists_chart_computedConnection_bound (r : Metric (M := M)) (c : M)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    ∃ C > 0, ∀ y ∈ K, ‖computedConnection (coordinateMetric r c) y‖ ≤ C := by
  have hc := (SmoothMetricConnection.contDiffOn_coordinateBilinear_connection r.inner
    (ManifoldBilinear.isSmooth_inner r) (GlobalLeviCivita.inner_nondegenerate r) c).continuousOn
  obtain ⟨C, hC, hb⟩ := (hK.image_of_continuousOn (hc.mono hKt)).isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun y hy => hb _ (mem_image_of_mem _ hy)⟩

private theorem chartDerivative_change_le (r s : Metric (M := M)) (H : Field (M := M))
    (c : M) (y : CoordinateSpace) :
    ‖coordinateDerivativeTensor s H c y‖ ≤ ‖coordinateDerivativeTensor r H c y‖ +
      (8 * (‖computedConnection (coordinateMetric r c) y‖ + ‖computedConnection (coordinateMetric s c) y‖)) *
        ‖metricComponents (coordinateBilinear H c) y‖ := by
  let T := metricComponents (coordinateBilinear H c) y
  let J := coordinateJet (metricComponents (coordinateBilinear H c)) y
  let R := computedConnection (coordinateMetric r c) y
  let S := computedConnection (coordinateMetric s c) y
  change ‖covariantJet S T J‖ ≤ ‖covariantJet R T J‖ + (8 * (‖R‖ + ‖S‖)) * ‖T‖
  calc
    _ ≤ ‖J‖ + 8 * ‖S‖ * ‖T‖ := norm_covariantJet_le S T J
    _ ≤ (‖covariantJet R T J‖ + 8 * ‖R‖ * ‖T‖) + 8 * ‖S‖ * ‖T‖ :=
      add_le_add_right (norm_rawJet_le_covariantJet R T J) _
    _ = _ := by ring

/-- On a fixed compact set, the target derivative is controlled by the
source derivative and the undifferentiated tensor, with all norms physical. -/
theorem normScalar_compact_compare (r s : Metric (M := M)) (K : Set M) (hK : IsCompact K) :
    ∃ C > 0, ∀ x ∈ K, ∀ H : Field (M := M), IsSmooth H →
      normScalar s H x ≤ C * (normScalar r H x + physicalNorm2 r H x) := by
  let A := { H : Field (M := M) // IsSmooth H }
  have h := compact_uniform_comparison
    (fun x (H : A) => normScalar s H.val x)
    (fun x (H : A) => normScalar r H.val x + physicalNorm2 r H.val x)
    (fun x H => add_nonneg (normScalar_nonneg r H.val x) (physicalNorm2_nonneg r H.val x))
    (by
      intro c
      obtain ⟨U, hU, hUs, L, hL, hLt, hUL⟩ := exists_compact_chart_window c
      obtain ⟨A2, hA2, hLow2⟩ := exists_chart_norm2_lower r c L hL hLt
      obtain ⟨A3, hA3, hLow3⟩ := exists_chart_norm3_lower r c L hL hLt
      obtain ⟨B3, hB3, hHigh3⟩ := exists_chart_norm3_upper s c L hL hLt
      obtain ⟨Gr, hGr, hΓr⟩ := exists_chart_computedConnection_bound r c L hL hLt
      obtain ⟨Gs, hGs, hΓs⟩ := exists_chart_computedConnection_bound s c L hL hLt
      let D := 8 * (Gr + Gs)
      have hD : 0 ≤ D := by dsimp [D]; positivity
      let C := B3 * (A3 + D * A2)
      have hC : 0 < C := mul_pos hB3 (add_pos_of_pos_of_nonneg hA3 (mul_nonneg hD hA2.le))
      refine ⟨U, hU, C, hC, ?_⟩
      rintro x hx ⟨H,hH⟩
      let y := chartAt CoordinateSpace c x
      let e := chartAt CoordinateSpace c
      have hy : y ∈ L := hUL hx
      have h2 := physicalNorm2_eq_coordinate r H c (hLt hy)
      rw [e.left_inv (hUs hx)] at h2
      have hR := normScalar_eq_chart r H hH c x (hUs hx)
      have hS := normScalar_eq_chart s H hH c x (hUs hx)
      have hJr : ‖coordinateDerivativeTensor r H c y‖ ≤ A3 * normScalar r H x := by
        rw [hR]
        exact hLow3 y hy _
      have hT : ‖metricComponents (coordinateBilinear H c) y‖ ≤ A2 * physicalNorm2 r H x := by
        rw [h2]
        exact hLow2 y hy _
      have hΓ : (8 : ℝ) * (‖computedConnection (coordinateMetric r c) y‖ +
          ‖computedConnection (coordinateMetric s c) y‖) ≤ D := by
        exact mul_le_mul_of_nonneg_left (add_le_add (hΓr y hy) (hΓs y hy)) (by norm_num)
      have hE := (chartDerivative_change_le r s H c y).trans
        (add_le_add hJr (mul_le_mul hΓ hT (norm_nonneg _) hD))
      have hExpand : B3 * (A3 * normScalar r H x + D * (A2 * physicalNorm2 r H x)) ≤
          C * (normScalar r H x + physicalNorm2 r H x) := by
        have hX := normScalar_nonneg r H x
        have hY := physicalNorm2_nonneg r H x
        dsimp [C]
        calc
          _ ≤ B3 * ((A3 + D * A2) * normScalar r H x + (A3 + D * A2) * physicalNorm2 r H x) := by
            apply mul_le_mul_of_nonneg_left _ hB3.le
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hD hA2.le)) hX
            · rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA3.le) hY
          _ = _ := by ring
      calc
        normScalar s H x ≤ B3 * ‖coordinateDerivativeTensor s H c y‖ := by
          rw [hS]
          exact hHigh3 y hy _
        _ ≤ _ := mul_le_mul_of_nonneg_left hE hB3.le
        _ ≤ _ := hExpand) K hK
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, fun x hx H hH => hb x hx ⟨H,hH⟩⟩

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The actual geometric-volume essential bound on first covariant
derivatives in the manuscript. -/
def CompactDhBound (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M)) : Prop :=
  ∀ K : Set M, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
    eLpNorm (normScalar r (fun m => g n m - B m)) ⊤
      ((ManifoldVolume.geometricMeasure B).restrict K) ≤ ENNReal.ofReal C

private theorem eLpNorm_top_le_of_pointwise {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {K : Set X} (hK : MeasurableSet K) (f : X → ℝ) {C : ℝ} (hf : ∀ x ∈ K, ‖f x‖ ≤ C) :
    eLpNorm f ⊤ (μ.restrict K) ≤ ENNReal.ofReal C := by
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound ((ae_restrict_mem hK).mono hf)

theorem compactDhBound_changeAuxiliary (r s : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : CompactDhBound r B g) : CompactDhBound s B g := by
  classical
  unfold CompactDhBound at hb ⊢
  intro K hK
  let μ := (ManifoldVolume.geometricMeasure B).restrict K
  let H (n : ℕ) : Field (M := M) := fun m => g n m - B m
  have hH (n : ℕ) : IsSmooth (H n) := IntrinsicCov2.isSmooth_difference (g n) B (hg n) hB
  obtain ⟨C, hC, hcomp⟩ := normScalar_compact_compare r s K hK
  obtain ⟨R, hR, hRbd⟩ := hb K hK
  have hsmall : ∀ᶠ n in atTop, ∀ x ∈ K, physicalNorm2 r (H n) x < 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hconv K hK) 1 zero_lt_one] with n hn
    intro x hx
    simpa only [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg (physicalNorm2_nonneg r (g n - B) x)]
      using hn x hx
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  have htail (n : ℕ) (hn : N ≤ n) :
      eLpNorm (normScalar s (H n)) ⊤ μ ≤ ENNReal.ofReal (C * (R + 1)) := by
    have hRae : ∀ᵐ x ∂μ, ‖normScalar r (H n) x‖ₑ ≤ eLpNorm (normScalar r (H n)) ⊤ μ := by
      rw [eLpNorm_exponent_top]
      exact ae_le_eLpNormEssSup
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [hRae, ae_restrict_mem hK.measurableSet] with x hx hxK
    have hrb := hx.trans (hRbd n)
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (normScalar_nonneg r (H n) x),
      ENNReal.ofReal_le_ofReal_iff hR] at hrb
    rw [Real.norm_eq_abs, abs_of_nonneg (normScalar_nonneg s (H n) x)]
    exact (hcomp x hxK (H n) (hH n)).trans
      (mul_le_mul_of_nonneg_left (add_le_add hrb (hN n hn x hxK).le) hC.le)
  have hprefix (i : Fin N) : ∃ D : ℝ, 0 ≤ D ∧
      eLpNorm (normScalar s (H i.val)) ⊤ μ ≤ ENNReal.ofReal D := by
    let f := normScalar s (H i.val)
    have hc : Continuous f := continuous_normScalar s _ (hH i.val)
    obtain ⟨D, hD, hDb⟩ := (hK.image_of_continuousOn hc.continuousOn).isBounded.exists_pos_norm_le
    exact ⟨D, hD.le, eLpNorm_top_le_of_pointwise hK.measurableSet f
      (fun x hx => hDb _ (mem_image_of_mem _ hx))⟩
  choose D hD using hprefix
  let P := ∑ i : Fin N, D i
  have hP : 0 ≤ P := Finset.sum_nonneg fun i _ => (hD i).1
  have hTailNonneg : 0 ≤ C * (R + 1) := mul_nonneg hC.le (by positivity)
  refine ⟨C * (R + 1) + P, add_nonneg hTailNonneg hP, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (htail n hn).trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hP))
  · let i : Fin N := ⟨n, Nat.lt_of_not_ge hn⟩
    have hi : D i ≤ P := Finset.single_le_sum (f := D) (fun j _ => (hD j).1) (Finset.mem_univ i)
    exact (hD i).2.trans (ENNReal.ofReal_le_ofReal (hi.trans (le_add_of_nonneg_left hTailNonneg)))

/-- The original analytic hypotheses, including intrinsic vacuum, are
equivalent for any two smooth auxiliary metrics on the same four-manifold
and for the very same metric sequence. -/
theorem admissible_iff_changeAuxiliary (r s : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) :
    ((∀ n, IntrinsicRicciTrace.IsVacuum (g n)) ∧ LocallyUniformlyConverges r g B ∧ CompactDhBound r B g) ↔
      ((∀ n, IntrinsicRicciTrace.IsVacuum (g n)) ∧ LocallyUniformlyConverges s g B ∧ CompactDhBound s B g) :=
  ⟨fun h => ⟨h.1, locallyUniformlyConverges_changeAuxiliary r s g B h.2.1,
      compactDhBound_changeAuxiliary r s B g hB hg h.2.1 h.2.2⟩,
    fun h => ⟨h.1, locallyUniformlyConverges_changeAuxiliary s r g B h.2.1,
      compactDhBound_changeAuxiliary s r B g hB hg h.2.1 h.2.2⟩⟩

end Burnett.Geometry.AuxiliaryAdmissibility
