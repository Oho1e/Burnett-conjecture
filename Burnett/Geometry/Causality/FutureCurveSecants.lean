import Burnett.Geometry.Causality.ChartChronologicalSteps
import Burnett.Geometry.IntrinsicCov2
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option maxHeartbeats 3800000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter Bundle
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The secant slopes of a differentiable curve with future timelike velocity
remain in the future timelike cone as the adjacent endpoints approach. -/
theorem eventually_future_chords_of_chart_derivative {g : Field (M := M)}
    (hg : IsSmooth g) (o : TimeOrientation g) (c : M) (γ : ℝ → CoordinateSpace)
    (s : ℝ) (v : CoordinateSpace) (hγ : HasDerivAt γ v s)
    (hv : (γ s, v) ∈ futureChartVelocities o c) :
    ∀ᶠ t in 𝓝[≠] s,
      (s < t → (γ s, γ t) ∈ futureCoordinateChords o c) ∧
      (t < s → (γ t, γ s) ∈ futureCoordinateChords o c) := by
  obtain ⟨U, hU, V, hV, hCone⟩ := mem_nhds_prod_iff.mp ((isOpen_futureChartVelocities hg o c).mem_nhds hv)
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp hU
  let W := Metric.ball (γ s) r
  have hs : γ s ∈ W := Metric.mem_ball_self hr
  have hNear : ∀ᶠ t in 𝓝 s, γ t ∈ W :=
    hγ.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hs)
  have hSlope : ∀ᶠ t in 𝓝[≠] s, slope γ s t ∈ V :=
    hasDerivAt_iff_tendsto_slope.mp hγ hV
  filter_upwards [hNear.filter_mono nhdsWithin_le_nhds, hSlope] with t ht htv
  have hSec (hne : t ≠ s) : (t - s) • slope γ s t = γ t - γ s := by
    rw [slope_def_module, smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hne), one_smul]
  constructor
  · intro hst u hu
    have hY : AffineMap.lineMap (γ s) (γ t) u ∈ W := by
      apply (convex_ball (γ s) r).segment_subset hs ht
      rw [segment_eq_image_lineMap]
      exact mem_image_of_mem _ hu
    have hPair : (AffineMap.lineMap (γ s) (γ t) u, slope γ s t) ∈ futureChartVelocities o c :=
      hCone (show (_, _) ∈ U ×ˢ V from ⟨hBall hY, htv⟩)
    rw [← hSec (ne_of_gt hst)]
    exact futureChartVelocity_smul o c hPair (sub_pos.mpr hst)
  · intro hts u hu
    have hY : AffineMap.lineMap (γ t) (γ s) u ∈ W := by
      apply (convex_ball (γ s) r).segment_subset ht hs
      rw [segment_eq_image_lineMap]
      exact mem_image_of_mem _ hu
    have hPair : (AffineMap.lineMap (γ t) (γ s) u, slope γ s t) ∈ futureChartVelocities o c :=
      hCone (show (_, _) ∈ U ×ˢ V from ⟨hBall hY, htv⟩)
    have hrev : (s - t) • slope γ s t = γ s - γ t := by
      rw [← neg_sub t s, neg_smul, hSec (ne_of_lt hts), neg_sub]
    rw [← hrev]
    exact futureChartVelocity_smul o c hPair (sub_pos.mpr hts)

/-- The adjacent chart chronology follows from the actual tangent velocity
of an intrinsic future timelike curve at the central time. -/
theorem eventually_chartChronology_of_intrinsic_derivative {g : Field (M := M)}
    (hg : IsSmooth g) (o : TimeOrientation g) (γ : ℝ → M) (s : ℝ)
    (v : TangentSpace Model (γ s))
    (hγ : HasMFDerivAt 𝓘(ℝ) Model γ s ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (hv : g (γ s) v v < 0) (hfuture : g (γ s) (o.vector (γ s)) v < 0) :
    ∀ᶠ t in 𝓝[≠] s, (s < t → (γ s, γ t) ∈ chartChronology o) ∧
      (t < s → (γ t, γ s) ∈ chartChronology o) := by
  let c := γ s
  let e := chartAt CoordinateSpace c
  have hc : c ∈ e.source := mem_chart_source CoordinateSpace c
  let T := (trivializationAt CoordinateSpace (TangentSpace Model) c).continuousLinearEquivAt ℝ c hc
  let w := T v
  have hw : tangentFrame c c w = v := T.symm_apply_apply v
  have hy : e c ∈ e.target := e.mapsTo hc
  have hd : HasDerivAt (e ∘ γ) w s := by
    have hChart : MDifferentiableAt Model Model e (γ s) :=
      (mdifferentiable_chart (I := Model) c).mdifferentiableAt hc
    have hComp := hChart.hasMFDerivAt.comp s hγ
    have hValue : (mfderiv Model Model e (γ s)) v = w := by
      rw [← hw]
      exact IntrinsicCov2.mfderiv_chart_tangentFrame c c hc w
    convert hComp.hasFDerivAt.hasDerivAt using 1
    change w = (mfderiv Model Model e (γ s)) ((1 : ℝ) • v)
    rw [one_smul]
    exact hValue.symm
  have hVel : (e c, w) ∈ futureChartVelocities o c := by
    refine ⟨hy, ?_, ?_⟩
    · change g (e.symm (e c)) (tangentFrame c (e.symm (e c)) w) (tangentFrame c (e.symm (e c)) w) < 0
      rw [e.left_inv hc, hw]
      exact hv
    · change g (e.symm (e c))
        (tangentFrame c (e.symm (e c)) (ChartVectorField.coordinateVector o.vector c (e c)))
        (tangentFrame c (e.symm (e c)) w) < 0
      rw [ChartVectorField.tangentFrame_coordinateVector o.vector c hy, e.left_inv hc, hw]
      exact hfuture
  have hSrc : ∀ᶠ t in 𝓝 s, γ t ∈ e.source :=
    hγ.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hc)
  filter_upwards [hSrc.filter_mono nhdsWithin_le_nhds,
    eventually_future_chords_of_chart_derivative hg o c (e ∘ γ) s w hd hVel] with t ht hsec
  exact ⟨fun hs => Relation.TransGen.single ⟨c, hc, ht, hsec.1 hs⟩,
    fun hs => Relation.TransGen.single ⟨c, ht, hc, hsec.2 hs⟩⟩

end Burnett.Geometry.FiniteCausalVolume
