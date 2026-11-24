import Burnett.Geometry.MaximalChart.ReceivingChartCovariantJet
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartVolumeInputs

/-! The original auxiliary derivative and the original partial derivative
have the same localized half-density inputs up to a strong L² error. -/

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Microlocal.AtlasVolumeGradient

open Filter MeasureTheory Set Burnett.RicciSymbol Burnett.Fourier
open Burnett.Geometry BackgroundConnection ConnectionDifference ManifoldMetric ManifoldMetricSequence
  ManifoldBilinear MaximalChart
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport test_memLp)
open Burnett.Analysis.HminusWeightedDual (complexTest)
open Burnett.Analysis.LocalWeakDerivative (contDiff_test_mul_local)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

private theorem fixedCovariantJet_component_smoothOn (r : Metric (M := M)) (H : Field (M := M))
    (hH : IsSmooth H) (c : AtlasChart M) (i : JetSlot) :
    ContDiffOn ℝ ∞ (fun x => fixedCovariantJet r.inner H c x i.1 i.2.1 i.2.2) c.chart.target := by
  have hConn := fixedForm_connection_smooth r.inner (isSmooth_inner r)
    (GlobalLeviCivita.inner_nondegenerate r) c
  have hΓ (a b e : Index) : ContDiffOn ℝ ∞
      (fun x => computedConnection (fixedForm r.inner c) x a b e) c.chart.target :=
    contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hConn a) b) e
  have hC := fixedForm_components_smooth H hH c
  have hJ := SmoothMetricConnection.contDiffOn_coordinateJet _ _ c.chart.open_target hC i.1 i.2.1 i.2.2
  unfold fixedCovariantJet covariantJet
  exact (hJ.sub (ContDiffOn.sum (fun a _ => (hΓ a i.1 i.2.1).mul (hC a i.2.2)))).sub
    (ContDiffOn.sum (fun a _ => (hΓ a i.1 i.2.2).mul (hC i.2.1 a)))

/-- The paper's original (D h_n), multiplied by the same fixed cutoff
and background volume half-density as the coordinate test input. -/
def fixedVolumeCovariantGradientSchwartz (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart.target)
    (n : ℕ) (i : JetSlot) : SchwartzMap CoordinateSpace ℂ :=
  let w := fixedWeightedCutoff B hB hn c χ hχ
  let hw : tsupport (w : CoordinateSpace → ℝ) ⊆ c.chart.target := tsupport_mul_subset_left.trans hχ
  let H : Field (M := M) := fun m => g n m - B m
  let f : D := ⟨fun x => (w : CoordinateSpace → ℝ) x * fixedCovariantJet r.inner H c x i.1 i.2.1 i.2.2,
    contDiff_test_mul_local c.chart.open_target (test_smooth w) hw
      (fixedCovariantJet_component_smoothOn r H (IntrinsicCov2.isSmooth_difference (g n) B (hg n) hB) c i),
    (test_compactSupport w).mul_right⟩
  complexTest f

theorem fixedVolumeCovariantGradientSchwartz_apply (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart.target)
    (n : ℕ) (i : JetSlot) (x : CoordinateSpace) :
    fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n i x =
      ((((χ : CoordinateSpace → ℝ) x * fixedHalfDensity B c x) *
        fixedCovariantJet r.inner (fun m => g n m - B m) c x i.1 i.2.1 i.2.2 : ℝ) : ℂ) := rfl

theorem fixedVolumeCovariantGradientSchwartz_intrinsic (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart.target)
    (n : ℕ) (i : JetSlot) (m : M) (hm : m ∈ c.chart.source) :
    fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n i (c.chart m) =
      ((((χ : CoordinateSpace → ℝ) (c.chart m) * fixedHalfDensity B c (c.chart m)) *
        IntrinsicCov2.tensor r.inner (fun y => g n y - B y) m
          ![chartTangentBasis c m hm i.1, chartTangentBasis c m hm i.2.1,
            chartTangentBasis c m hm i.2.2] : ℝ) : ℂ) := by
  rw [fixedVolumeCovariantGradientSchwartz_apply,
    fixedCovariantJet_intrinsic_components r _ (IntrinsicCov2.isSmooth_difference (g n) B (hg n) hB) c m hm]

theorem fixedVolumeCovariantGradientSchwartz_tsupport (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart.target)
    (n : ℕ) (i : JetSlot) :
    tsupport (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n i : CoordinateSpace → ℂ) ⊆
      tsupport (χ : CoordinateSpace → ℝ) := by
  apply closure_mono
  intro x hx
  by_contra hs
  have hz : (χ : CoordinateSpace → ℝ) x = 0 := by simpa [Function.mem_support] using hs
  exact hx (by rw [fixedVolumeCovariantGradientSchwartz_apply, hz, zero_mul, zero_mul, Complex.ofReal_zero])

private def fixedConnectionCorrection (r : Metric (M := M)) (B : Field (M := M))
    (g : ℕ → Field (M := M)) (c : AtlasChart M) (n : ℕ) (i : JetSlot) (x : CoordinateSpace) : ℝ :=
  covariantJet (computedConnection (fixedForm r.inner c) x) (fixedPerturbation B (g n) c x) 0 i.1 i.2.1 i.2.2

private theorem fixedConnectionCorrection_uniformly_zero (r : Metric (M := M)) (B : Field (M := M))
    (g : ℕ → Field (M := M)) (hconv : LocallyUniformlyConverges r g B) (c : AtlasChart M)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKt : K ⊆ c.chart.target) (i : JetSlot) :
    TendstoUniformlyOn (fun n => fixedConnectionCorrection r B g c n i) (fun _ => 0) atTop K := by
  let Γ := computedConnection (fixedForm r.inner c)
  have hΓ : ContinuousOn Γ c.chart.target :=
    (fixedForm_connection_smooth r.inner (isSmooth_inner r) (GlobalLeviCivita.inner_nondegenerate r) c).continuousOn
  obtain ⟨C, hC, hBound⟩ := (hK.image_of_continuousOn (hΓ.mono hKt)).isBounded.exists_pos_norm_le
  have h0 := fixed_components_uniform_of_physical_C0loc r g B hconv c K hK hKt
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε / (8 * C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp h0) δ hδ] with n hn x hx
  let P := fixedPerturbation B (g n) c x
  let Q := covariantJet (Γ x) P 0
  have hP : ‖P‖ < δ := by
    have h := hn x hx
    rw [dist_comm, dist_eq_norm] at h
    exact h
  have hΓx : ‖Γ x‖ ≤ C := hBound _ (mem_image_of_mem Γ hx)
  have hQ : ‖Q‖ ≤ 8 * ‖Γ x‖ * ‖P‖ := by
    simpa only [Q, norm_zero, zero_add] using
      PerturbationJet.norm_covariantJet_le (Γ x) P 0
  rw [dist_zero_left]
  change ‖Q i.1 i.2.1 i.2.2‖ < ε
  calc
    _ ≤ ‖Q‖ := (norm_le_pi_norm (Q i.1 i.2.1) i.2.2).trans
      ((norm_le_pi_norm (Q i.1) i.2.1).trans (norm_le_pi_norm Q i.1))
    _ ≤ 8 * C * δ := hQ.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hΓx (by norm_num)) hP.le (norm_nonneg _) (by positivity))
    _ < ε := by
      dsimp [δ]
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ (by positivity)).2 (by nlinarith only [hε])

omit [IsManifold Model ∞ M] [SecondCountableTopology M] in
private theorem fixedForm_difference_components (B : Field (M := M)) (g : ℕ → Field (M := M))
    (n : ℕ) (c : AtlasChart M) :
    metricComponents (fixedForm (fun m => g n m - B m) c) = fixedPerturbation B (g n) c := rfl

/-- The connection correction tends strongly to zero in the actual
coordinate (L^2) space. This uses only local (C^0) convergence. -/
theorem fixedVolumeCovariantGradient_sub_partial_tendsto_zero (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart.target)
    (i : JetSlot) :
    Tendsto (fun n => (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n i).toLp 2 volume -
      (fixedVolumeGradientSchwartz B g hB hg hn c χ hχ n i).toLp 2 volume) atTop (𝓝 0) := by
  let w := fixedWeightedCutoff B hB hn c χ hχ
  let u n := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n i
  let v n := fixedVolumeGradientSchwartz B g hB hg hn c χ hχ n i
  let e n : ComplexL2 CoordinateSpace := (u n).toLp 2 volume - (v n).toLp 2 volume
  have hw : tsupport (w : CoordinateSpace → ℝ) ⊆ tsupport (χ : CoordinateSpace → ℝ) := tsupport_mul_subset_left
  change Tendsto e atTop (𝓝 0)
  apply Burnett.P01.tendsto_weighted_localizationError_L2_zero (tsupport (w : CoordinateSpace → ℝ))
    (w : CoordinateSpace → ℝ) (test_memLp w) (fun _ hx => image_eq_zero_of_notMem_tsupport hx)
    (fun n => fixedConnectionCorrection r B g c n i)
    (fixedConnectionCorrection_uniformly_zero r B g hconv c _ (test_compactSupport w) (hw.trans hχ) i) e
  intro n
  filter_upwards [Lp.coeFn_sub ((u n).toLp 2 volume) ((v n).toLp 2 volume),
    (u n).coeFn_toLp 2 volume, (v n).coeFn_toLp 2 volume] with x hx hU hV
  rw [hx, Pi.sub_apply, hU, hV]
  simp only [u, v, fixedVolumeCovariantGradientSchwartz_apply, fixedVolumeGradientSchwartz_apply,
    show ∀ x, (w : CoordinateSpace → ℝ) x = (χ : CoordinateSpace → ℝ) x * fixedHalfDensity B c x from fun _ => rfl,
    fixedCovariantJet, fixedForm_difference_components, fixedConnectionCorrection, covariantJet, Pi.zero_apply]
  push_cast
  ring

end Burnett.Microlocal.AtlasVolumeGradient
