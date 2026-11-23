import Burnett.Analysis.GaugeProjection.ProjectedDefectLocalizationError
import Burnett.Analysis.Microlocal.VolumeWeightedChartJet
import Burnett.Geometry.IntrinsicDhMeasure

/-!
# Replace the weighted coordinate derivative by the actual covariant derivative

Both use the same compact cutoff and the background volume half-density.
The connection terms are fixed smooth coefficients times the original
undifferentiated perturbation, which tends to zero uniformly on the support.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.F05.OverlapCovariantGradient

open Filter MeasureTheory Set
open Burnett.RicciSymbol Burnett.Fourier Burnett.Geometry
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ManifoldMetricSequence Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.IntrinsicDhMeasure (coordinateDerivativeTensor)
open Burnett.F05.ChartVolumeAmplitude Burnett.F05.ChartVolumeBridge Burnett.F05.OriginalCoordinateCurl
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport test_memLp)
open Burnett.Analysis.HminusWeightedDual (complexTest)
open Burnett.Analysis.LocalWeakDerivative (contDiff_test_mul_local)
open scoped BigOperators ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem connection_smoothOn (r : Metric (M := M)) (c : M) :
    ContDiffOn ℝ ∞ (computedConnection (coordinateMetric r c)) (chartAt CoordinateSpace c).target :=
  SmoothMetricConnection.contDiffOn_coordinateBilinear_connection r.inner
    (isSmooth_inner r) (GlobalLeviCivita.inner_nondegenerate r) c

private theorem covariantComponent_smoothOn (r : Metric (M := M)) (H : Field (M := M))
    (hH : IsSmooth H) (c : M) (i : JetSlot) :
    ContDiffOn ℝ ∞ (fun x => coordinateDerivativeTensor r H c x i.1 i.2.1 i.2.2)
      (chartAt CoordinateSpace c).target := by
  have hΓ (a b d : Index) : ContDiffOn ℝ ∞
      (fun x => computedConnection (coordinateMetric r c) x a b d)
      (chartAt CoordinateSpace c).target :=
    (contDiffOn_pi.mp ((contDiffOn_pi.mp (contDiffOn_pi.mp (connection_smoothOn r c) a)) b)) d
  have hC := contDiffOn_metricComponents H hH c
  have hJ := SmoothMetricConnection.contDiffOn_coordinateJet _ _
    (chartAt CoordinateSpace c).open_target hC i.1 i.2.1 i.2.2
  unfold coordinateDerivativeTensor covariantJet
  exact (hJ.sub (ContDiffOn.sum (fun a _ => (hΓ a i.1 i.2.1).mul (hC a i.2.2)))).sub
    (ContDiffOn.sum (fun a _ => (hΓ a i.1 i.2.2).mul (hC i.2.1 a)))

/-- The localized genuine covariant derivative with the same background half-density. -/
def originalCovariantGradientSchwartz (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (c : M)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (n : ℕ) (i : JetSlot) : SchwartzMap CoordinateSpace ℂ :=
  let ψ := chartVolumeWeightedCutoff B hB hn c χ hχ
  let hψ := (chartVolumeWeightedCutoff_tsupport B hB hn c χ hχ).trans hχ
  let H : Field (M := M) := fun m => g n m - B m
  let f : D :=
    ⟨fun x => ψ.val x * coordinateDerivativeTensor r H c x i.1 i.2.1 i.2.2,
      contDiff_test_mul_local (chartAt CoordinateSpace c).open_target (test_smooth ψ) hψ
        (covariantComponent_smoothOn r H (IntrinsicCov2.isSmooth_difference (g n) B (hg n) hB) c i),
      (test_compactSupport ψ).mul_right⟩
  complexTest f

theorem originalCovariantGradientSchwartz_apply (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (c : M)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (n : ℕ) (i : JetSlot) (x : CoordinateSpace) :
    originalCovariantGradientSchwartz r B g hB hg hn c χ hχ n i x =
      ((((χ : CoordinateSpace → ℝ) x * chartHalfDensity B c x) *
        coordinateDerivativeTensor r (fun m => g n m - B m) c x i.1 i.2.1 i.2.2 : ℝ) : ℂ) :=
  rfl

def originalCovariantGradientL2 (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (c : M)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (n : ℕ) (i : JetSlot) : ComplexL2 CoordinateSpace :=
  (originalCovariantGradientSchwartz r B g hB hg hn c χ hχ n i).toLp 2 volume

private def connectionCorrection (r : Metric (M := M)) (B : Field (M := M))
    (g : ℕ → Field (M := M)) (c : M) (n : ℕ) (i : JetSlot) (x : CoordinateSpace) : ℝ :=
  let Γ := computedConnection (coordinateMetric r c) x
  (∑ a, Γ a i.1 i.2.1 * originalComponent B g c n (a, i.2.2) x) +
    ∑ a, Γ a i.1 i.2.2 * originalComponent B g c n (i.2.1, a) x

private theorem connectionCorrection_uniformly_zero (r : Metric (M := M)) (B : Field (M := M))
    (g : ℕ → Field (M := M)) (hconv : LocallyUniformlyConverges r g B) (c : M)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKt : K ⊆ (chartAt CoordinateSpace c).target)
    (i : JetSlot) :
    TendstoUniformlyOn (fun n => connectionCorrection r B g c n i) (fun _ => 0) atTop K := by
  let Γ := computedConnection (coordinateMetric r c)
  obtain ⟨C, hC, hBound⟩ := (hK.image_of_continuousOn
    ((connection_smoothOn r c).continuousOn.mono hKt)).isBounded.exists_pos_norm_le
  have hΓ (x : CoordinateSpace) (hx : x ∈ K) (a b d : Index) : ‖Γ x a b d‖ ≤ C :=
    (norm_le_pi_norm (Γ x a b) d).trans ((norm_le_pi_norm (Γ x a) b).trans
      ((norm_le_pi_norm (Γ x) a).trans (hBound _ (mem_image_of_mem _ hx))))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε / (8 * C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hSmall : ∀ᶠ n in atTop, ∀ (p : Index × Index), ∀ x ∈ K,
      ‖originalComponent B g c n p x‖ ≤ δ := by
    apply eventually_all.mpr
    intro p
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp
      (originalComponent_localUniform r B g hconv c p K hK hKt)) δ hδ] with n hn x hx
    simpa only [dist_zero_left] using (hn x hx).le
  filter_upwards [hSmall] with n hn x hx
  let f (a : Index) := Γ x a i.1 i.2.1 * originalComponent B g c n (a, i.2.2) x
  let h (a : Index) := Γ x a i.1 i.2.2 * originalComponent B g c n (i.2.1, a) x
  have hsum (F : Index → ℝ) (hF : ∀ a, ‖F a‖ ≤ C * δ) :
      ‖∑ a, F a‖ ≤ 4 * (C * δ) := by
    calc
      _ ≤ ∑ a, ‖F a‖ := norm_sum_le _ _
      _ ≤ ∑ _a : Index, C * δ := Finset.sum_le_sum (fun a _ => hF a)
      _ = _ := by simp [Index]
  have hf : ∀ a, ‖f a‖ ≤ C * δ := fun a => by
    dsimp only [f]
    rw [norm_mul]
    exact mul_le_mul (hΓ x hx a i.1 i.2.1) (hn (a, i.2.2) x hx) (norm_nonneg _) hC.le
  have hh : ∀ a, ‖h a‖ ≤ C * δ := fun a => by
    dsimp only [h]
    rw [norm_mul]
    exact mul_le_mul (hΓ x hx a i.1 i.2.2) (hn (i.2.1, a) x hx) (norm_nonneg _) hC.le
  rw [dist_zero_left]
  change ‖(∑ a, f a) + ∑ a, h a‖ < ε
  calc
    _ ≤ 4 * (C * δ) + 4 * (C * δ) :=
      (norm_add_le _ _).trans (add_le_add (hsum f hf) (hsum h hh))
    _ = (8 * C * ε) / (8 * C + 1) := by dsimp [δ]; ring
    _ < ε := (div_lt_iff₀ (by positivity)).2 (by nlinarith only [hε])

private theorem perturbationComponents (B : Field (M := M)) (g : ℕ → Field (M := M))
    (n : ℕ) (c : M) :
    metricComponents (coordinateBilinear (fun m => g n m - B m) c) =
      fun x => metricComponents (coordinateBilinear (g n) c) x -
        metricComponents (coordinateBilinear B c) x := rfl

/-- Replacing the raw derivatives by the same volume-weighted covariant
derivatives has a strongly vanishing error along the original sequence. -/
theorem originalGradient_sub_covariantGradient_tendsto_zero (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (c : M)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (i : JetSlot) :
    Tendsto (fun n => originalGradient_volumeWeightedL2 B g hB hg hn c χ hχ n i -
      originalCovariantGradientL2 r B g hB hg hn c χ hχ n i) atTop (𝓝 0) := by
  let ψ := chartVolumeWeightedCutoff B hB hn c χ hχ
  let hψ := (chartVolumeWeightedCutoff_tsupport B hB hn c χ hχ).trans hχ
  let u n := originalGradientSchwartz B g hB hg c ψ hψ n i
  let v n := originalCovariantGradientSchwartz r B g hB hg hn c χ hχ n i
  let e n : ComplexL2 CoordinateSpace := (u n).toLp 2 volume - (v n).toLp 2 volume
  change Tendsto e atTop (𝓝 0)
  apply Burnett.P01.tendsto_weighted_localizationError_L2_zero (tsupport (ψ : CoordinateSpace → ℝ))
    (ψ : CoordinateSpace → ℝ) (test_memLp ψ) (fun x hx => image_eq_zero_of_notMem_tsupport hx)
    (fun n => connectionCorrection r B g c n i)
    (connectionCorrection_uniformly_zero r B g hconv c _ (test_compactSupport ψ) hψ i) e
  intro n
  filter_upwards [Lp.coeFn_sub ((u n).toLp 2 volume) ((v n).toLp 2 volume),
    (u n).coeFn_toLp 2 volume, (v n).coeFn_toLp 2 volume] with x hx hU hV
  rw [hx, Pi.sub_apply, hU, hV]
  simp only [u, v, originalGradientSchwartz_apply_rawJet, originalCovariantGradientSchwartz_apply,
    show ∀ x, (ψ : CoordinateSpace → ℝ) x = (χ : CoordinateSpace → ℝ) x * chartHalfDensity B c x from fun _ => rfl,
    coordinateDerivativeTensor, covariantJet, perturbationComponents, connectionCorrection,
    originalComponent, Pi.sub_apply]
  push_cast
  ring

end Burnett.F05.OverlapCovariantGradient
