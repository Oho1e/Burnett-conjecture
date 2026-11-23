import Burnett.Analysis.Microlocal.Overlap.CovariantGradient
import Burnett.Analysis.Microlocal.Overlap.TransportedHalfDensityL2
import Burnett.Analysis.Microlocal.Overlap.Localization

/-!
# Transport the strong error between the two localized gradients

The two Schwartz representatives have support in the same compact chart window.
Subtraction commutes with the zero-extended half-density transport, so the
existing isometry carries their strong `L²` convergence to the target chart.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.F05.OverlapCovariantGradient

open Filter MeasureTheory Set
open Burnett.RicciSymbol Burnett.Fourier Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude Burnett.F05.ChartVolumeBridge Burnett.F05.OriginalCoordinateCurl
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.Overlap Burnett.Microlocal.OverlapGradient Burnett.Microlocal.OverlapKernel
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem transportedHalfDensitySchwartz_sub (c d : M) (K : Set CoordinateSpace)
    (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (f g : SchwartzMap CoordinateSpace ℂ) (hf : tsupport (f : CoordinateSpace → ℂ) ⊆ K)
    (hg : tsupport (g : CoordinateSpace → ℂ) ⊆ K)
    (hfg : tsupport ((f - g : SchwartzMap CoordinateSpace ℂ) : CoordinateSpace → ℂ) ⊆ K) :
    transportedHalfDensitySchwartz c d K hK hKU (f - g) hfg =
      transportedHalfDensitySchwartz c d K hK hKU f hf -
        transportedHalfDensitySchwartz c d K hK hKU g hg := by
  apply SchwartzMap.ext
  intro y
  change transportedHalfDensity c d K (f - g : SchwartzMap CoordinateSpace ℂ) y =
    transportedHalfDensity c d K f y - transportedHalfDensity c d K g y
  unfold transportedHalfDensity
  by_cases hy : y ∈ chartTransition c d '' K
  · simp only [indicator_of_mem hy, SchwartzMap.sub_apply, smul_sub]
  · simp only [indicator_of_notMem hy, sub_zero]

/-- The same Lebesgue `L²` distance before and after transport. -/
theorem transportedHalfDensitySchwartz_norm_sub_toLp (c d : M) (K : Set CoordinateSpace)
    (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (f g : SchwartzMap CoordinateSpace ℂ) (hf : tsupport (f : CoordinateSpace → ℂ) ⊆ K)
    (hg : tsupport (g : CoordinateSpace → ℂ) ⊆ K) :
    ‖(transportedHalfDensitySchwartz c d K hK hKU f hf).toLp 2 volume -
      (transportedHalfDensitySchwartz c d K hK hKU g hg).toLp 2 volume‖ =
      ‖f.toLp 2 volume - g.toLp 2 volume‖ := by
  have hfg : tsupport ((f - g : SchwartzMap CoordinateSpace ℂ) : CoordinateSpace → ℂ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hx => hxK (hf hx))
    have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport (fun hx => hxK (hg hx))
    exact hx (by simp only [SchwartzMap.sub_apply, hfx, hgx, sub_zero])
  let L := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure CoordinateSpace)
  change ‖L (transportedHalfDensitySchwartz c d K hK hKU f hf) -
    L (transportedHalfDensitySchwartz c d K hK hKU g hg)‖ = ‖L f - L g‖
  rw [← L.map_sub, ← L.map_sub, ← transportedHalfDensitySchwartz_sub c d K hK hKU f g hf hg hfg]
  exact transportedHalfDensitySchwartz_norm_toLp c d K hK hKU (f - g) hfg

/-- The Schwartz representative used by the original volume-weighted coordinate input. -/
def originalVolumeGradientSchwartz (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (c : M)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (n : ℕ) (i : JetSlot) : SchwartzMap CoordinateSpace ℂ :=
  let ψ := chartVolumeWeightedCutoff B hB hn c χ hχ
  let hψ := (chartVolumeWeightedCutoff_tsupport B hB hn c χ hχ).trans hχ
  originalGradientSchwartz B g hB hg c ψ hψ n i

theorem originalVolumeGradientSchwartz_tsupport (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (c : M)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (n : ℕ) (i : JetSlot) :
    tsupport (originalVolumeGradientSchwartz B g hB hg hn c χ hχ n i : CoordinateSpace → ℂ) ⊆
      tsupport (χ : CoordinateSpace → ℝ) := by
  apply closure_mono
  intro x hx
  by_contra hχx
  have hz : χ.val x = 0 := by simpa [Function.mem_support] using hχx
  exact hx (by rw [originalVolumeGradientSchwartz, originalGradientSchwartz_apply_rawJet,
    chartVolumeWeightedCutoff_apply, hz, zero_mul, zero_mul, Complex.ofReal_zero])

theorem originalCovariantGradientSchwartz_tsupport (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (c : M)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (n : ℕ) (i : JetSlot) :
    tsupport (originalCovariantGradientSchwartz r B g hB hg hn c χ hχ n i : CoordinateSpace → ℂ) ⊆
      tsupport (χ : CoordinateSpace → ℝ) := by
  apply closure_mono
  intro x hx
  by_contra hχx
  have hz : χ.val x = 0 := by simpa [Function.mem_support] using hχx
  exact hx (by rw [originalCovariantGradientSchwartz_apply, hz, zero_mul, zero_mul, Complex.ofReal_zero])

/-- Transport of the actual volume-weighted coordinate gradient in a compact overlap window. -/
def transportedOriginalVolumeGradientSchwartz (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (c d : M)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ K) (n : ℕ) (i : JetSlot) :
    SchwartzMap CoordinateSpace ℂ :=
  let hc := (hχ.trans hKU).trans (overlapSource_subset_chartTarget c d)
  transportedHalfDensitySchwartz c d K hK hKU
    (originalVolumeGradientSchwartz B g hB hg hn c χ hc n i)
    ((originalVolumeGradientSchwartz_tsupport B g hB hg hn c χ hc n i).trans hχ)

/-- Transport of the actual covariant gradient with the same cutoff and volume. -/
def transportedCovariantGradientSchwartz (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (c d : M)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ K) (n : ℕ) (i : JetSlot) :
    SchwartzMap CoordinateSpace ℂ :=
  let hc := (hχ.trans hKU).trans (overlapSource_subset_chartTarget c d)
  transportedHalfDensitySchwartz c d K hK hKU
    (originalCovariantGradientSchwartz r B g hB hg hn c χ hc n i)
    ((originalCovariantGradientSchwartz_tsupport r B g hB hg hn c χ hc n i).trans hχ)

theorem transportedOriginalVolumeGradient_sub_covariant_tendsto_zero (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (c d : M)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ K) (i : JetSlot) :
    Tendsto (fun n =>
      (transportedOriginalVolumeGradientSchwartz B g hB hg hn c d K hK hKU χ hχ n i).toLp 2 volume -
      (transportedCovariantGradientSchwartz r B g hB hg hn c d K hK hKU χ hχ n i).toLp 2 volume)
      atTop (𝓝 0) := by
  let hc := (hχ.trans hKU).trans (overlapSource_subset_chartTarget c d)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hNorm (n : ℕ) :
      ‖(transportedOriginalVolumeGradientSchwartz B g hB hg hn c d K hK hKU χ hχ n i).toLp 2 volume -
        (transportedCovariantGradientSchwartz r B g hB hg hn c d K hK hKU χ hχ n i).toLp 2 volume‖ =
      ‖originalGradient_volumeWeightedL2 B g hB hg hn c χ hc n i -
        originalCovariantGradientL2 r B g hB hg hn c χ hc n i‖ :=
    transportedHalfDensitySchwartz_norm_sub_toLp c d K hK hKU _ _
      ((originalVolumeGradientSchwartz_tsupport B g hB hg hn c χ hc n i).trans hχ)
      ((originalCovariantGradientSchwartz_tsupport r B g hB hg hn c χ hc n i).trans hχ)
  simp only [hNorm]
  exact tendsto_zero_iff_norm_tendsto_zero.mp
    (originalGradient_sub_covariantGradient_tendsto_zero r B g hB hg hn hconv c χ hc i)

end Burnett.F05.OverlapCovariantGradient
