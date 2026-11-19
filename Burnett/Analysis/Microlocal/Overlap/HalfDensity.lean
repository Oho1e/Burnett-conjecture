import Burnett.Analysis.LocalWeakDerivative
import Burnett.Analysis.Sobolev.TestJet
import Burnett.Geometry.SmoothMetricConnection
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Chart half-densities and conversion of geometric volume pairings to Lebesgue pairings.
-/

set_option autoImplicit false
noncomputable section

namespace Burnett.F05.ChartVolumeBridge

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Manifold Topology
open Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition
open Burnett.X02.SobolevTestJet

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- The factor that identifies scalar chart L² pairings with Lebesgue pairings. -/
def chartHalfDensity (B : Field (M := M)) (c : M) (x : CoordinateSpace) : ℝ :=
  Real.sqrt (Real.sqrt |Matrix.det (metricComponents (coordinateBilinear B c) x)|)

theorem chartHalfDensity_pos (B : Field (M := M)) (hB : IsNondegenerate B) (c : M)
    {x : CoordinateSpace} (hx : x ∈ (chartAt CoordinateSpace c).target) :
    0 < chartHalfDensity B c x :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (abs_pos.mpr
    (ManifoldVolumeRegularity.coordinate_det_ne_zero B hB c hx)))

theorem chartHalfDensity_sq (B : Field (M := M)) (c : M) (x : CoordinateSpace) :
    (chartHalfDensity B c x) ^ 2 =
      (LorentzVolume.density (metricComponents (coordinateBilinear B c)) x).toReal := by
  simp only [chartHalfDensity, LorentzVolume.density,
    Real.sq_sqrt (Real.sqrt_nonneg _), ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

theorem chartHalfDensity_smoothOn (B : Field (M := M)) (hs : IsSmooth B)
    (hn : IsNondegenerate B) (c : M) :
    ContDiffOn ℝ ∞ (chartHalfDensity B c) (chartAt CoordinateSpace c).target := by
  let U := (chartAt CoordinateSpace c).target
  let D₀ (x : CoordinateSpace) := Matrix.det (metricComponents (coordinateBilinear B c) x)
  have hD₀ : ContDiffOn ℝ ∞ D₀ U :=
    SmoothMetricConnection.contDiffOn_det _ U (contDiffOn_metricComponents B hs c)
  have hpos (x : CoordinateSpace) (hx : x ∈ U) : 0 < |D₀ x| :=
    abs_pos.mpr (ManifoldVolumeRegularity.coordinate_det_ne_zero B hn c hx)
  have ha : ContDiffOn ℝ ∞ (fun y => |D₀ y|) U :=
    hD₀.abs (fun x hx => ManifoldVolumeRegularity.coordinate_det_ne_zero B hn c hx)
  exact (ha.sqrt fun x hx => (hpos x hx).ne').sqrt
    (fun x hx => (Real.sqrt_pos.mpr (hpos x hx)).ne')

/-- The globally smooth compact test formed from the fixed local cutoff
and the actual chart half density. -/
def chartVolumeWeightedCutoff (B : Field (M := M)) (hs : IsSmooth B)
    (hn : IsNondegenerate B) (c : M) (χ : D)
    (hχ : tsupport (χ : Space → ℝ) ⊆ (chartAt CoordinateSpace c).target) : D :=
  ⟨fun x => (χ : Space → ℝ) x * chartHalfDensity B c x,
    ⟨Burnett.Analysis.LocalWeakDerivative.contDiff_test_mul_local
      (chartAt CoordinateSpace c).open_target (test_smooth χ) hχ
      (chartHalfDensity_smoothOn B hs hn c), (test_compactSupport χ).mul_right⟩⟩

theorem chartVolumeWeightedCutoff_apply (B : Field (M := M)) (hs : IsSmooth B)
    (hn : IsNondegenerate B) (c : M) (χ : D)
    (hχ : tsupport (χ : Space → ℝ) ⊆ (chartAt CoordinateSpace c).target) (x : CoordinateSpace) :
    (chartVolumeWeightedCutoff B hs hn c χ hχ : Space → ℝ) x =
      (χ : Space → ℝ) x * chartHalfDensity B c x := rfl

theorem chartVolumeWeightedCutoff_tsupport (B : Field (M := M)) (hs : IsSmooth B)
    (hn : IsNondegenerate B) (c : M) (χ : D)
    (hχ : tsupport (χ : Space → ℝ) ⊆ (chartAt CoordinateSpace c).target) :
    tsupport (chartVolumeWeightedCutoff B hs hn c χ hχ : Space → ℝ) ⊆
      tsupport (χ : Space → ℝ) :=
  tsupport_mul_subset_left

/-- Equality of scalar complex pairings with the actual coordinate volume
on an arbitrary measurable subset of the open chart target. -/
theorem coordinateMeasure_setIntegral_inner_eq_halfDensity
    (B : Field (M := M)) (hs : IsSmooth B) (c : M)
    (S : Set CoordinateSpace) (hS : MeasurableSet S) (hSU : S ⊆ (chartAt CoordinateSpace c).target)
    (f h : CoordinateSpace → ℂ) :
    (∫ x in S, inner ℂ (f x) (h x) ∂(ManifoldVolume.coordinateMeasure B c)) =
      ∫ x in S, inner ℂ
        ((chartHalfDensity B c x : ℂ) * f x) ((chartHalfDensity B c x : ℂ) * h x) := by
  let G := metricComponents (coordinateBilinear B c)
  have hm := LorentzVolume.aemeasurable_density_restrict (volume : Measure CoordinateSpace) G S hS
    ((continuousOn_components B hs c).mono hSU)
  have hfinite : ∀ᵐ x ∂(volume : Measure CoordinateSpace).restrict S,
      LorentzVolume.density G x < (⊤ : ℝ≥0∞) :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have he := setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hm hfinite
    (fun x => inner ℂ (f x) (h x)) hS
  calc
    _ = ∫ x in S, (LorentzVolume.density G x).toReal • inner ℂ (f x) (h x) := he
    _ = _ := by
      refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
      change (LorentzVolume.density G x).toReal • inner ℂ (f x) (h x) =
        inner ℂ ((chartHalfDensity B c x : ℂ) * f x) ((chartHalfDensity B c x : ℂ) * h x)
      rw [← chartHalfDensity_sq B c x, Complex.real_smul]
      simp only [RCLike.inner_apply, Complex.ofReal_pow, map_mul, Complex.conj_ofReal]
      ring

/-- A continuous scalar component supported in a compact part of the
actual chart has finite coordinate-volume Lᵖ norm. -/
theorem coordinateMeasure_memLp_of_compact_support
    (B : Field (M := M)) (hs : IsSmooth B) (c : M) {f : CoordinateSpace → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f)
    (hU : tsupport f ⊆ (chartAt CoordinateSpace c).target) (p : ℝ≥0∞) :
    MemLp f p (ManifoldVolume.coordinateMeasure B c) := by
  have htop := hf.memLp_top_of_hasCompactSupport hc (ManifoldVolume.coordinateMeasure B c)
  exact htop.mono_exponent_of_measure_support_ne_top
    (fun _ hx => image_eq_zero_of_notMem_tsupport hx)
    (ManifoldVolumeRegularity.coordinateMeasure_compact_lt_top B hs c hc hU).ne le_top

/-- The corresponding identity in the actual complex L² spaces of the
restricted measures, when their four representatives are square integrable. -/
theorem coordinateMeasure_restrict_L2_inner_eq_halfDensity
    (B : Field (M := M)) (hs : IsSmooth B) (c : M)
    (S : Set CoordinateSpace) (hS : MeasurableSet S) (hSU : S ⊆ (chartAt CoordinateSpace c).target)
    (f h : CoordinateSpace → ℂ)
    (hf : MemLp f 2 ((ManifoldVolume.coordinateMeasure B c).restrict S))
    (hh : MemLp h 2 ((ManifoldVolume.coordinateMeasure B c).restrict S))
    (hf' : MemLp (fun x => (chartHalfDensity B c x : ℂ) * f x) 2 (volume.restrict S))
    (hh' : MemLp (fun x => (chartHalfDensity B c x : ℂ) * h x) 2 (volume.restrict S)) :
    inner ℂ (hf.toLp f) (hh.toLp h) =
      inner ℂ (hf'.toLp (fun x => (chartHalfDensity B c x : ℂ) * f x))
        (hh'.toLp (fun x => (chartHalfDensity B c x : ℂ) * h x)) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x in S, inner ℂ (f x) (h x) ∂(ManifoldVolume.coordinateMeasure B c) := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, hh.coeFn_toLp] with x hfx hhx
      rw [hfx, hhx]
    _ = ∫ x in S, inner ℂ ((chartHalfDensity B c x : ℂ) * f x)
        ((chartHalfDensity B c x : ℂ) * h x) :=
      coordinateMeasure_setIntegral_inner_eq_halfDensity B hs c S hS hSU f h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf'.coeFn_toLp, hh'.coeFn_toLp] with x hfx hhx
      rw [hfx, hhx]

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- Preferred-chart pullback of a geometric base-volume scalar pairing,
followed by the actual coordinate half-density transform. -/
theorem geometricMeasure_chartSource_inner_eq_halfDensity
    (B : Field (M := M)) (hs : IsSmooth B) (c : M)
    (f h : M → ℂ)
    (hm : AEStronglyMeasurable (fun m => inner ℂ (f m) (h m))
      ((ManifoldVolume.geometricMeasure B).restrict (chartAt CoordinateSpace c).source)) :
    (∫ m in (chartAt CoordinateSpace c).source, inner ℂ (f m) (h m)
      ∂(ManifoldVolume.geometricMeasure B)) =
      ∫ x in (chartAt CoordinateSpace c).target, inner ℂ
        ((chartHalfDensity B c x : ℂ) * f ((chartAt CoordinateSpace c).symm x))
        ((chartHalfDensity B c x : ℂ) * h ((chartAt CoordinateSpace c).symm x)) := by
  let e := chartAt CoordinateSpace c
  have ht : MeasurableSet e.target := e.open_target.measurableSet
  have hmap :
      (ManifoldVolume.geometricMeasure B).restrict e.source =
        Measure.map (ManifoldVolume.inverseChart c)
          ((ManifoldVolume.coordinateMeasure B c).restrict e.target) :=
    ManifoldVolume.geometricMeasure_restrict B c
  change (∫ m, inner ℂ (f m) (h m) ∂((ManifoldVolume.geometricMeasure B).restrict e.source)) = _
  rw [hmap] at hm ⊢
  rw [integral_map (ManifoldVolume.measurable_inverseChart c).aemeasurable hm]
  calc
    _ = ∫ x in e.target, inner ℂ (f (e.symm x)) (h (e.symm x))
          ∂(ManifoldVolume.coordinateMeasure B c) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem ht] with x hx
      rw [ManifoldVolume.inverseChart_of_mem c hx]
    _ = _ := coordinateMeasure_setIntegral_inner_eq_halfDensity B hs c e.target ht
      Subset.rfl (f ∘ e.symm) (h ∘ e.symm)

end Burnett.F05.ChartVolumeBridge
