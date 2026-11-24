import Burnett.Analysis.Microlocal.OriginalVolumeMatrixMeasure
import Burnett.Analysis.Microlocal.ChartDensitySymmetry
import Burnett.Analysis.Microlocal.CompactFrequencyCutoff
import Burnett.Analysis.MeasureWeakRicci

set_option autoImplicit false
noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricTransition
open Burnett.F05.ChartVolumeAmplitude Burnett.F05.ChartVolumeBridge Burnett.F05.OriginalCoordinateCurl
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly Burnett.Microlocal.MatrixTraceDensity
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.FixedSubsequenceSeparableExtension
open Burnett.Microlocal.SeparablePositive
open Burnett.Microlocal.FixedChartGeometricDensity (unitChartSymbol)
open Burnett.Microlocal.CompactFrequencyCutoff (smoothCutoffSymbol)
open Burnett.X02.SobolevTestJet (D Space test_smooth)
open Burnett.Analysis.LocalWeakRicciIdentification (coordinateMeasure_test_integral_eq)
open scoped ContDiff Topology Manifold InnerProduct

private theorem singleton_spatial_action (a : BoundedSymbol Space) (v : ComplexL2 Space) :
    finiteSeparableOperator (fun _ : Unit => a) (fun _ => unitChartSymbol) v = symbolL2 a v := by
  have h (u : ComplexL2 Space) : symbolL2 unitChartSymbol u = u := by
    apply Lp.ext
    filter_upwards [symbolL2_ae unitChartSymbol u] with x hx
    simpa only [unitChartSymbol, one_mul] using hx
  have hu : fourierMultiplier unitChartSymbol v = v := by
    rw [fourierMultiplier_apply, h, fourierL2Equiv.symm_apply_apply]
  simp only [finiteSeparableOperator, Finset.univ_unique, Finset.sum_singleton, separableOperator,
    ContinuousLinearMap.comp_apply, hu]
  rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The original ordered raw component product is tested against the coordinate volume.
The two half-densities give exactly one volume density, with the square of the actual cutoff.
The same original trace, density and subsequence reappear on the right. -/
theorem original_cutoff_products_of_represented
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B)
    (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (q : CompactChartInput M)
    (σ : ℕ → ℕ) (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (φ : D) (i j : JetSlot) :
    let J := fun (n : ℕ) (k : JetSlot) (x : Space) =>
      coordinateJet (fun y => metricComponents (coordinateBilinear (g n) q.center) y -
        metricComponents (coordinateBilinear B q.center) y) x k.1 k.2.1 k.2.2
    Tendsto (fun n => Complex.ofReal (∫ x, (φ : Space → ℝ) x * ((q.cutoff : Space → ℝ) x)^2 *
      (J (σ n) i x * J (σ n) j x) ∂ManifoldVolume.coordinateMeasure B q.center))
      atTop (𝓝 (∫ z, ((φ : Space → ℝ) z.1 : ℂ) * density ν hf z i j ∂traceMeasure ν)) := by
  intro J
  let χ := (q.cutoff : Space → ℝ)
  let a := smoothCutoffSymbol φ
  let w := originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
    (q.cutoff_support.trans q.ball_in_chart)
  have ha : Continuous (a : Space → ℂ) := Complex.continuous_ofReal.comp (test_smooth φ).continuous
  have hm : ContDiffOn ℝ ∞ (unitChartSymbol : Space → ℂ) ({0}ᶜ : Set Space) := contDiffOn_const
  have hd : DegreeZero (unitChartSymbol : Space → ℂ) := fun _ _ _ => rfl
  have hrest (z : Chart q.ball) :
      finiteSmoothRestriction q.ball (fun _ : Unit => a) (fun _ => unitChartSymbol)
        (fun _ => ha) (fun _ => hm) z = ((φ : Space → ℝ) z.1 : ℂ) := by
    rcases z with ⟨x,ξ⟩
    rw [finiteSmoothRestriction_apply]
    simp [a, smoothCutoffSymbol, unitChartSymbol]
  have htarget := hRep.2.2.2.2.2.2 Unit (fun _ => a) (fun _ => unitChartSymbol)
    (fun _ => ha) (fun _ => hm) (fun _ => hd) i j
  simp only [hrest, singleton_spatial_action] at htarget
  refine htarget.congr (fun n => ?_)
  change inner ℂ (w (σ n) i) (symbolL2 a (w (σ n) j)) =
    Complex.ofReal (∫ x, (φ : Space → ℝ) x * χ x ^ 2 * (J (σ n) i x * J (σ n) j x)
      ∂ManifoldVolume.coordinateMeasure B q.center)
  have hmult (x : Space) : (φ : Space → ℝ) x * χ x ^ 2 * (J (σ n) i x * J (σ n) j x) =
      χ x * ((φ : Space → ℝ) x * χ x * (J (σ n) i x * J (σ n) j x)) := by ring
  simp_rw [hmult]
  rw [coordinateMeasure_test_integral_eq B hB q.center (q.cutoff_support.trans q.ball_in_chart),
    ← integral_complex_ofReal, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [symbolL2_ae a (w (σ n) j),
    originalGradient_volumeWeightedL2_ae B g hB hg hn q.center q.cutoff
      (q.cutoff_support.trans q.ball_in_chart) (σ n) i,
    originalGradient_volumeWeightedL2_ae B g hB hg hn q.center q.cutoff
      (q.cutoff_support.trans q.ball_in_chart) (σ n) j] with x hax hix hjx
  change (w (σ n) i : Space → ℂ) x = _ at hix
  change (w (σ n) j : Space → ℂ) x = _ at hjx
  rw [hax, hix, hjx]
  have hvol : Real.sqrt |Matrix.det (metricComponents (coordinateBilinear B q.center) x)| =
      (chartHalfDensity B q.center x)^2 := by
    simp only [chartHalfDensity, Real.sq_sqrt (Real.sqrt_nonneg _)]
  rw [hvol]
  simp only [RCLike.inner_apply, originalGradientSchwartz_apply_rawJet,
    map_mul, Complex.conj_ofReal]
  change _ = (((χ x * chartHalfDensity B q.center x ^ 2) *
      ((φ : Space → ℝ) x * χ x * (J (σ n) i x * J (σ n) j x)) : ℝ) : ℂ)
  change ((φ : Space → ℝ) x : ℂ) * ((chartHalfDensity B q.center x : ℂ) *
      ((χ x * J (σ n) j x : ℝ) : ℂ)) *
      ((chartHalfDensity B q.center x : ℂ) * ((χ x * J (σ n) i x : ℝ) : ℂ)) = _
  push_cast
  ring

end Burnett.Microlocal.Overlap
