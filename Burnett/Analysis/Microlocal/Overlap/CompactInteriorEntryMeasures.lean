import Burnett.Analysis.Microlocal.Overlap.OverlapWeightedEntryMeasures
import Burnett.Geometry.FlatRigidity.WeakCurvature

set_option autoImplicit false
set_option maxHeartbeats 3600000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Geometry.FlatRigidity (exists_smooth_cutoff_on_compact_chart)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ComplexConjugate ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- A cutoff equal to one on a compact inner target window recovers the
unweighted overlap identity for all Borel sets over that window. -/
theorem setIntegral_roundChart_eq_on_compact_interior
    (q d : CompactChartInput M)
    (hKU : q.ball.closedBall ⊆ (chartTransition q.center d.center).source)
    (hMap : MapsTo (chartTransition q.center d.center) q.ball.closedBall d.ball.closedBall)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (i j : JetSlot) (α β : JetSlot → BoundedSymbol E)
    (C : Set E) (hC : IsCompact C)
    (hInside : C ⊆ interior (chartTransition q.center d.center '' q.ball.closedBall))
    (S : Set (Chart d.ball)) (hS : MeasurableSet S) (hSC : ∀ y ∈ S, (y.1 : E) ∈ C) :
    let T := roundChartWindowMap q d hKU hMap
    (∀ (ζ : BoundedSymbol E) (_ : ContDiff ℝ ∞ (ζ : E → ℂ))
      (_ : tsupport (ζ : E → ℂ) ⊆ chartTransition q.center d.center '' q.ball.closedBall),
      (∫ p in T ⁻¹' S, ζ (T p).1 * density νq hfq p i j ∂traceMeasure νq) =
        ∫ y in S, ∑ k : JetSlot, ∑ l : JetSlot,
          ζ y.1 * conj (α k y.1) * β l y.1 * density νd hfd y k l ∂traceMeasure νd) →
    (∫ p in T ⁻¹' S, density νq hfq p i j ∂traceMeasure νq) =
      ∫ y in S, ∑ k : JetSlot, ∑ l : JetSlot,
        conj (α k y.1) * β l y.1 * density νd hfd y k l ∂traceMeasure νd := by
  intro T hWeighted
  obtain ⟨L, _, _, hL, θ, hθ, hθc, hθL, _, hOne⟩ :=
    exists_smooth_cutoff_on_compact_chart hC isOpen_interior hInside
  let a : D := ⟨θ, hθ, hθc⟩
  let ζ := physicalCoefficient a
  have hζ : ContDiff ℝ ∞ (ζ : E → ℂ) := Complex.ofRealCLM.contDiff.comp hθ
  have hζS : tsupport (ζ : E → ℂ) ⊆ chartTransition q.center d.center '' q.ball.closedBall := by
    apply (closure_mono ?_).trans (hθL.trans (hL.trans interior_subset))
    intro y hy hz
    apply hy
    change ((θ y : ℝ) : ℂ) = 0
    rw [hz, Complex.ofReal_zero]
  have hζOne (y : Chart d.ball) (hy : y ∈ S) : ζ y.1 = 1 := by
    change ((θ y.1 : ℝ) : ℂ) = 1
    rw [hOne _ (hSC y hy), Complex.ofReal_one]
  have hTS : MeasurableSet (T ⁻¹' S) :=
    (continuous_roundChartWindowMap q d hKU hMap).measurable hS
  have hLeft :
      (∫ p in T ⁻¹' S, ζ (T p).1 * density νq hfq p i j ∂traceMeasure νq) =
      ∫ p in T ⁻¹' S, density νq hfq p i j ∂traceMeasure νq := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hTS] with p hp
    rw [hζOne (T p) hp, one_mul]
  have hRight :
      (∫ y in S, ∑ k : JetSlot, ∑ l : JetSlot,
        ζ y.1 * conj (α k y.1) * β l y.1 * density νd hfd y k l ∂traceMeasure νd) =
      ∫ y in S, ∑ k : JetSlot, ∑ l : JetSlot,
        conj (α k y.1) * β l y.1 * density νd hfd y k l ∂traceMeasure νd := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hS] with y hy
    simp only [hζOne y hy, one_mul]
  exact hLeft.symm.trans ((hWeighted ζ hζ hζS).trans hRight)

end Burnett.Microlocal.Overlap
