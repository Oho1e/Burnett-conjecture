import Burnett.Analysis.Microlocal.Overlap.RepresentedCoordinateProducts

set_option autoImplicit false
noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricTransition
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density integrable_density_entry)
open Burnett.X02.SobolevTestJet (D Space test_smooth test_compactSupport)
open Burnett.Analysis.LocalWeakDerivative (contDiff_test_mul_local)
open scoped ContDiff Topology Manifold

/-- A compact test supported on a nonzero cutoff locus divided by the cutoff squared. -/
def inverseSquareTest (χ φ : D)
    (hs : tsupport (φ : Space → ℝ) ⊆ {x | (χ : Space → ℝ) x ≠ 0}) : D := by
  let U : Set Space := {x | (χ : Space → ℝ) x ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage (test_smooth χ).continuous
  have hInv : ContDiffOn ℝ ∞ (fun x => ((χ : Space → ℝ) x ^ 2)⁻¹) U :=
    ((test_smooth χ).pow 2).contDiffOn.inv (fun _ hx => pow_ne_zero 2 hx)
  exact ⟨fun x => (φ : Space → ℝ) x * ((χ : Space → ℝ) x ^ 2)⁻¹,
    contDiff_test_mul_local hU (test_smooth φ) hs hInv, (test_compactSupport φ).mul_right⟩

private theorem inverseSquareTest_cancel (χ φ : D)
    (hs : tsupport (φ : Space → ℝ) ⊆ {x | (χ : Space → ℝ) x ≠ 0}) (x : Space) :
    (inverseSquareTest χ φ hs : Space → ℝ) x * (χ : Space → ℝ) x ^ 2 = (φ : Space → ℝ) x := by
  change (φ : Space → ℝ) x * ((χ : Space → ℝ) x ^ 2)⁻¹ * (χ : Space → ℝ) x ^ 2 = _
  by_cases hx : (φ : Space → ℝ) x = 0
  · simp [hx]
  · have hχ := hs (subset_tsupport (φ : Space → ℝ) hx)
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hχ), mul_one]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Remove the squared cutoff under a compact test within its nonzero set,
keeping the original subsequence and the original ordered density. -/
theorem original_products_of_represented_on_nonzero_cutoff
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B)
    (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (q : CompactChartInput M)
    (σ : ℕ → ℕ) (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (φ : D) (hφ : tsupport (φ : Space → ℝ) ⊆ {x | (q.cutoff : Space → ℝ) x ≠ 0})
    (i j : JetSlot) :
    let J := fun (n : ℕ) (k : JetSlot) (x : Space) =>
      coordinateJet (fun y => metricComponents (coordinateBilinear (g n) q.center) y -
        metricComponents (coordinateBilinear B q.center) y) x k.1 k.2.1 k.2.2
    Integrable (fun z => ((φ : Space → ℝ) z.1 * ((q.cutoff : Space → ℝ) z.1 ^ 2)⁻¹) *
      (density ν hf z i j).re) (traceMeasure ν) ∧
    Tendsto (fun n => ∫ x, (φ : Space → ℝ) x * (J (σ n) i x * J (σ n) j x)
      ∂ManifoldVolume.coordinateMeasure B q.center) atTop
      (𝓝 (∫ z, ((φ : Space → ℝ) z.1 * ((q.cutoff : Space → ℝ) z.1 ^ 2)⁻¹) *
        (density ν hf z i j).re ∂traceMeasure ν)) := by
  intro J
  let ψ := inverseSquareTest q.cutoff φ hφ
  have hlim := original_cutoff_products_of_represented B g hB hg hn q σ ν hf hRep ψ i j
  have hreal := (Complex.continuous_re.tendsto _).comp hlim
  let a (z : Chart q.ball) : ℂ := ((ψ : Space → ℝ) z.1 : ℂ)
  have ha : Continuous a := Complex.continuous_ofReal.comp
    ((test_smooth ψ).continuous.comp (continuous_subtype_val.comp continuous_fst))
  obtain ⟨C, hC⟩ := (isCompact_univ.image ha).isBounded.exists_norm_le
  have hI : Integrable (fun z => a z * density ν hf z i j) (traceMeasure ν) :=
    (integrable_density_entry ν hf i j).bdd_mul ha.measurable.aestronglyMeasurable
      ⟨C, fun z => hC (a z) (mem_image_of_mem a (mem_univ z))⟩
  have hTest (x : Space) : (ψ : Space → ℝ) x =
      (φ : Space → ℝ) x * ((q.cutoff : Space → ℝ) x ^ 2)⁻¹ := rfl
  refine ⟨?_, ?_⟩
  · simpa only [RCLike.re_to_complex, a, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      hTest, zero_mul, sub_zero] using hI.re
  change Tendsto (fun n => (Complex.ofReal (∫ x, (ψ : Space → ℝ) x *
      (q.cutoff : Space → ℝ) x ^ 2 * (J (σ n) i x * J (σ n) j x)
        ∂ManifoldVolume.coordinateMeasure B q.center)).re) atTop
    (𝓝 ((∫ z, a z * density ν hf z i j ∂traceMeasure ν).re)) at hreal
  have hRe := (by simpa only [RCLike.re_to_complex] using (integral_re hI).symm :
    (∫ z, a z * density ν hf z i j ∂traceMeasure ν).re =
      ∫ z, (a z * density ν hf z i j).re ∂traceMeasure ν)
  rw [hRe] at hreal
  have hCancel (x : Space) : (ψ : Space → ℝ) x * (q.cutoff : Space → ℝ) x ^ 2 =
      (φ : Space → ℝ) x := inverseSquareTest_cancel q.cutoff φ hφ x
  simp only [Complex.ofReal_re, hCancel] at hreal
  simpa only [a, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hTest,
    zero_mul, sub_zero] using hreal

end Burnett.Microlocal.Overlap
