import Burnett.Analysis.Microlocal.Overlap.ReceivingPhysicalVolumeTransport
import Burnett.Geometry.ManifoldVolumeRegularity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Physical-volume kernels in the actual half-density coordinates of two charts. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
namespace Burnett.Microlocal.Overlap

open MeasureTheory Set Filter Classical Function Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient (fixedHalfDensity)
open scoped Manifold ContDiff Topology ComplexConjugate

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

/-- Actual fixed-volume integration in an arbitrary receiving chart. -/
theorem integral_geometricVolume_receiving (B : Field (M := M)) (hB : IsSmooth B)
    (c : AtlasChart M) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : M → F) (hf : StronglyMeasurable f) :
    (∫ p in c.chart.source, f p ∂ManifoldVolume.geometricMeasure B) =
      ∫ x in c.chart.target, (fixedHalfDensity B c x ^ 2) • f (c.chart.symm x) := by
  let U := c.chart.target
  let G := metricComponents (fixedForm B c)
  have hU : MeasurableSet U := c.chart.open_target.measurableSet
  have hG : ContinuousOn G U :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j =>
      (fixedForm_components_smooth B hB c i j).continuousOn
  have hρ : AEMeasurable (LorentzVolume.density G) (volume.restrict U) :=
    LorentzVolume.aemeasurable_density_restrict volume G U hU hG
  have hfinite : ∀ᵐ x ∂volume.restrict U, LorentzVolume.density G x < ⊤ :=
    Eventually.of_forall fun x => (LorentzVolume.density_ne_top G x).lt_top
  rw [geometricVolume_restrict_eq_receiving B c,
    integral_map (measurable_receivingVolumeInverse c).aemeasurable hf.aestronglyMeasurable]
  change (∫ x, f (receivingVolumeInverse c x) ∂(volume.withDensity (LorentzVolume.density G)).restrict U) = _
  rw [restrict_withDensity hU, integral_withDensity_eq_integral_toReal_smul₀ hρ hfinite]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) hU] with x hx
  rw [receivingVolumeInverse_of_mem c hx]
  congr 1
  simp only [LorentzVolume.density, G, fixedHalfDensity, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    Real.sq_sqrt (Real.sqrt_nonneg _)]

/-- A kernel written relative to physical volume acquires one half-density in
each variable, in addition to the factors already included in the test inputs. -/
def receivingHalfDensityKernel (B : Field (M := M)) (c d : AtlasChart M)
    (k : M → M → ℂ) (x y : E) : ℂ :=
  (fixedHalfDensity B c x : ℂ) * k (c.chart.symm x) (d.chart.symm y) * (fixedHalfDensity B d y : ℂ)

theorem integral_geometricVolume_separatedChartKernel
    (B : Field (M := M)) (hB : IsSmooth B) [SFinite (ManifoldVolume.geometricMeasure B)]
    (c d : AtlasChart M) (k : M → M → ℂ) (hk : Measurable (uncurry k))
    (v f : M → ℂ) (hv : Measurable v) (hf : Measurable f) :
    (∫ p in c.chart.source, conj (v p) *
        (∫ q in d.chart.source, k p q * f q ∂ManifoldVolume.geometricMeasure B)
        ∂ManifoldVolume.geometricMeasure B) =
      ∫ x in c.chart.target, conj ((fixedHalfDensity B c x : ℂ) * v (c.chart.symm x)) *
        (∫ y in d.chart.target, receivingHalfDensityKernel B c d k x y *
          ((fixedHalfDensity B d y : ℂ) * f (d.chart.symm y))) := by
  let μ := ManifoldVolume.geometricMeasure B
  have hJoint : StronglyMeasurable (fun pq : M × M => k pq.1 pq.2 * f pq.2) :=
    (hk.mul (hf.comp measurable_snd)).stronglyMeasurable
  have hOuter : Measurable (fun p => conj (v p) * (∫ q in d.chart.source, k p q * f q ∂μ)) :=
    (Complex.continuous_conj.measurable.comp hv).mul
      (hJoint.integral_prod_right' (ν := μ.restrict d.chart.source)).measurable
  rw [integral_geometricVolume_receiving B hB c _ hOuter.stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with x
  have hRow : Measurable (fun q => k (c.chart.symm x) q * f q) :=
    (hk.comp (measurable_const.prodMk measurable_id)).mul hf
  rw [integral_geometricVolume_receiving B hB d _ hRow.stronglyMeasurable]
  let a := (fixedHalfDensity B c x : ℂ)
  have hInner :
      (∫ y in d.chart.target, receivingHalfDensityKernel B c d k x y *
        ((fixedHalfDensity B d y : ℂ) * f (d.chart.symm y))) =
      a * (∫ y in d.chart.target, (fixedHalfDensity B d y ^ 2) •
        (k (c.chart.symm x) (d.chart.symm y) * f (d.chart.symm y))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    simp only [receivingHalfDensityKernel, a, Complex.real_smul, Complex.ofReal_pow]
    ring
  rw [hInner]
  simp only [a, Complex.real_smul, Complex.ofReal_pow, map_mul, Complex.conj_ofReal]
  ring

end Burnett.Microlocal.Overlap
