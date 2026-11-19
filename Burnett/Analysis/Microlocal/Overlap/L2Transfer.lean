import Burnett.Analysis.Microlocal.Overlap.HalfDensity

set_option autoImplicit false
noncomputable section

namespace Burnett.F05.ChartVolumeBridge

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Manifold Topology
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricTransition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- On a measurable part of a chart, a scalar field is square integrable for geometric
volume exactly when its half-density representative is square integrable for Lebesgue volume. -/
theorem coordinateMeasure_memLp_two_iff_halfDensity (B : Field (M := M)) (hs : IsSmooth B)
    (hn : IsNondegenerate B) (c : M) {S : Set CoordinateSpace} (hS : MeasurableSet S)
    (hSU : S ⊆ (chartAt CoordinateSpace c).target) (f : CoordinateSpace → ℂ) :
    MemLp f 2 ((ManifoldVolume.coordinateMeasure B c).restrict S) ↔
      MemLp (fun x => (chartHalfDensity B c x : ℂ) * f x) 2 (volume.restrict S) := by
  let G := metricComponents (coordinateBilinear B c)
  let μ := (volume : Measure CoordinateSpace).restrict S
  let ρ := LorentzVolume.density G
  let h (x : CoordinateSpace) : ℂ := chartHalfDensity B c x
  have e : (ManifoldVolume.coordinateMeasure B c).restrict S = μ.withDensity ρ := by
    exact restrict_withDensity hS ρ
  rw [e]
  change MemLp f 2 (μ.withDensity ρ) ↔ MemLp (fun x => h x * f x) 2 μ
  have hρ : AEMeasurable ρ μ := LorentzVolume.aemeasurable_density_restrict volume G S hS
    ((continuousOn_components B hs c).mono hSU)
  have hρpos : ∀ᵐ x ∂μ, ρ x ≠ 0 := by
    filter_upwards [ae_restrict_mem (μ := volume) hS] with x hx
    exact (LorentzVolume.density_pos G x
      (ManifoldVolumeRegularity.coordinate_det_ne_zero B hn c (hSU hx))).ne'
  have hh : AEStronglyMeasurable h μ :=
    (Complex.continuous_ofReal.comp_continuousOn
      ((chartHalfDensity_smoothOn B hs hn c).continuousOn.mono hSU)).aestronglyMeasurable hS
  have hh0 : ∀ᵐ x ∂μ, h x ≠ 0 := by
    filter_upwards [ae_restrict_mem (μ := volume) hS] with x hx
    change (chartHalfDensity B c x : ℂ) ≠ 0
    exact_mod_cast (chartHalfDensity_pos B hn c (hSU hx)).ne'
  have eNorm : (fun x => (ρ x).toReal • ‖f x‖ ^ 2) = (fun x => ‖h x * f x‖ ^ 2) := by
    funext x
    simp only [h, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, smul_eq_mul]
    rw [chartHalfDensity_sq]
  have hI := integrable_withDensity_iff_integrable_smul₀' (g := fun x => ‖f x‖ ^ 2) hρ
    (Eventually.of_forall fun x => (LorentzVolume.density_ne_top G x).lt_top)
  rw [eNorm] at hI
  constructor
  · intro hf
    have hfm := hf.aestronglyMeasurable.mono_ac (withDensity_absolutelyContinuous' hρ hρpos)
    exact (memLp_two_iff_integrable_sq_norm (hh.mul hfm)).mpr
      (hI.mp ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf))
  · intro hf
    have hfm : AEStronglyMeasurable f μ :=
      (hf.aestronglyMeasurable.mul hh.aemeasurable.inv.aestronglyMeasurable).congr (by
      filter_upwards [hh0] with x hx
      change (h x * f x) * (h x)⁻¹ = f x
      field_simp)
    have hfm' := hfm.mono_ac (withDensity_absolutelyContinuous μ ρ)
    exact (memLp_two_iff_integrable_sq_norm hfm').mpr
      (hI.mpr ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf))

end Burnett.F05.ChartVolumeBridge
