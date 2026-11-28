import Burnett.Analysis.Microlocal.Overlap.GlobalOriginalAmplitudeContraction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2100

noncomputable section

namespace Burnett.V03

open Set Filter MeasureTheory Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian)
open Burnett.F07.IntrinsicAmplitude (intrinsicPhysicalWeight)
open Burnett.Microlocal.Overlap (IntrinsicAmplitudeCovariance HasIntrinsicPhysicalContraction
  amplitudeCosphereWindow measurableSet_amplitudeCosphereWindow)
open scoped ContDiff Manifold ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M]

/-- The compressed Hamiltonian weight integrates against the same F05
physical measure as the Einstein moment, on the same compact base window. -/
theorem integral_nullCompression_samePhysicalMeasure
    (r : Metric (M := M)) (B : Field (M := M)) (hn : IsNondegenerate B)
    (A : IntrinsicAmplitudeCovariance r) (μ : Measure (Cosphere r))
    (hμ : HasIntrinsicPhysicalContraction r B hn A μ)
    (K : Set M) (hK : MeasurableSet K) (f : Cosphere r → ℝ) :
    let U := amplitudeCosphereWindow r K
    (∫ p, if hamiltonian B hn p = 0 then
      4 * (intrinsicPhysicalWeight B hn A.density p : ℂ) * (f p : ℂ) else 0 ∂(A.control.restrict U)) =
      4 * ∫ p, (f p : ℂ) ∂(μ.restrict U) := by
  classical
  intro U
  let Z : Set (Cosphere r) := {p | hamiltonian B hn p = 0}
  let w := intrinsicPhysicalWeight B hn A.density
  let τ := A.control.restrict U
  let ρ := τ.restrict Z
  change MeasurableSet Z ∧ AEMeasurable w (A.control.restrict Z) ∧
    (∀ᵐ p ∂(A.control.restrict Z), 0 ≤ w p) ∧
    μ = (A.control.restrict Z).withDensity (fun p => ENNReal.ofReal (w p)) at hμ
  obtain ⟨hZ,hw,hpos,hμeq⟩ := hμ
  have hU := measurableSet_amplitudeCosphereWindow r hK
  have hre : ρ = (A.control.restrict Z).restrict U := by
    change (A.control.restrict U).restrict Z = (A.control.restrict Z).restrict U
    rw [Measure.restrict_restrict hZ, Measure.restrict_restrict hU, inter_comm]
  have hν : μ.restrict U = ρ.withDensity (fun p => ENNReal.ofReal (w p)) := by
    rw [hμeq, restrict_withDensity hU, hre]
  have hMeas : AEMeasurable (fun p => ENNReal.ofReal (w p)) ρ := by
    rw [hre]
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hw.mono_measure Measure.restrict_le_self)
  have hPosρ : ∀ᵐ p ∂ρ, 0 ≤ w p := by
    rw [hre]
    exact ae_restrict_of_ae hpos
  have hD : (∫ p, (f p : ℂ) ∂(μ.restrict U)) = ∫ p, (w p : ℂ) * (f p : ℂ) ∂ρ := by
    rw [hν, integral_withDensity_eq_integral_toReal_smul₀ hMeas
      (.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hPosρ] with p hp
    rw [ENNReal.toReal_ofReal hp]
    rfl
  rw [hD, ← integral_const_mul]
  let F (p : Cosphere r) := 4 * (w p : ℂ) * (f p : ℂ)
  have he : (fun p => if hamiltonian B hn p = 0 then F p else 0) = Z.indicator F := rfl
  change (∫ p, (if hamiltonian B hn p = 0 then F p else 0) ∂τ) =
    ∫ p, (4 : ℂ) * ((w p : ℂ) * (f p : ℂ)) ∂ρ
  rw [he, integral_indicator hZ]
  apply integral_congr_ae
  exact .of_forall fun p => mul_assoc _ _ _

end Burnett.V03
