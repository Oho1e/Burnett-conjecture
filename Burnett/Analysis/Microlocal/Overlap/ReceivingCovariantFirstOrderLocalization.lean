import Burnett.Analysis.Microlocal.Overlap.ReceivingFirstOrderKernel
import Burnett.Analysis.Microlocal.Overlap.FirstOrderNegativeContinuity
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartCovariantPairing

/-! First-order localization for the same actual covariant jet as in the paper. -/
set_option autoImplicit false
set_option maxRecDepth 4500
set_option maxHeartbeats 2900000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Analysis.HminusWeightedDual (negativeEnergy)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeGradientSchwartz fixedVolumeCovariantGradientSchwartz
  fixedVolumeCovariantGradient_sub_partial_tendsto_zero)
open Burnett.Microlocal.BesselLocalization (firstOrderRow negativeEnergy_firstOrderRow_tendsto_zero_of_strongL2_replacement)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Matrix Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- A finite first-order system on the original localized covariant jet
constrains the same jet covariance on that window. The H-minus premise is
the actual norm of its rows on the covariant, volume half-density inputs. -/
theorem original_receiving_covariant_firstOrderSystem_kernel_of_negativeEnergy {Rows : Type*} [Fintype Rows]
    {J L : Type} [Fintype J] [Fintype L]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart '' K)
    (a : Rows → J → D) (v : Rows → J → E) (i : Rows → J → JetSlot)
    (b : Rows → L → D) (j : Rows → L → JetSlot)
    (hStrong : let hχc := hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
      let u := fixedVolumeCovariantGradientSchwartz r B g hB hg hnB c χ hχc
      ∀ s : Rows, Tendsto (fun n => negativeEnergy (firstOrderRow (a s) (v s) (i s) (b s) (j s) (u n)))
        atTop (𝓝 0)) :
    let P (p : Cosphere r) : Matrix Rows JetSlot ℂ := fun s => receivingFirstOrderSymbol c (a s) (v s) (i s) p
    ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K), (χ : E → ℝ) (c.chart (projection p)) ≠ 0 →
      P p * atlasJetCovarianceOperator c A.density p = 0 ∧
      ∀ w : JetSlot → ℂ, P p *ᵥ (atlasJetCovarianceOperator c A.density p *ᵥ w) = 0 := by
  apply original_receiving_firstOrderSystem_kernel_of_negativeEnergy r B g hB hg hsB hsG hnB hnG hconv hb hv
    σ hσ A hA c K hK hKc χ hχ a v i b j
  intro hχc u s
  let w := fixedVolumeCovariantGradientSchwartz r B g hB hg hnB c χ hχc
  refine negativeEnergy_firstOrderRow_tendsto_zero_of_strongL2_replacement (a s) (v s) (i s) (b s) (j s)
    u w (fun k => ?_) (hStrong s)
  have h := (fixedVolumeCovariantGradient_sub_partial_tendsto_zero r B g hB hg hnB hconv c χ hχc k).neg
  simpa only [neg_sub, neg_zero, w, u, Function.comp_def] using h

end Burnett.Microlocal.Overlap
