import Burnett.Analysis.Microlocal.Overlap.ReceivingFirstOrderPrincipal
import Burnett.Analysis.Microlocal.Overlap.ReceivingRowRangeBridge

/-! The fixed receiving-chart first-order system constrains the original jet covariance range. -/
set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 3000000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Analysis.HminusWeightedDual (negativeEnergy)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeGradientSchwartz)
open Burnett.Microlocal.BesselLocalization (firstOrderRow rowPrincipal physicalCoefficient angularDirectionSymbol
  angularDirection_contDiffOn angularDirection_degreeZero)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.RowKernelDensity (separableRowAction)
open Burnett.Microlocal.SeparablePositive (separableOperator)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped ContDiff Manifold Matrix Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- Strong H-minus vanishing of each compactly localized first-order row
forces the range of the actual jet covariance into the common local kernel
where the physical cutoff is nonzero. All rows use the same original control and extraction. -/
theorem original_receiving_firstOrderSystem_kernel_of_negativeEnergy {Rows : Type*} [Fintype Rows]
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
      let u := fixedVolumeGradientSchwartz B g hB hg hnB c χ hχc
      ∀ s : Rows, Tendsto (fun n => negativeEnergy (firstOrderRow (a s) (v s) (i s) (b s) (j s) (u n)))
        atTop (𝓝 0)) :
    let P (p : Cosphere r) : Matrix Rows JetSlot ℂ := fun s => receivingFirstOrderSymbol c (a s) (v s) (i s) p
    ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K), (χ : E → ℝ) (c.chart (projection p)) ≠ 0 →
      P p * atlasJetCovarianceOperator c A.density p = 0 ∧
      ∀ w : JetSlot → ℂ, P p *ᵥ (atlasJetCovarianceOperator c A.density p *ᵥ w) = 0 := by
  intro P
  let hχc := hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
  let u := fixedVolumeGradientSchwartz B g hB hg hnB c χ hχc
  let ρ := A.control.restrict (amplitudeCosphereWindow r K)
  let N (p : Cosphere r) : Matrix JetSlot JetSlot ℂ := fun s t => atlasOrderedJetEntry c A.density p s t
  let ζ := receivingFirstOrderNormalization (r := r) c χ
  have hWin := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  have hRows (s : Rows) : ∀ᵐ p ∂ρ, (ζ p • P p s) ᵥ* (N p)ᵀ = 0 := by
    let a₀ (k : J) := physicalCoefficient (a s k)
    let m (k : J) := angularDirectionSymbol (v s k)
    have hPr := fixedVolumeRowPrincipal_tendsto_zero_of_negativeEnergy r B g hB hg hnB hconv hb
      c χ hχc (a s) (v s) (i s) (b s) (j s) (hStrong s)
    have hStrong' : Tendsto (fun n => separableRowAction (i s) a₀ m (fun k => (u (σ n) k).toLp 2 volume))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, rowPrincipal, separableRowAction, separableOperator,
        ContinuousLinearMap.comp_apply, a₀, m, u] using hPr.comp hσ.tendsto_atTop
    have hR := (original_receiving_separableRow_kernel r B g hB hg hsB hsG hnB hnG hconv hb hv σ hσ A hA
      c K hK hKc χ hχ (i s) a₀ m (fun t => Complex.ofRealCLM.contDiff.comp (test_smooth (a s t)))
      (fun t => (test_compactSupport (a s t)).comp_left Complex.ofReal_zero)
      (fun t => angularDirection_contDiffOn (v s t)) (fun t => angularDirection_degreeZero (v s t)) hStrong').2
    filter_upwards [hR, ae_restrict_mem (μ := A.control) hWin] with p hp hLoc
    have hEq : receivingPrincipalRow c χ (i s) a₀ m p = ζ p • P p s :=
      receivingPrincipalRow_eq_firstOrderSymbol c χ (a s) (v s) (i s) p (hKc hLoc)
    rw [← hEq]
    exact hp.2
  have hRange := ae_receivingJetOperator_kernel_of_scaled_ordered_rows c A hK hKc P ζ hRows
  filter_upwards [hRange, ae_restrict_mem (μ := A.control) hWin] with p hp hLoc hNonzero
  exact hp (receivingFirstOrderNormalization_ne_zero c χ p (hKc hLoc) hNonzero)

end Burnett.Microlocal.Overlap
