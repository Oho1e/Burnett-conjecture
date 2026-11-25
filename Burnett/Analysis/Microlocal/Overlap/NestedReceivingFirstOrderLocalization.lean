import Burnett.Analysis.Microlocal.Overlap.FirstOrderCutoffCommutator
import Burnett.Analysis.Microlocal.Overlap.ReceivingCovariantCurl

/-! The local strong H⁻¹ hypothesis with nested cutoffs on the original covariant jet. -/

set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 3900000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Analysis.HminusWeightedDual (negativeEnergy)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Microlocal.BesselLocalization
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ContDiff Manifold Matrix Topology

open private cutoffProduct coeffMul_comp
  from Burnett.Analysis.Microlocal.Overlap.FirstOrderCutoffCommutator
open private bessel_coeffMul_fixedVolumeGradient_tendsto_zero
  from Burnett.Analysis.Microlocal.Overlap.ReceivingCovariantCurl

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- Multiplying the original half-density jet by an inner cutoff removes the
outer cutoff exactly when the outer cutoff is one on the inner support. -/
theorem coeffMul_fixedVolumeCovariantGradientSchwartz_eq_of_plateau
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ η : D)
    (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) (hη : tsupport (η : E → ℝ) ⊆ c.chart.target)
    (hOne : ∀ x ∈ tsupport (χ : E → ℝ), (η : E → ℝ) x = 1) (n : ℕ) (k : JetSlot) :
    coeffMul χ (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η hη n k) =
      fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n k := by
  ext x
  change ((χ : E → ℝ) x : ℂ) * fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η hη n k x =
    fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n k x
  rw [fixedVolumeCovariantGradientSchwartz_apply, fixedVolumeCovariantGradientSchwartz_apply]
  by_cases hx : x ∈ tsupport (χ : E → ℝ)
  · rw [hOne x hx, one_mul]
    push_cast
    rw [mul_assoc]
  · simp only [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, zero_mul]

variable [MeasurableSpace M] [BorelSpace M]

/-- A fixed smooth zeroth-order term on the actual covariant jet tends
strongly to zero after applying inverse Bessel regularization. -/
theorem bessel_coeffMul_fixedVolumeCovariantGradient_tendsto_zero
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (η : D) (hη : tsupport (η : E → ℝ) ⊆ c.chart.target)
    (a : D) (k : JetSlot) :
    Tendsto (fun n => fourierMultiplier besselSymbol
      ((coeffMul a (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η hη n k)).toLp 2 volume))
      atTop (𝓝 0) := by
  let T := (fourierMultiplier besselSymbol).comp (symbolCLM (physicalCoefficient a))
  let u n := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η hη n k
  let w n := fixedVolumeGradientSchwartz B g hB hg hn c η hη n k
  have hStrong := fixedVolumeCovariantGradient_sub_partial_tendsto_zero r B g hB hg hn hconv c η hη k
  have hErr : Tendsto (fun n => T ((u n).toLp 2 volume) - T ((w n).toLp 2 volume)) atTop (𝓝 0) := by
    simpa only [u, w, Function.comp_def, map_sub, map_zero] using (T.continuous.tendsto 0).comp hStrong
  have hPartial : Tendsto (fun n => T ((w n).toLp 2 volume)) atTop (𝓝 0) := by
    simpa only [T, w, ContinuousLinearMap.comp_apply, coeffMul_toLp] using
      bessel_coeffMul_fixedVolumeGradient_tendsto_zero r B g hB hg hn hconv hb c η hη a k
  simp only [coeffMul_toLp]
  change Tendsto (fun n => T ((u n).toLp 2 volume)) atTop (𝓝 0)
  simpa only [sub_add_cancel, zero_add] using hErr.add hPartial

/-- For the original receiving jet, the row on the inner cutoff tends to
zero in squared H⁻¹ norm exactly when the inner-cutoff row on the outer
input tends to zero in the actual Bessel L² realization. -/
theorem negativeEnergy_covariantFirstOrderRow_tendsto_zero_iff_nestedCutoff
    {J L : Type*} [Fintype J] [Fintype L]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ η : D)
    (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) (hη : tsupport (η : E → ℝ) ⊆ c.chart.target)
    (hOne : ∀ x ∈ tsupport (χ : E → ℝ), (η : E → ℝ) x = 1)
    (a : J → D) (v : J → E) (i : J → JetSlot) (b : L → D) (j : L → JetSlot) :
    let U := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ
    let W := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η hη
    Tendsto (fun n => negativeEnergy (firstOrderRow a v i b j (U n))) atTop (𝓝 0) ↔
      Tendsto (fun n => fourierMultiplier besselSymbol
        ((coeffMul χ (firstOrderRow a v i b j (W n))).toLp 2 volume)) atTop (𝓝 0) := by
  intro U W
  let F n := firstOrderRow a v i b j (U n)
  let G n := coeffMul χ (firstOrderRow a v i b j (W n))
  let T := (fourierMultiplier besselSymbol).comp (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E))
  have hCut (n : ℕ) (k : JetSlot) : coeffMul χ (W n k) = U n k :=
    coeffMul_fixedVolumeCovariantGradientSchwartz_eq_of_plateau r B g hB hg hn c χ η hχ hη hOne n k
  let d (h : J) := cutoffProduct (a h) (coefficientPDeriv χ (v h))
  have hComm (n : ℕ) : F n - G n = ∑ h : J, coeffMul (d h) (W n (i h)) := by
    simpa only [F, G, d, hCut, coeffMul_comp] using firstOrderRow_cutoff_sub a v i b j χ (W n)
  have hTerm (h : J) :
      Tendsto (fun n => T (coeffMul (d h) (W n (i h)))) atTop (𝓝 0) :=
    bessel_coeffMul_fixedVolumeCovariantGradient_tendsto_zero r B g hB hg hn hconv hb
      c η hη (d h) (i h)
  have hDiff : Tendsto (fun n => T (F n) - T (G n)) atTop (𝓝 0) := by
    simp_rw [← map_sub, hComm, map_sum]
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun h _ => hTerm h)
  change Tendsto (fun n => negativeEnergy (F n)) atTop (𝓝 0) ↔ Tendsto (fun n => T (G n)) atTop (𝓝 0)
  rw [← tendsto_besselLp_iff_negativeEnergy_tendsto_zero F]
  change Tendsto (fun n => T (F n)) atTop (𝓝 0) ↔ Tendsto (fun n => T (G n)) atTop (𝓝 0)
  constructor
  · intro h
    simpa only [sub_sub_cancel, sub_zero] using h.sub hDiff
  · intro h
    simpa only [sub_add_cancel, zero_add] using hDiff.add h

variable [T2Space M]

/-- The nested local H⁻¹ hypothesis for a fixed finite system forces the
same original jet covariance into its kernel on the receiving cutoff window. -/
theorem original_receiving_covariant_firstOrderSystem_kernel_of_nestedCutoff
    {Rows : Type*} {J L : Type} [Fintype Rows] [Fintype J] [Fintype L]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (χ η : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart '' K) (hη : tsupport (η : E → ℝ) ⊆ c.chart.target)
    (hOne : ∀ x ∈ tsupport (χ : E → ℝ), (η : E → ℝ) x = 1)
    (a : Rows → J → D) (v : Rows → J → E) (i : Rows → J → JetSlot)
    (b : Rows → L → D) (j : Rows → L → JetSlot)
    (hLocal : ∀ s : Rows, Tendsto (fun n => fourierMultiplier besselSymbol
      ((coeffMul χ (firstOrderRow (a s) (v s) (i s) (b s) (j s)
        (fixedVolumeCovariantGradientSchwartz r B g hB hg hnB c η hη n))).toLp 2 volume)) atTop (𝓝 0)) :
    let P (p : Cosphere r) : Matrix Rows JetSlot ℂ := fun s => receivingFirstOrderSymbol c (a s) (v s) (i s) p
    ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K), (χ : E → ℝ) (c.chart (projection p)) ≠ 0 →
      P p * atlasJetCovarianceOperator c A.density p = 0 ∧
      ∀ w : JetSlot → ℂ, P p *ᵥ (atlasJetCovarianceOperator c A.density p *ᵥ w) = 0 := by
  apply original_receiving_covariant_firstOrderSystem_kernel_of_negativeEnergy
    r B g hB hg hsB hsG hnB hnG hconv hb hv σ hσ A hA c K hK hKc χ hχ a v i b j
  intro hχc U s
  exact (negativeEnergy_covariantFirstOrderRow_tendsto_zero_iff_nestedCutoff
    r B g hB hg hnB hconv hb c χ η hχc hη hOne (a s) (v s) (i s) (b s) (j s)).mpr (hLocal s)

end Burnett.Microlocal.Overlap
