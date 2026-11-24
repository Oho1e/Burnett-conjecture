import Burnett.Analysis.Microlocal.Overlap.ReceivingCovariantFirstOrderLocalization
import Burnett.Analysis.Microlocal.CoordinateCurlRows

/-! The actual localized auxiliary covariant gradient has the curl kernel
on the same receiving-chart covariance. -/

set_option autoImplicit false
set_option maxRecDepth 4500
set_option maxHeartbeats 3300000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Matrix Burnett.Fourier Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Analysis.HminusWeightedDual (negativeEnergy)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Microlocal.AtlasVolumeGradient (fixedWeightedCutoff fixedComponent fixedComponent_smooth fixedPerturbation
  fixedComponent_localUniform fixedJet_uniform_bound_on_compact fixedVolumeGradientSchwartz
  fixedVolumeGradient_weak_and_uniform_L2 fixedVolumeCovariantGradientSchwartz
  fixedVolumeCovariantGradient_sub_partial_tendsto_zero)
open Burnett.F05.CoordinateCurl (Axis TensorPair tensorGradientSchwartz localizedGradientTest
  localizedGradient_tsupport localizedGradientTest_test_tendsto_zero exists_outerCutoff_on_tsupport
  curlRowCoefficients curlRowDirections curlRowInputs coordinateCurl_firstOrderRow_negativeEnergy_tendsto_zero axis)
open Burnett.Microlocal.BesselLocalization
open Burnett.Microlocal.CurlDensity (JetSlot CurlSlot curlMatrix)
open Burnett.Microlocal.RowKernelDensity (groupRow)
open Burnett.X02.SobolevTestJet (D directional test_memLp test_smooth test_compactSupport)
open scoped BigOperators ContDiff InnerProduct Manifold Matrix Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

private theorem bessel_coeffMul_fixedVolumeGradient_tendsto_zero
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) (a : D) (k : JetSlot) :
    Tendsto (fun n => fourierMultiplier besselSymbol
      ((coeffMul a (fixedVolumeGradientSchwartz B g hB hg hn c χ hχ n k)).toLp 2 volume)) atTop (𝓝 0) := by
  let w := fixedWeightedCutoff B hB hn c χ hχ
  have hw : tsupport (w : E → ℝ) ⊆ c.chart.target := tsupport_mul_subset_left.trans hχ
  let f (n : ℕ) : D := localizedGradientTest c.chart.open_target w hw
    (fixedComponent_smooth B g hB hg c n k.2) k.1
  obtain ⟨θ, hθ⟩ := exists_outerCutoff_on_tsupport w
  have hOne (n : ℕ) (x : E) (hx : (f n : E → ℝ) x ≠ 0) : (θ : E → ℝ) x = 1 :=
    hθ x (localizedGradient_tsupport w (fixedComponent B g c n k.2) k.1 (subset_tsupport _ hx))
  have hEq (n : ℕ) : sourceSchwartz (test_smooth (f n)) θ (hOne n) =
      fixedVolumeGradientSchwartz B g hB hg hn c χ hχ n k := SchwartzMap.ext fun _ => rfl
  obtain ⟨C, _, hU, _⟩ := fixedVolumeGradient_weak_and_uniform_L2 r B g hB hg hn hconv hb c χ hχ
  have hReal (n : ℕ) : ‖(test_memLp (f n)).toLp (f n : E → ℝ)‖ ≤ C := by
    have hNorm : ‖(sourceSchwartz (test_smooth (f n)) θ (hOne n)).toLp 2 volume‖ =
        ‖(test_memLp (f n)).toLp (f n : E → ℝ)‖ := by
      simp only [SchwartzMap.toLp, Lp.norm_toLp]
      congr 1
      exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => Complex.norm_real ((f n : E → ℝ) x))
    rw [← hNorm, hEq]
    exact hU n k
  have hTest (φ : D) : Tendsto (fun n => ∫ x, (f n : E → ℝ) x * (φ : E → ℝ) x) atTop (𝓝 0) :=
    localizedGradientTest_test_tendsto_zero c.chart.open_target w hw (fun n => fixedComponent B g c n k.2)
      (fun n => fixedComponent_smooth B g hB hg c n k.2)
      (fixedComponent_localUniform r B g hconv c k.2) k.1 φ
  simpa only [hEq, coeffMul_toLp] using vanishingFrequency_after_coefficient_tendsto_zero
    besselSymbol bessel_small_outside_ball a (fun n => (f n : E → ℝ)) (fun n => test_smooth (f n))
    (fun n => test_memLp (f n)) θ hOne C hReal hTest

/-- The genuine half-density localized covariant gradient annihilates
the curl row in negative energy, including any fixed smooth lower-order row. -/
theorem fixedVolumeCovariantCurl_negativeEnergy_tendsto_zero {L : Type} [Fintype L]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (θ : D) (hθ : ∀ x ∈ tsupport (χ : E → ℝ), (θ : E → ℝ) x = 1)
    (s : CurlSlot) (b : L → D) (j : L → JetSlot) :
    Tendsto (fun n => negativeEnergy (firstOrderRow (curlRowCoefficients θ)
      (curlRowDirections s.1 s.2.1) (curlRowInputs s.1 s.2.1 s.2.2) b j
      (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n))) atTop (𝓝 0) := by
  let a := curlRowCoefficients θ
  let v := curlRowDirections s.1 s.2.1
  let i := curlRowInputs s.1 s.2.1 s.2.2
  let W := fixedVolumeGradientSchwartz B g hB hg hn c χ hχ
  let U := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ
  apply negativeEnergy_firstOrderRow_tendsto_zero_of_strongL2_replacement a v i b j U W
    (fixedVolumeCovariantGradient_sub_partial_tendsto_zero r B g hB hg hn hconv c χ hχ)
  let w := fixedWeightedCutoff B hB hn c χ hχ
  have hwχ : tsupport (w : E → ℝ) ⊆ tsupport (χ : E → ℝ) := tsupport_mul_subset_left
  have hw := hwχ.trans hχ
  obtain ⟨C, hC, hJet⟩ := fixedJet_uniform_bound_on_compact r B g hB hg hn hconv hb c
    (test_compactSupport w) hw
  have hD (n : ℕ) (p : TensorPair) (d : Axis) (x : E) (hx : x ∈ tsupport (w : E → ℝ)) :
      ‖directional d (fixedComponent B g c n p) x‖ ≤ C := by
    let F := coordinateJet (fixedPerturbation B (g n) c) x
    change ‖F d p.1 p.2‖ ≤ C
    exact (norm_le_pi_norm (F d p.1) p.2).trans
      ((norm_le_pi_norm (F d) p.1).trans ((norm_le_pi_norm F d).trans (hJet n x hx)))
  let P n := firstOrderRow a v i (Fin.elim0 : Fin 0 → D) (Fin.elim0 : Fin 0 → JetSlot) (W n)
  have hP : Tendsto (fun n => negativeEnergy (P n)) atTop (𝓝 0) :=
    coordinateCurl_firstOrderRow_negativeEnergy_tendsto_zero c.chart.open_target w hw θ
      (fun x hx => hθ x (hwχ hx)) (fixedComponent B g c) (fixedComponent_smooth B g hB hg c)
      (fixedComponent_localUniform r B g hconv c) s.1 s.2.1 s.2.2 hC hD
  let T := (fourierMultiplier besselSymbol).comp (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E))
  have hL (l : L) : Tendsto (fun n => T (coeffMul (b l) (W n (j l)))) atTop (𝓝 0) :=
    bessel_coeffMul_fixedVolumeGradient_tendsto_zero r B g hB hg hn hconv hb c χ hχ (b l) (j l)
  have hMain : Tendsto (fun n => T (P n)) atTop (𝓝 0) :=
    (tendsto_besselLp_iff_negativeEnergy_tendsto_zero P).mpr hP
  have hFull (n : ℕ) : firstOrderRow a v i b j (W n) = P n + ∑ l, coeffMul (b l) (W n (j l)) := by
    simp [firstOrderRow, P]
  apply (tendsto_besselLp_iff_negativeEnergy_tendsto_zero (fun n => firstOrderRow a v i b j (W n))).mp
  change Tendsto (fun n => T (firstOrderRow a v i b j (W n))) atTop (𝓝 0)
  simp_rw [hFull, map_add, map_sum]
  simpa only [Finset.sum_const_zero, add_zero] using hMain.add
    (tendsto_finset_sum Finset.univ (fun l _ => hL l))

omit [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
theorem receivingCurlSymbol_eq {r : Metric (M := M)} (c : AtlasChart M) (θ : D) (p : Cosphere r)
    (hθ : (θ : E → ℝ) (c.chart (projection p)) = 1) (s : CurlSlot) :
    receivingFirstOrderSymbol c (curlRowCoefficients θ) (curlRowDirections s.1 s.2.1)
      (curlRowInputs s.1 s.2.1 s.2.2) p = curlMatrix (atlasChartUnitCovector c p) s := by
  let ξ := atlasChartUnitCovector c p
  let x := c.chart (projection p)
  have hInner (d : Axis) : inner ℝ (WithLp.toLp 2 ξ) (axis d) = ξ d := by
    rw [axis, EuclideanSpace.inner_single_right]
    simp
  have hPlus : ((θ : E → ℝ) x : ℂ) = 1 := by exact_mod_cast hθ
  have hMinus : (((-θ : D) : E → ℝ) x : ℂ) = -1 := by
    change ((-(θ : E → ℝ) x : ℝ) : ℂ) = -1
    rw [Complex.ofReal_neg, hPlus]
  funext k
  simp only [receivingFirstOrderSymbol, groupRow, Fin.sum_univ_two]
  change (if (s.2.1, s.2.2) = k then ((θ : E → ℝ) x : ℂ) * (inner ℝ (WithLp.toLp 2 ξ) (axis s.1) : ℂ) else 0) +
    (if (s.1, s.2.2) = k then (((-θ : D) : E → ℝ) x : ℂ) * (inner ℝ (WithLp.toLp 2 ξ) (axis s.2.1) : ℂ) else 0) =
    curlMatrix ξ s k
  rw [hInner, hInner, hPlus, hMinus]
  have flip (t : JetSlot) : (t = k) ↔ (k = t) := eq_comm
  simp only [curlMatrix, one_mul, neg_one_mul, flip (s.2.1, s.2.2), flip (s.1, s.2.2), sub_eq_add_neg]
  apply congrArg₂ (· + ·) rfl
  split <;> simp_all

variable [T2Space M]

/-- The original intrinsic jet covariance has curl-free range at the actual
auxiliary unit covectors of each receiving chart on the open cutoff window. -/
theorem original_receiving_covariant_curl_kernel {L : Type} [Fintype L]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart '' K)
    (θ : D) (hθ : ∀ x ∈ tsupport (χ : E → ℝ), (θ : E → ℝ) x = 1)
    (b : CurlSlot → L → D) (j : CurlSlot → L → JetSlot) :
    ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K), (χ : E → ℝ) (c.chart (projection p)) ≠ 0 →
      curlMatrix (atlasChartUnitCovector c p) * atlasJetCovarianceOperator c A.density p = 0 ∧
      ∀ z : JetSlot → ℂ, curlMatrix (atlasChartUnitCovector c p) *ᵥ (atlasJetCovarianceOperator c A.density p *ᵥ z) = 0 := by
  have h := original_receiving_covariant_firstOrderSystem_kernel_of_negativeEnergy r B g hB hg
    hsB hsG hnB hnG hconv hb hv σ hσ A hA c K hK hKc χ hχ (fun _ : CurlSlot => curlRowCoefficients θ)
    (fun s => curlRowDirections s.1 s.2.1) (fun s => curlRowInputs s.1 s.2.1 s.2.2) b j
    (fun s => fixedVolumeCovariantCurl_negativeEnergy_tendsto_zero r B g hB hg hnB hconv hb c χ
      (hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))) θ hθ s (b s) (j s))
  filter_upwards [h] with p hp hNonzero
  have hOne := hθ _ (subset_tsupport (χ : E → ℝ) hNonzero)
  have hEq : (fun s : CurlSlot => receivingFirstOrderSymbol c (curlRowCoefficients θ)
      (curlRowDirections s.1 s.2.1) (curlRowInputs s.1 s.2.1 s.2.2) p) =
      curlMatrix (atlasChartUnitCovector c p) := funext fun s => receivingCurlSymbol_eq c θ p hOne s
  simpa only [hEq] using hp hNonzero

end Burnett.Microlocal.Overlap
