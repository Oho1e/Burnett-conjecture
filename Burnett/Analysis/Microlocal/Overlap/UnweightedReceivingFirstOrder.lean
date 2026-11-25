import Burnett.Analysis.Microlocal.Overlap.NestedReceivingFirstOrderLocalization
import Burnett.Analysis.GaugeProjection.StrongCompactness.ReceivingCutoff

/-! A local strong H⁻¹ source stated in the ordinary, unweighted chart coordinates. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 5000000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Analysis.HminusWeightedDual (negativeEnergy)
open Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Microlocal.BesselLocalization
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.P01 (exists_projectedChartCutoff inverseHalfDensityCutoff inverseHalfDensityCutoff_tsupport
  fixedWeightedCutoff_inverseHalfDensityCutoff)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open scoped BigOperators ContDiff Manifold Topology

open private cutoffProduct coeffMul_comp coeffMul_apply
  from Burnett.Analysis.Microlocal.Overlap.FirstOrderCutoffCommutator

local notation "E" => CoordinateSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The actual unweighted coordinate components of the original covariant jet. -/
def receivingRawCovariantJet (r : Metric (M := M)) (B : Field (M := M))
    (g : ℕ → Field (M := M)) (c : AtlasChart M) (n : ℕ) (k : JetSlot) (x : E) : ℂ :=
  (fixedCovariantJet r.inner (fun m => g n m - B m) c x k.1 k.2.1 k.2.2 : ℝ)

variable [SecondCountableTopology M]

/-- The original half-density test with the inverse density in the cutoff
equals the ordinary unweighted localized jet, including the zero extension. -/
theorem fixedVolumeCovariantGradient_inverseHalfDensity_apply
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (n : ℕ) (k : JetSlot) (x : E) :
    let d := inverseHalfDensityCutoff B hB hn c χ hχ
    let hd := (inverseHalfDensityCutoff_tsupport B hB hn c χ hχ).trans hχ
    fixedVolumeCovariantGradientSchwartz r B g hB hg hn c d hd n k x =
      ((χ : E → ℝ) x : ℂ) * receivingRawCovariantJet r B g c n k x := by
  intro d hd
  rw [fixedVolumeCovariantGradientSchwartz_apply]
  have h := congrArg (fun a : D => (a : E → ℝ) x)
    (fixedWeightedCutoff_inverseHalfDensityCutoff B hB hn c χ hχ)
  change (d : E → ℝ) x * fixedHalfDensity B c x = (χ : E → ℝ) x at h
  rw [h]
  exact Complex.ofReal_mul _ _

/-- Differential action of a smooth coordinate row, with no input cutoff. -/
def receivingRawFirstOrderRow {J L : Type*} [Fintype J] [Fintype L]
    (a : J → E → ℝ) (v : J → E) (i : J → JetSlot)
    (b : L → E → ℝ) (j : L → JetSlot) (u : JetSlot → E → ℂ) (x : E) : ℂ :=
  (∑ h, (a h x : ℂ) * fderiv ℝ (u (i h)) x (v h)) + ∑ h, (b h x : ℂ) * u (j h) x

private theorem firstOrderRow_eq_raw_apply {J L : Type*} [Fintype J] [Fintype L]
    (a : J → D) (v : J → E) (i : J → JetSlot) (b : L → D) (j : L → JetSlot)
    (u : JetSlot → SchwartzMap E ℂ) (x : E) :
    firstOrderRow a v i b j u x =
      receivingRawFirstOrderRow (fun h => (a h : E → ℝ)) v i (fun h => (b h : E → ℝ)) j
        (fun k => (u k : E → ℂ)) x := by
  rw [firstOrderRow, SchwartzMap.add_apply, receivingRawFirstOrderRow]
  let ev := SchwartzMap.delta ℂ ℂ x
  change ev (∑ h, coeffMul (a h) (SchwartzMap.pderivCLM ℂ (v h) (u (i h)))) +
    ev (∑ h, coeffMul (b h) (u (j h))) = _
  simp only [map_sum]
  change (∑ h, coeffMul (a h) (SchwartzMap.pderivCLM ℂ (v h) (u (i h))) x) +
    (∑ h, coeffMul (b h) (u (j h)) x) = _
  simp only [coeffMul_apply, SchwartzMap.pderivCLM_apply]

variable [MeasurableSpace M] [BorelSpace M]

/-- Strong H⁻¹ convergence of the ordinary localized source implies the
negative-energy hypothesis on the original half-density input for the same
principal coefficients. The commutator uses only fixed zero-order factors. -/
theorem negativeEnergy_of_realized_unweightedFirstOrderSource
    {J L : Type*} [Fintype J] [Fintype L]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (a : J → D) (v : J → E) (i : J → JetSlot) (b : L → D) (j : L → JetSlot)
    (F : ℕ → SchwartzMap E ℂ)
    (hF : ∀ n x, F n x = ((χ : E → ℝ) x : ℂ) *
      receivingRawFirstOrderRow (fun h => (a h : E → ℝ)) v i (fun h => (b h : E → ℝ)) j
        (receivingRawCovariantJet r B g c n) x)
    (hStrong : Tendsto (fun n => negativeEnergy (F n)) atTop (𝓝 0)) :
    let d := inverseHalfDensityCutoff B hB hn c χ hχ
    let hd := (inverseHalfDensityCutoff_tsupport B hB hn c χ hχ).trans hχ
    Tendsto (fun n => negativeEnergy (firstOrderRow a v i b j
      (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c d hd n))) atTop (𝓝 0) := by
  intro d hd
  obtain ⟨η₀, hη₀, hη₀C, hη₀c, V, hV, hχV, _, hOne⟩ :=
    exists_projectedChartCutoff (test_compactSupport χ) c.chart.open_target hχ
  let η : D := ⟨η₀, hη₀, hη₀C⟩
  let e := inverseHalfDensityCutoff B hB hn c η hη₀c
  let he := (inverseHalfDensityCutoff_tsupport B hB hn c η hη₀c).trans hη₀c
  let U := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c d hd
  let W := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c e he
  have hU := fixedVolumeCovariantGradient_inverseHalfDensity_apply r B g hB hg hn c χ hχ
  have hW := fixedVolumeCovariantGradient_inverseHalfDensity_apply r B g hB hg hn c η hη₀c
  have hCut (n : ℕ) (k : JetSlot) : coeffMul χ (W n k) = U n k := by
    ext x
    change coeffMul χ (W n k) x = U n k x
    rw [coeffMul_apply, show W n k x = _ from hW n k x, show U n k x = _ from hU n k x]
    by_cases hx : x ∈ tsupport (χ : E → ℝ)
    · simp only [show (η : E → ℝ) x = 1 from hOne (hχV hx), Complex.ofReal_one, one_mul]
    · simp only [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, zero_mul]
  have hSource (n : ℕ) : coeffMul χ (firstOrderRow a v i b j (W n)) = F n := by
    ext x
    change coeffMul χ (firstOrderRow a v i b j (W n)) x = F n x
    rw [coeffMul_apply, firstOrderRow_eq_raw_apply, hF n x]
    by_cases hx : x ∈ tsupport (χ : E → ℝ)
    · have hNear (k : JetSlot) : (W n k : E → ℂ) =ᶠ[𝓝 x] receivingRawCovariantJet r B g c n k := by
        filter_upwards [hV.mem_nhds (hχV hx)] with y hy
        simp only [show W n k y = _ from hW n k y, show (η : E → ℝ) y = 1 from hOne hy,
          Complex.ofReal_one, one_mul]
      have hDer (k : JetSlot) : fderiv ℝ (W n k : E → ℂ) x =
          fderiv ℝ (receivingRawCovariantJet r B g c n k) x := (hNear k).fderiv_eq
      simp only [receivingRawFirstOrderRow, fun k => (hNear k).eq_of_nhds, hDer]
    · simp only [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, zero_mul]
  let L₂ := (fourierMultiplier besselSymbol).comp (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E))
  let G n := firstOrderRow a v i b j (U n)
  let q h := cutoffProduct (a h) (coefficientPDeriv χ (v h))
  have hComm (n : ℕ) : G n - F n = ∑ h, coeffMul (q h) (W n (i h)) := by
    simpa only [G, q, hCut, hSource, coeffMul_comp] using firstOrderRow_cutoff_sub a v i b j χ (W n)
  have hEach (h : J) : Tendsto (fun n => L₂ (coeffMul (q h) (W n (i h)))) atTop (𝓝 0) :=
    bessel_coeffMul_fixedVolumeCovariantGradient_tendsto_zero r B g hB hg hn hconv hb c e he (q h) (i h)
  have hError : Tendsto (fun n => L₂ (G n) - L₂ (F n)) atTop (𝓝 0) := by
    simp_rw [← map_sub, hComm, map_sum]
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun h _ => hEach h)
  have hBessel : Tendsto (fun n => L₂ (F n)) atTop (𝓝 0) :=
    (tendsto_besselLp_iff_negativeEnergy_tendsto_zero F).mpr hStrong
  change Tendsto (fun n => negativeEnergy (G n)) atTop (𝓝 0)
  apply (tendsto_besselLp_iff_negativeEnergy_tendsto_zero G).mp
  simpa only [sub_add_cancel, zero_add] using hError.add hBessel

end Burnett.Microlocal.Overlap
