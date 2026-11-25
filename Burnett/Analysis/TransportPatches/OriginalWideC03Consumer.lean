import Burnett.Analysis.TransportPatches.OriginalWideCubicPatchL3
import Burnett.Analysis.TransportPatches.OriginalC03PatchFiniteEndpoints

/-! Apply C02 to the cutoffs and Schwartz field already selected by C03. -/
set_option autoImplicit false
set_option maxRecDepth 5200
set_option maxHeartbeats 7300000

noncomputable section

namespace Burnett.C02

open Set Metric Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol Burnett.Geometry
open Burnett.A02.FrequencySplit (E)
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix receivingCutoffFluctuation)
open Burnett.C03 (ProjectedPatchLpBounds)
open Burnett.C01 (patchCenter)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The selected C03 patch is passed in by its center, exact cutoff and
source witness. This theorem applies the C02 errors to that same field. -/
theorem exists_originalWideL3_consumeC03Source
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target)
    (p : ℝ) (hp : 3 < p) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (Cp : {p : ℝ // 1 < p} → ℝ) (hCp : ∀ p, 0 ≤ Cp p) :
    ∃ (i o L C η : ℝ) (hf : ∀ x ∈ K, WideScreenFrequencySmooth i o (chartInverseMetric B c x)),
      0 < i ∧ i < o ∧ 0 ≤ L ∧ 0 ≤ C ∧ 0 < η ∧
      ∀ (ℓ : ℝ) (hℓ : 0 < ℓ), 6 * ℓ ≤ 1 → L * (6 * ℓ) ≤ η → ∀ j : LatticeIndex,
      let x₀ := patchCenter ℓ j
      let P := closedBall x₀ (6 * ℓ)
      ∀ (hPK : P ⊆ K) (χ : E → ℝ) (hDiff : ContDiff ℝ ∞ χ) (hχ : tsupport χ ⊆ P),
      (∀ᶠ n in atTop, ∃ z : ProjectionSchwartzMatrix,
        (∀ a b x, z a b x = ((χ x *
          (metricComponents (fixedForm (g n) c) x a b - metricComponents (fixedForm B c) x a b) : ℝ) : ℂ)) ∧
        ∀ q : {q : ℝ // 1 < q}, ProjectedPatchLpBounds q.val z P (Cp q * e n) (Cp q * (1 + e n / ℓ))) →
      let dχ : D := ⟨χ, hDiff, (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hχ⟩
      let z := receivingCutoffFluctuation B g hB hg c dχ (hχ.trans (hPK.trans hKU))
      let m := chartInverseMetric B c x₀
      let hm := hf x₀ (hPK (mem_closedBall_self (mul_nonneg (by norm_num) hℓ.le)))
      let T₁ := actualFrozenScreenErrorMultiplier i o m hm
      let T₂ := actualFrozenPhaseErrorMultiplier i o m hm
      let f₁ (n : ℕ) (a : Index × OrderedPair) := multiplierCoordinateDerivative T₁ (z (σ n)) a.1 a.2
      let f₂ (n : ℕ) (a : Index × OrderedPair) := multiplierCoordinateDerivative T₂ (z (σ n)) a.1 a.2
      let R := C * ℓ ^ frozenErrorExponent p * ((volume : Measure E) P).toReal ^ (1 / 3 : ℝ)
      (∀ n : ℕ, MemLp (orderedGradientValue (f₁ n)) 3 volume ∧
        MemLp (orderedGradientValue (f₂ n)) 3 volume) ∧
      ∀ ε > 0, ∀ᶠ n in atTop,
        (eLpNorm (orderedGradientValue (f₁ n)) 3 volume).toReal ≤ R + ε ∧
        (eLpNorm (orderedGradientValue (f₂ n)) 3 volume).toReal ≤ R + ε := by
  let q₂ : {q : ℝ // 1 < q} := ⟨2, by norm_num⟩
  let qₚ : {q : ℝ // 1 < q} := ⟨p, by linarith⟩
  obtain ⟨i, o, L, C, η, hf, hi, hio, hL, hC, hη, hWindow⟩ :=
    exists_originalWideL3_cubicWindow r B g hB hg hSig hconv σ hσ A hA hPair c K hK hConv hKU p hp
      (2 * Cp q₂) (2 * Cp qₚ) (mul_nonneg (by norm_num) (hCp q₂)) (mul_nonneg (by norm_num) (hCp qₚ))
  refine ⟨i, o, L, 64 * C, η, hf, hi, hio, hL, mul_nonneg (by norm_num) hC, hη, ?_⟩
  intro ℓ hℓ hd hSmall j x₀ P hPK χ hDiff hχ hSource dχ z m hm T₁ T₂ f₁ f₂ R
  have hBounds := eventually_receivingProjectedPatchLp_of_source B g hB hg c dχ
    (hχ.trans (hPK.trans hKU)) P ℓ hℓ σ hσ e he Cp hCp hSource
  obtain ⟨hMembership, hRows⟩ := hWindow ℓ hℓ hd hSmall x₀ hPK dχ hχ
    (fun n => Cp q₂ * e (σ n)) (fun n => Cp qₚ * e (σ n))
    (hBounds.mono (fun _ h => h q₂)) (hBounds.mono (fun _ h => h qₚ))
  have hMem₁ (n : ℕ) (a : Index × OrderedPair) : MemLp (f₁ n a : E → ℂ) 3 volume :=
    (hMembership n a.1 a.2).1
  have hMem₂ (n : ℕ) (a : Index × OrderedPair) : MemLp (f₂ n a : E → ℂ) 3 volume :=
    (hMembership n a.1 a.2).2
  refine ⟨fun n => ⟨(orderedGradientValue_L3_le_sum (f₁ n) (hMem₁ n)).1,
    (orderedGradientValue_L3_le_sum (f₂ n) (hMem₂ n)).1⟩, ?_⟩
  let Rrow := C * ℓ ^ frozenErrorExponent p * ((volume : Measure E) P).toReal ^ (1 / 3 : ℝ)
  have hEq : 64 * Rrow = R := by dsimp [Rrow, R]; ring
  intro ε hε
  have hOne := orderedGradientValue_eventually_L3 f₁ Rrow hMem₁
    (fun t ht => (hRows t ht).mono (fun _ h a => (h a.1 a.2).1)) ε hε
  have hTwo := orderedGradientValue_eventually_L3 f₂ Rrow hMem₂
    (fun t ht => (hRows t ht).mono (fun _ h a => (h a.1 a.2).2)) ε hε
  simpa only [hEq] using hOne.and hTwo

end Burnett.C02
