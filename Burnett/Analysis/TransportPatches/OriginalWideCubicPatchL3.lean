import Burnett.Analysis.TransportPatches.WidePatchGradientL2
import Burnett.Analysis.TransportPatches.WideWindowSphereJets
import Burnett.Analysis.TransportPatches.WideGradientVectorL3

/-! The actual two wide errors on a C01 cubic patch use the C03 projected input. -/
set_option autoImplicit false
set_option maxRecDepth 5400
set_option maxHeartbeats 7900000

noncomputable section

namespace Burnett.C02

open Set Metric Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol Burnett.Geometry
open Burnett.A02.FrequencySplit (E)
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (receivingCutoffFluctuation)
open Burnett.C03 (ProjectedPatchLpBounds)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- For each fixed finite p above three, one choice of full wide operators
works throughout the fixed compact convex chart window. Both endpoints use
the same original cutoff field and the outer ball of radius six times the
cubic patch scale. -/
theorem exists_originalWideL3_cubicWindow
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target)
    (p : ℝ) (hp : 3 < p) (B₂ Bₚ : ℝ) (hB₂ : 0 ≤ B₂) (hBₚ : 0 ≤ Bₚ) :
    ∃ (i o L C₃ η : ℝ) (hf : ∀ x ∈ K, WideScreenFrequencySmooth i o (chartInverseMetric B c x)),
      0 < i ∧ i < o ∧ 0 ≤ L ∧ 0 ≤ C₃ ∧ 0 < η ∧
      ∀ (ℓ : ℝ) (hℓ : 0 < ℓ), 6 * ℓ ≤ 1 → L * (6 * ℓ) ≤ η → ∀ (x₀ : E),
      let P := closedBall x₀ (6 * ℓ)
      ∀ (hPK : P ⊆ K) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ P),
      let hx₀ : x₀ ∈ P := mem_closedBall_self (mul_nonneg (by norm_num) hℓ.le)
      let m := chartInverseMetric B c x₀
      let hm := hf x₀ (hPK hx₀)
      let T₁ := actualFrozenScreenErrorMultiplier i o m hm
      let T₂ := actualFrozenPhaseErrorMultiplier i o m hm
      let z := receivingCutoffFluctuation B g hB hg c χ (hχ.trans (hPK.trans hKU))
      ∀ (val₂ valₚ : ℕ → ℝ),
        (∀ᶠ n in atTop, ProjectedPatchLpBounds 2 (z (σ n)) P (val₂ n) B₂) →
        (∀ᶠ n in atTop, ProjectedPatchLpBounds p (z (σ n)) P (valₚ n) Bₚ) →
        let R := C₃ * ℓ ^ frozenErrorExponent p * ((volume : Measure E) P).toReal ^ (1 / 3 : ℝ)
        (∀ n : ℕ, ∀ b : Index, ∀ k : OrderedPair,
          MemLp (multiplierCoordinateDerivative T₁ (z (σ n)) b k : E → ℂ) 3 volume ∧
          MemLp (multiplierCoordinateDerivative T₂ (z (σ n)) b k : E → ℂ) 3 volume) ∧
        ∀ ε > 0, ∀ᶠ n in atTop, ∀ b : Index, ∀ k : OrderedPair,
          (eLpNorm' (multiplierCoordinateDerivative T₁ (z (σ n)) b k : E → ℂ) 3 volume).toReal ≤ R + ε ∧
          (eLpNorm' (multiplierCoordinateDerivative T₂ (z (σ n)) b k : E → ℂ) 3 volume).toReal ≤ R + ε := by
  obtain ⟨i, o, L, C, η, V, hi, hio, hL, hC, hη, hVo, hKV, hVU, hJoint, hSlope⟩ :=
    exists_wideJointWindow (r := r) B hB hSig c K hK hConv hKU
  have hf (x : E) (hx : x ∈ K) : WideScreenFrequencySmooth i o (chartInverseMetric B c x) :=
    wideScreen_frequencySmooth_of_joint hJoint (hKV hx)
  obtain ⟨J, hJ, hJets⟩ := actualWideWindow_sphereJets B c K V hK hVo hKV hVU
    hB hSig.isNondegenerate i o hJoint hf
  obtain ⟨Ap, hAp, hInterp⟩ := exists_widePatchErrors_L3 p hp
  obtain ⟨_, _, hFinite⟩ := exists_actualWide_projectedGradient_Lp p (by linarith)
  let C₂ := 4 * C * (8 * B₂)
  let Cₚ := 16 * (Ap * J) * Bₚ
  let α := frozenErrorExponent p
  let C₃ := C₂ ^ α * Cₚ ^ (1 - α) * (6 : ℝ) ^ α
  have hC₂ : 0 ≤ C₂ := mul_nonneg (mul_nonneg (by norm_num) hC) (mul_nonneg (by norm_num) hB₂)
  have hCₚ : 0 ≤ Cₚ := mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hAp hJ)) hBₚ
  have hC₃ : 0 ≤ C₃ := mul_nonneg (mul_nonneg (Real.rpow_nonneg hC₂ _) (Real.rpow_nonneg hCₚ _))
    (Real.rpow_nonneg (by norm_num) _)
  refine ⟨i, o, L, C₃, η, hf, hi, hio, hL, hC₃, hη, ?_⟩
  intro ℓ hℓ hd₁ hSmall x₀ P hPK χ hχ hx₀ m hm T₁ T₂ z val₂ valₚ hProj₂ hProjₚ R
  refine ⟨?_, ?_⟩
  · intro n b k
    have h := hFinite i o m hm J hJ (hJets x₀ (hPK hx₀)) (z (σ n)) b k
    exact ⟨memLp_three_of_complexL2_and_finiteP p hp _ h.1.1,
      memLp_three_of_complexL2_and_finiteP p hp _ h.2.1⟩
  intro ε hε
  let vol := ((volume : Measure E) P).toReal
  have hP : IsCompact P := isCompact_closedBall _ _
  have hd (x : E) (hx : x ∈ P) : ‖x - x₀‖ ≤ 6 * ℓ := by
    rw [← dist_eq_norm]
    exact hx
  obtain ⟨h₀, h₁, h₂, hBound₁, hBound₂⟩ :=
    actualWideL2_of_ricciRangeSlope r B g hB hg hSig hconv σ hσ A hA hPair c K hKU i o L C η hC hf hSlope
      P hPK hP x₀ hx₀ (6 * ℓ) hd hd₁ hSmall χ hχ
  let τ := A.control.restrict (amplitudeCosphereWindow r (c.chart.symm '' P))
  let N (T : ClassicalMatrixMultiplier OrderedPair) := Real.sqrt (∫ q, globalDefectNormIntegrand B c χ T A q ∂τ)
  have hBase : ∀ᶠ n in atTop, orderedGradientL2Norm originalProjectedMatrixMultiplier (z (σ n)) ≤
      8 * B₂ * vol ^ (1 / 2 : ℝ) := hProj₂.mono (fun n hn =>
        orderedOriginalGradientL2_le_of_projectedPatchLp (z (σ n)) P (val₂ n) B₂ hB₂ hn)
  have hN₀ : N originalProjectedMatrixMultiplier ≤ 8 * B₂ * vol ^ (1 / 2 : ℝ) := le_of_tendsto h₀ hBase
  have hScale : 0 ≤ 4 * C * (6 * ℓ) := by positivity
  have hScaleEq : 4 * C * (6 * ℓ) * (8 * B₂ * vol ^ (1 / 2 : ℝ)) =
      C₂ * (6 * ℓ) * vol ^ (1 / 2 : ℝ) := by dsimp only [C₂]; ring
  have hLim₁ : N T₁ ≤ C₂ * (6 * ℓ) * vol ^ (1 / 2 : ℝ) :=
    hBound₁.trans ((mul_le_mul_of_nonneg_left hN₀ hScale).trans_eq hScaleEq)
  have hLim₂ : N T₂ ≤ C₂ * (6 * ℓ) * vol ^ (1 / 2 : ℝ) :=
    hBound₂.trans ((mul_le_mul_of_nonneg_left hN₀ hScale).trans_eq hScaleEq)
  have hL₂ (t : ℝ) (ht : 0 < t) : ∀ᶠ n in atTop,
      orderedGradientL2Norm T₁ (z (σ n)) ≤ C₂ * (6 * ℓ) * vol ^ (1 / 2 : ℝ) + t ∧
      orderedGradientL2Norm T₂ (z (σ n)) ≤ C₂ * (6 * ℓ) * vol ^ (1 / 2 : ℝ) + t := by
    filter_upwards [h₁.eventually (Iio_mem_nhds (hLim₁.trans_lt (lt_add_of_pos_right _ ht))),
      h₂.eventually (Iio_mem_nhds (hLim₂.trans_lt (lt_add_of_pos_right _ ht)))] with n hn₁ hn₂
    exact ⟨hn₁.le, hn₂.le⟩
  have hResult := hInterp i o m hm J hJ (hJets x₀ (hPK hx₀)) (fun n => z (σ n)) P hP
    C₂ Bₚ (6 * ℓ) hC₂ hBₚ (by positivity) valₚ hL₂ hProjₚ ε hε
  have hRescale : C₂ ^ α * Cₚ ^ (1 - α) * (6 * ℓ) ^ α * vol ^ (1 / 3 : ℝ) = R := by
    rw [Real.mul_rpow (by norm_num) hℓ.le]
    simp only [R, C₃, vol, α, mul_assoc]
  change (∀ᶠ n in atTop, ∀ b : Index, ∀ k : OrderedPair,
    (eLpNorm' (multiplierCoordinateDerivative T₁ (z (σ n)) b k : E → ℂ) 3 volume).toReal ≤
      C₂ ^ α * Cₚ ^ (1 - α) * (6 * ℓ) ^ α * vol ^ (1 / 3 : ℝ) + ε ∧
    (eLpNorm' (multiplierCoordinateDerivative T₂ (z (σ n)) b k : E → ℂ) 3 volume).toReal ≤
      C₂ ^ α * Cₚ ^ (1 - α) * (6 * ℓ) ^ α * vol ^ (1 / 3 : ℝ) + ε) at hResult
  rwa [hRescale] at hResult

end Burnett.C02
