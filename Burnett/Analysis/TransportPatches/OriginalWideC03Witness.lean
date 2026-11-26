import Burnett.Analysis.FrozenTransport.UniformOriginalThinCubicFamily

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
theorem exists_originalWideL3_cubicWindow_withJointScreen
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target)
    (p : ℝ) (hp : 3 < p) (B₂ Bₚ : ℝ) (hB₂ : 0 ≤ B₂) (hBₚ : 0 ≤ Bₚ) :
    ∃ (i o L C₃ η : ℝ) (V : Set E) (hf : ∀ x ∈ K, WideScreenFrequencySmooth i o (chartInverseMetric B c x)),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ c.chart.target ∧ HasJointWideScreen B c i o V ∧
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
  refine ⟨i, o, L, C₃, η, V, hf, hVo, hKV, hVU, hJoint, hi, hio, hL, hC₃, hη, ?_⟩
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
theorem exists_originalWideL3_consumeC03Source_withJointScreen
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target)
    (p : ℝ) (hp : 3 < p) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (Cp : {p : ℝ // 1 < p} → ℝ) (hCp : ∀ p, 0 ≤ Cp p) :
    ∃ (i o L C η : ℝ) (V : Set E) (hf : ∀ x ∈ K, WideScreenFrequencySmooth i o (chartInverseMetric B c x)),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ c.chart.target ∧ HasJointWideScreen B c i o V ∧
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
  obtain ⟨i, o, L, C, η, V, hf, hVo, hKV, hVU, hJoint, hi, hio, hL, hC, hη, hWindow⟩ :=
    exists_originalWideL3_cubicWindow_withJointScreen r B g hB hg hSig hconv σ hσ A hA hPair c K hK hConv hKU p hp
      (2 * Cp q₂) (2 * Cp qₚ) (mul_nonneg (by norm_num) (hCp q₂)) (mul_nonneg (by norm_num) (hCp qₚ))
  refine ⟨i, o, L, 64 * C, η, V, hf, hVo, hKV, hVU, hJoint, hi, hio, hL, mul_nonneg (by norm_num) hC, hη, ?_⟩
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

/-! The two paper thin-screen gradient estimates on the original common patch witness. -/
