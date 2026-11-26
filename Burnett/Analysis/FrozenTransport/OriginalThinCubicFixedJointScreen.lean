import Burnett.Analysis.TransportPatches.OriginalWideC03Witness

set_option autoImplicit false
set_option maxRecDepth 5700
set_option maxHeartbeats 11000000

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
open scoped ContDiff ENNReal Manifold Topology

local notation "GradSlot" => Index × OrderedPair

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- Choose the wide cutoffs and their joint collar before varying the
thin-cone parameters and the patch scale. The same original covariance and C03 field give both whole-space
gradient errors of the literal thin-screen physical replacement. -/
theorem exists_originalThinScreenL3_consumeC03Source_withFixedJointScreen
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target)
    (p : ℝ) (hp : 3 < p) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (Cp : {p : ℝ // 1 < p} → ℝ) (hCp : ∀ p, 0 ≤ Cp p) :
    ∃ (i o Lw ηw : ℝ) (V : Set E) (hf : ∀ x ∈ K, WideScreenFrequencySmooth i o (chartInverseMetric B c x)),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ c.chart.target ∧ HasJointWideScreen B c i o V ∧
      0 < i ∧ i < o ∧ 0 ≤ Lw ∧ 0 < ηw ∧
      ∀ (κ δ c₀ thinInner thinOuter : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (hc₀ : 0 < c₀)
        (hIn : 0 < thinInner) (hIO : thinInner < thinOuter),
      let η := c₀ * κ * δ ^ 2
      ∃ C Lt : ℝ, 0 ≤ C ∧ 0 ≤ Lt ∧
      ∀ (ℓ : ℝ) (hℓ : 0 < ℓ), 6 * ℓ ≤ 1 → Lw * (6 * ℓ) ≤ ηw → Lt * (6 * ℓ) ≤ thinInner * η →
      ∀ j : LatticeIndex,
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
      let T := actualThinScreenMultiplier m i o hm (show 0 < η by positivity) thinInner thinOuter
      let diff (n : ℕ) (a : GradSlot) := multiplierCoordinateDerivative originalProjectedMatrixMultiplier (z (σ n)) a.1 a.2 -
        multiplierCoordinateDerivative T (z (σ n)) a.1 a.2
      let phase (n : ℕ) (a : GradSlot) := fourierMultiplier (frozenPhaseScalar m)
        (multiplierCoordinateDerivative T (z (σ n)) a.1 a.2)
      let R := C * ℓ ^ frozenErrorExponent p * ((volume : Measure E) P).toReal ^ (1 / 3 : ℝ)
      (∀ n : ℕ, MemLp (orderedGradientValue (diff n)) 3 volume ∧
        MemLp (orderedGradientValue (phase n)) 3 volume) ∧
      ∀ ε > 0, ∀ᶠ n in atTop,
        (eLpNorm (orderedGradientValue (diff n)) 3 volume).toReal ≤ R + ε ∧
        (eLpNorm (orderedGradientValue (phase n)) 3 volume).toReal ≤ R + ε := by
  obtain ⟨i, o, Lw, Cw, ηw, V, hf, hVo, hKV, hVU, hJoint, hi, hio, hLw, hCw, hηw, hWide⟩ :=
    exists_originalWideL3_consumeC03Source_withJointScreen r B g hB hg hSig hconv σ hσ A hA hPair c K hK hConv hKU p hp e he Cp hCp
  refine ⟨i, o, Lw, ηw, V, hf, hVo, hKV, hVU, hJoint, hi, hio, hLw, hηw, ?_⟩
  intro κ δ c₀ thinInner thinOuter hκ hδ hc₀ hIn hIO η
  have hη : 0 < η := by dsimp only [η]; positivity
  let qp : {q : ℝ // 1 < q} := ⟨p, by linarith⟩
  obtain ⟨Lt, hLt, hThinZero⟩ := exists_thinComplement_subpatch_tendsto_zero r B g hB hg hSig.isSymmetric
    hSig.isNondegenerate hconv σ hσ A hA hPair c K hK hConv hKU
  obtain ⟨Ap, hAp, hThinLp⟩ := exists_chartThinScalar_window_Lp B c K hK hKU hB hSig.isNondegenerate
    η thinInner thinOuter hη p (by linarith)
  obtain ⟨A₃, hA₃, hThinL3⟩ := exists_chartThinScalar_window_Lp B c K hK hKU hB hSig.isNondegenerate
    η thinInner thinOuter hη 3 (by norm_num)
  let C := 64 * A₃ * Cw
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by norm_num) hA₃) hCw
  refine ⟨C, Lt, hC, hLt, ?_⟩
  intro ℓ hℓ hd hSmall hThinSmall j x₀ P hPK χ hDiff hχ hSource dχ z m hm T diff phase R
  have hP : IsCompact P := isCompact_closedBall _ _
  have hx₀ : x₀ ∈ P := mem_closedBall_self (mul_nonneg (by norm_num) hℓ.le)
  have hDist (x : E) (hx : x ∈ P) : ‖x - x₀‖ ≤ 6 * ℓ := by
    rw [← dist_eq_norm]
    exact hx
  obtain ⟨hMem, hRate⟩ := hWide ℓ hℓ hd hSmall j hPK χ hDiff hχ hSource
  have hBounds := eventually_receivingProjectedPatchLp_of_source B g hB hg c dχ
    (hχ.trans (hPK.trans hKU)) P ℓ hℓ σ hσ e he Cp hCp hSource
  have hZero := hThinZero P hPK hP x₀ hx₀ (6 * ℓ) hDist η thinInner thinOuter hη hIn.le hIO hThinSmall dχ hχ
  have hCompP (f : ComplexL2 E) (hF : MemLp (f : E → ℂ) (ENNReal.ofReal p) volume) :
      let F := fourierMultiplier (thinComplementScalar m hη thinInner thinOuter) f
      MemLp (F : E → ℂ) (ENNReal.ofReal p) volume ∧
        (eLpNorm (F : E → ℂ) (ENNReal.ofReal p) volume).toReal ≤
          Ap * (eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume).toReal :=
    (hThinLp x₀ (hPK hx₀) f hF).2
  obtain ⟨hCompMem, hCompZero⟩ := thinComplement_strong3_of_projectedPatchLp p hp m hη thinInner thinOuter
    Ap hAp hCompP (fun n => z (σ n)) P (2 * Cp qp) (fun n => Cp qp * e (σ n))
    (hBounds.mono (fun _ h => h qp)) hZero
  have hS (f : ComplexL2 E) (hF : MemLp (f : E → ℂ) 3 volume) :
      let F := fourierMultiplier (thinConeScalar m hη thinInner thinOuter) f
      MemLp (F : E → ℂ) 3 volume ∧
        (eLpNorm (F : E → ℂ) 3 volume).toReal ≤ A₃ * (eLpNorm (f : E → ℂ) 3 volume).toReal := by
    have h3 : ENNReal.ofReal (3 : ℝ) = 3 := by norm_num
    have hF' : MemLp (f : E → ℂ) (ENNReal.ofReal 3) volume := h3.symm ▸ hF
    simpa only [h3] using (hThinL3 x₀ (hPK hx₀) f hF').1
  let Rw := Cw * ℓ ^ frozenErrorExponent p * ((volume : Measure E) P).toReal ^ (1 / 3 : ℝ)
  obtain ⟨hOut, hBound⟩ := actualThinScreen_gradient_errors_L3_of_wide m i o hm hη thinInner thinOuter
    (fun n => z (σ n)) A₃ Rw hA₃ hS hMem hRate hCompMem hCompZero
  refine ⟨hOut, ?_⟩
  have hRescale : 64 * A₃ * Rw = R := by dsimp only [Rw, R, C]; ring
  simpa only [hRescale] using hBound

end Burnett.C02

set_option autoImplicit false
set_option maxRecDepth 5900
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.C02

open Set Metric Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol Burnett.Geometry
open Burnett.A02.FrequencySplit
open ConnectionDifference ManifoldVolume ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.Overlap Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix receivingCutoffFluctuation)
open Burnett.C03 (ProjectedPatchLpBounds)
open Burnett.C01 (patchCenter)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.X02.SobolevTestJet (D)
open scoped ComplexConjugate ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The same actual wide screen supports the complete cubic replacement
for every subsequent thin choice on the receiving chart. -/
theorem exists_uniform_originalThinCubicC03Replacement_withFixedJointScreen
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target)
    (p : ℝ) (hp : 3 < p) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (Cp : {p : ℝ // 1 < p} → ℝ) (hCp : ∀ p, 0 ≤ Cp p)
    (cut add : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ) (D₀ : ℝ) (hD₀ : 0 ≤ D₀) :
    ∃ (i o Lw ηw : ℝ) (V : Set E) (hf : ∀ x ∈ K, WideScreenFrequencySmooth i o (chartInverseMetric B c x)),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ c.chart.target ∧ HasJointWideScreen B c i o V ∧
      0 < i ∧ i < o ∧ 0 ≤ Lw ∧ 0 < ηw ∧
      ∀ (κ δ c₀ thinInner thinOuter : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (hc₀ : 0 < c₀)
        (hIn : 0 < thinInner) (hIO : thinInner < thinOuter),
      let η := c₀ * κ * δ ^ 2
      ∃ Cerror Ccubic Lt : ℝ, 0 ≤ Cerror ∧ 0 ≤ Ccubic ∧ 0 ≤ Lt ∧
      ∀ (ℓ : ℝ) (hℓ : 0 < ℓ), 6 * ℓ ≤ 1 → Lw * (6 * ℓ) ≤ ηw → Lt * (6 * ℓ) ≤ thinInner * η →
      ∀ j : LatticeIndex,
      let x₀ := patchCenter ℓ j
      let P := closedBall x₀ (6 * ℓ)
      ∀ (hPK : P ⊆ K) (χ : E → ℝ) (hDiff : ContDiff ℝ ∞ χ) (hχ : tsupport χ ⊆ P),
      (∀ᶠ n in atTop, ∃ z : ProjectionSchwartzMatrix,
        (∀ a b x, z a b x = ((χ x *
          (metricComponents (fixedForm (g n) c) x a b - metricComponents (fixedForm B c) x a b) : ℝ) : ℂ)) ∧
        ∀ q : {q : ℝ // 1 < q}, ProjectedPatchLpBounds q.val z P (Cp q * e n) (Cp q * (1 + e n / ℓ))) →
      let dχ : D := ⟨χ, hDiff, (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hχ⟩
      let z (n : ℕ) := receivingCutoffFluctuation B g hB hg c dχ (hχ.trans (hPK.trans hKU)) (σ n)
      let m := chartInverseMetric B c x₀
      let γ := metricComponents (fixedForm B c) x₀
      let hm := hf x₀ (hPK (mem_closedBall_self (mul_nonneg (by norm_num) hℓ.le)))
      let hη : 0 < η := by positivity
      let hz (n : ℕ) (a b : Index) (x : E) : conj (z n a b x) = z n a b x := Complex.conj_ofReal _
      let T := actualThinScreenMultiplier m i o hm hη thinInner thinOuter
      let u (n : ℕ) := originalCubicPhysical (z n) (hz n)
      let v (n : ℕ) := originalCubicThinScreen m i o hm hη thinInner thinOuter (z n) (hz n)
      let G (n : ℕ) := originalCubicGauge (z n) (hz n)
      let phase (n : ℕ) (a : Index × OrderedPair) := fourierMultiplier (frozenPhaseScalar m)
        (multiplierCoordinateDerivative T (z n) a.1 a.2)
      let mass := ((volume : Measure E) P).toReal
      ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} → (∀ a : ℝ, 0 < a → ∀ ξ, b (a • ξ) = a * b ξ) →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D₀) →
      ∀ ε > 0, ∀ᶠ n in atTop,
        |completeCubicEnergy (frozenActionCubicLinear γ) (frozenActionCubicQuadratic γ)
            (fixedInfraredSymbol cut add b) (u n + G n) -
          completeCubicEnergy (frozenActionCubicLinear γ) (frozenActionCubicQuadratic γ)
            (fixedInfraredSymbol cut add b) (v n + G n)| ≤
          Ccubic * ℓ ^ frozenErrorExponent p * mass + ε ∧
        (eLpNorm (orderedGradientValue (phase n)) 3 volume).toReal ≤
          Cerror * ℓ ^ frozenErrorExponent p * mass ^ (1 / 3 : ℝ) + ε := by
  obtain ⟨i, o, Lw, ηw, V, hf, hVo, hKV, hVU, hJoint, hi, hio, hLw, hηw, hThinAll⟩ :=
    exists_originalThinScreenL3_consumeC03Source_withFixedJointScreen r B g hB hg hSig hconv σ hσ A hA hPair c K hK hConv hKU p hp e he Cp hCp
  refine ⟨i, o, Lw, ηw, V, hf, hVo, hKV, hVU, hJoint, hi, hio, hLw, hηw, ?_⟩
  intro κ δ c₀ thinInner thinOuter hκ hδ hc₀ hIn hIO η
  obtain ⟨Ce, Lt, hCe, hLt, hThin⟩ := hThinAll κ δ c₀ thinInner thinOuter hκ hδ hc₀ hIn hIO
  obtain ⟨M₀, hM₀, hBox⟩ := exists_receivingFrozenCubicCoefficient_box B hB hSig.isNondegenerate c K hK hKU
  obtain ⟨C, hC, hCube⟩ := exists_uniform_completeCubic_actualThinReplacement cut add hcut hadd
  let q₃ : {q : ℝ // 1 < q} := ⟨3, by norm_num⟩
  let grad := 2 * Cp q₃
  let Ccub := C * M₀ * (D₀ + 1) * Ce * (4 * (64 * grad) + Ce)^2
  have hGrad : 0 ≤ grad := mul_nonneg (by norm_num) (hCp _)
  refine ⟨Ce, Ccub, Lt, hCe, by positivity, hLt, ?_⟩
  intro ℓ hℓ hEll hWide hThinSmall j x₀ P hPK χ hχ₀ hχ hSource dχ z m γ hm hη hz T u v G phase mass
    b hb hom jet ε hε
  obtain ⟨_, hErrors⟩ := hThin ℓ hℓ hEll hWide hThinSmall j hPK χ hχ₀ hχ hSource
  have hx₀ : x₀ ∈ K := hPK (mem_closedBall_self (mul_nonneg (by norm_num) hℓ.le))
  obtain ⟨hLin, hQuad⟩ := hBox x₀ hx₀
  have hSourceReal : ∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (z n) P (Cp q₃ * e (σ n)) grad := by
    have hBounds := eventually_receivingProjectedPatchLp_of_source B g hB hg c dχ
      (hχ.trans (hPK.trans hKU)) P ℓ hℓ σ hσ e he Cp hCp hSource
    exact hBounds.mono fun _ h => h q₃
  have hValue : Tendsto (fun n => Cp q₃ * e (σ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (he.comp hσ.tendsto_atTop)
  have hRate := hCube M₀ hM₀ (frozenActionCubicLinear γ) (frozenActionCubicQuadratic γ)
    (frozenActionCubicLinear_symmetry γ) hLin hQuad b hb hom D₀ hD₀ jet m i o hm η hη thinInner thinOuter z hz P
    (fun n => Cp q₃ * e (σ n)) grad Ce ℓ (frozenErrorExponent p) hGrad hCe hℓ.le
    (by linarith only [hEll]) (frozenErrorExponent_bounds hp).1.le hValue hSourceReal
    (fun ε hε => (hErrors ε hε).mono fun _ h => h.1)
  filter_upwards [hRate ε hε, hErrors ε hε] with n hc hf
  exact ⟨hc, hf.2⟩

end Burnett.C02
