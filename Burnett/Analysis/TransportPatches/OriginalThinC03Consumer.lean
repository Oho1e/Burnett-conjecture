import Burnett.Analysis.TransportPatches.OriginalWideC03Consumer
import Burnett.Analysis.TransportPatches.ThinComplementPatchL2
import Burnett.Analysis.TransportPatches.ThinComplementPatchStrong3
import Burnett.Analysis.TransportPatches.ThinConeWindowLp
import Burnett.Analysis.TransportPatches.ThinScreenErrorLpAssembly

/-! The two paper thin-screen gradient estimates on the original common patch witness. -/
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

/-- Fix the finite exponent and the actual thin-cone parameters before the
patch scale. The same original covariance and C03 field give both whole-space
gradient errors of the literal thin-screen physical replacement. -/
theorem exists_originalThinScreenL3_consumeC03Source
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target)
    (p : ℝ) (hp : 3 < p) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (Cp : {p : ℝ // 1 < p} → ℝ) (hCp : ∀ p, 0 ≤ Cp p)
    (κ δ c₀ thinInner thinOuter : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (hc₀ : 0 < c₀)
    (hIn : 0 < thinInner) (hIO : thinInner < thinOuter) :
    let η := c₀ * κ * δ ^ 2
    ∃ (i o Lw C ηw Lt : ℝ) (hf : ∀ x ∈ K, WideScreenFrequencySmooth i o (chartInverseMetric B c x)),
      0 < i ∧ i < o ∧ 0 ≤ Lw ∧ 0 ≤ C ∧ 0 < ηw ∧ 0 ≤ Lt ∧
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
  intro η
  have hη : 0 < η := by dsimp only [η]; positivity
  let qp : {q : ℝ // 1 < q} := ⟨p, by linarith⟩
  obtain ⟨i, o, Lw, Cw, ηw, hf, hi, hio, hLw, hCw, hηw, hWide⟩ :=
    exists_originalWideL3_consumeC03Source r B g hB hg hSig hconv σ hσ A hA hPair c K hK hConv hKU p hp e he Cp hCp
  obtain ⟨Lt, hLt, hThinZero⟩ := exists_thinComplement_subpatch_tendsto_zero r B g hB hg hSig.isSymmetric
    hSig.isNondegenerate hconv σ hσ A hA hPair c K hK hConv hKU
  obtain ⟨Ap, hAp, hThinLp⟩ := exists_chartThinScalar_window_Lp B c K hK hKU hB hSig.isNondegenerate
    η thinInner thinOuter hη p (by linarith)
  obtain ⟨A₃, hA₃, hThinL3⟩ := exists_chartThinScalar_window_Lp B c K hK hKU hB hSig.isNondegenerate
    η thinInner thinOuter hη 3 (by norm_num)
  let C := 64 * A₃ * Cw
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by norm_num) hA₃) hCw
  refine ⟨i, o, Lw, C, ηw, Lt, hf, hi, hio, hLw, hC, hηw, hLt, ?_⟩
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
