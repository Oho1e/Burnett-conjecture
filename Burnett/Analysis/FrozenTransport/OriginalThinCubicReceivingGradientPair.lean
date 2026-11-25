import Burnett.Analysis.FrozenTransport.OriginalThinCubicGradientPair
import Burnett.Analysis.FrozenTransport.PatchCorrection.OriginalFrequencyTestJets

set_option autoImplicit false
set_option maxRecDepth 5700
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.C02

open Set Metric Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol Burnett.Geometry
open Burnett.A02.FrequencySplit (E Joint fixedInfraredSymbol completeCubicEnergy)
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix receivingCutoffFluctuation)
open Burnett.C03 (ProjectedPatchLpBounds)
open Burnett.C01 (patchCenter)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.X02.SobolevTestJet (D)
open scoped ComplexConjugate ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The fixed joint wide-screen witness applies to the entire finite family
of original C03 cutoffs. The same scalar test gives both complete cubic
replacement and both normalized gradient errors for the canonical C02 field. -/
theorem exists_originalThinCubicReceivingFamily_withFixedJointScreen_andGradientPair
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (c : AtlasChart M) (Kplus Kwide : Set E) (hKplus : IsCompact Kplus) (hKwide : IsCompact Kwide)
    (hConvex : Convex ℝ Kwide) (hKpW : Kplus ⊆ Kwide) (hKWU : Kwide ⊆ c.chart.target)
    (p : ℝ) (hp : 3 < p) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (Cp : {q : ℝ // 1 < q} → ℝ) (hCp : ∀ q, 0 ≤ Cp q)
    (cut add : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ) (a : Joint → ℝ)
    (ha : ContDiffOn ℝ ∞ a (c.chart.target ×ˢ {ξ : E | ξ ≠ 0}))
    (hom : ∀ x ∈ Kplus, ∀ t : ℝ, 0 < t → ∀ ξ : E, a (x, t • ξ) = t * a (x, ξ)) :
    ∃ (i o Lw ηw : ℝ) (V : Set E) (hf : ∀ x ∈ Kwide, WideScreenFrequencySmooth i o (chartInverseMetric B c x)),
      IsOpen V ∧ Kwide ⊆ V ∧ V ⊆ c.chart.target ∧ HasJointWideScreen B c i o V ∧
      0 < i ∧ i < o ∧ 0 ≤ Lw ∧ 0 < ηw ∧
      ∀ (κ δ cThin inn out : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (hcThin : 0 < cThin)
        (hin : 0 < inn) (hio : inn < out),
      let η := cThin * κ * δ ^ 2
      let hη : 0 < η := by dsimp only [η]; positivity
      ∃ Cerror Ccubic Lt : ℝ, 0 ≤ Cerror ∧ 0 ≤ Ccubic ∧ 0 ≤ Lt ∧
      ∀ (ℓ : ℝ) (hℓ : 0 < ℓ), 6 * ℓ ≤ 1 → Lw * (6 * ℓ) ≤ ηw → Lt * (6 * ℓ) ≤ inn * η →
      ∀ (s : Finset LatticeIndex) (χ : LatticeIndex → E → ℝ),
      let W (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6 * ℓ)
      ∀ (hCuts : ∀ j ∈ s, ContDiff ℝ ∞ (χ j) ∧ tsupport (χ j) ⊆ W j ∧ W j ⊆ Kplus),
      (∀ j ∈ s, ∀ᶠ n in atTop, ∃ z : ProjectionSchwartzMatrix,
        (∀ i k x, z i k x = ((χ j x * (metricComponents (fixedForm (g n) c) x i k -
          metricComponents (fixedForm B c) x i k) : ℝ) : ℂ)) ∧
        ∀ q : {q : ℝ // 1 < q}, ProjectedPatchLpBounds q.val z (W j) (Cp q * e n) (Cp q * (1 + e n / ℓ))) →
      let x₀ (j : s) := patchCenter ℓ j
      let m (j : s) := chartInverseMetric B c (x₀ j)
      let γ (j : s) := metricComponents (fixedForm B c) (x₀ j)
      let hCenter (j : s) : x₀ j ∈ Kplus :=
        (hCuts j j.property).2.2 (mem_closedBall_self (mul_nonneg (by norm_num) hℓ.le))
      let hm (j : s) := hf (x₀ j) (hKpW (hCenter j))
      let dχ (j : s) : D := ⟨χ j, (hCuts j j.property).1,
        (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure (hCuts j j.property).2.1⟩
      let hχU (j : s) : tsupport (dχ j : E → ℝ) ⊆ c.chart.target :=
        (hCuts j j.property).2.1.trans ((hCuts j j.property).2.2.trans (hKpW.trans hKWU))
      let z (j : s) (n : ℕ) := receivingCutoffFluctuation B g hB hg c (dχ j) (hχU j) (σ n)
      let hz (j : s) (n : ℕ) (i k : Index) (x : E) : conj (z j n i k x) = z j n i k x :=
        Complex.conj_ofReal _
      let u (j : s) (n : ℕ) := originalCubicPhysical (z j n) (hz j n)
      let v (j : s) (n : ℕ) := originalCubicThinScreen (m j) i o (hm j) hη inn out (z j n) (hz j n)
      let G (j : s) (n : ℕ) := originalCubicGauge (z j n) (hz j n)
      let diff (j : s) (n : ℕ) (k : Index × OrderedPair) :=
        multiplierCoordinateDerivative originalProjectedMatrixMultiplier (z j n) k.1 k.2 -
          multiplierCoordinateDerivative (actualThinScreenMultiplier (m j) i o (hm j) hη inn out)
            (z j n) k.1 k.2
      let phase (j : s) (n : ℕ) (k : Index × OrderedPair) := fourierMultiplier (frozenPhaseScalar (m j))
        (multiplierCoordinateDerivative (actualThinScreenMultiplier (m j) i o (hm j) hη inn out)
          (z j n) k.1 k.2)
      (∀ (j : s) (n : ℕ), MemLp (orderedGradientValue (diff j n)) 3 volume ∧
        MemLp (orderedGradientValue (phase j n)) 3 volume) ∧
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ j : s,
        let symbol := fixedInfraredSymbol cut add (fun ξ => a (x₀ j, ξ))
        let mass := ((volume : Measure E) (W j)).toReal
        |completeCubicEnergy (frozenActionCubicLinear (γ j)) (frozenActionCubicQuadratic (γ j))
            symbol (u j n + G j n) -
          completeCubicEnergy (frozenActionCubicLinear (γ j)) (frozenActionCubicQuadratic (γ j))
            symbol (v j n + G j n)| ≤ Ccubic * ℓ ^ frozenErrorExponent p * mass + ε ∧
        (eLpNorm (orderedGradientValue (diff j n)) 3 volume).toReal ≤
          Cerror * ℓ ^ frozenErrorExponent p * mass ^ (1 / 3 : ℝ) + ε ∧
        (eLpNorm (orderedGradientValue (phase j n)) 3 volume).toReal ≤
          Cerror * ℓ ^ frozenErrorExponent p * mass ^ (1 / 3 : ℝ) + ε := by
  classical
  obtain ⟨D₀, hD₀, jets⟩ := Burnett.V11.exists_uniform_originalFrequencyTest_jets
    c.chart.target Kplus c.chart.open_target hKplus (hKpW.trans hKWU) a ha 16
  obtain ⟨i, o, Lw, ηw, V, hf, hV, hKV, hVU, hJoint, hi, hio, hLw, hηw, thin⟩ :=
    exists_uniform_originalThinCubicC03Replacement_withFixedJointScreen_andGradientPair r B g hB hg hSig hconv
      σ hσ A hA hPair c Kwide hKwide hConvex hKWU p hp e he Cp hCp cut add hcut hadd D₀ hD₀
  refine ⟨i, o, Lw, ηw, V, hf, hV, hKV, hVU, hJoint, hi, hio, hLw, hηw, ?_⟩
  intro κ δ cThin inn out hκ hδ hcThin hin hio' η hη
  obtain ⟨Cerror, Ccubic, Lt, hCe, hCc, hLt, estimate⟩ := thin κ δ cThin inn out hκ hδ hcThin hin hio'
  refine ⟨Cerror, Ccubic, Lt, hCe, hCc, hLt, ?_⟩
  intro ℓ hℓ hSix hWide hThin s χ W hCuts hRaw x₀ m γ hCenter hm dχ hχU z hz u v G diff phase
  have each (j : s) := estimate ℓ hℓ hSix hWide hThin j
    ((hCuts j j.property).2.2.trans hKpW) (χ j) (hCuts j j.property).1 (hCuts j j.property).2.1
    (hRaw j j.property)
  refine ⟨fun j n => (each j).1 n, ?_⟩
  intro ε hε
  refine eventually_all.2 fun j => ?_
  have hFiber : ContDiffOn ℝ ∞ (fun ξ => a (x₀ j, ξ)) {ξ : E | ξ ≠ 0} := by
    have smooth : ContDiff ℝ ∞ (fun ξ : E => (x₀ j, ξ)) := contDiff_const.prodMk contDiff_id
    exact ha.comp smooth.contDiffOn (fun _ hξ => ⟨hKWU (hKpW (hCenter j)), hξ⟩)
  exact (each j).2 (fun ξ => a (x₀ j, ξ)) hFiber (hom _ (hCenter j)) (jets _ (hCenter j)) ε hε

end Burnett.C02
