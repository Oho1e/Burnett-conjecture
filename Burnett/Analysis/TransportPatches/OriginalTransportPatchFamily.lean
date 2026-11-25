import Burnett.Analysis.TransportPatches.OriginalProjectedPatchSource
import Burnett.Analysis.TransportPatches.OriginalWideC03Consumer

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000

noncomputable section

namespace Burnett.C02

open Set Metric Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol Burnett.Geometry
open Burnett.A02.FrequencySplit (E)
open ConnectionDifference CurvatureDifference InverseField ManifoldMetric ManifoldBilinear
open ManifoldMetricSequence MaximalChart Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 Burnett.C03
open Burnett.C01 (patchCenter)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold ENNReal Topology BigOperators

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

def wideErrorGradientL3Norm (T : ClassicalMatrixMultiplier OrderedPair) (z : ProjectionSchwartzMatrix) : ℝ :=
  (eLpNorm (orderedGradientValue (fun a : Index × OrderedPair =>
    multiplierCoordinateDerivative T z a.1 a.2)) 3 volume).toReal

/-- One choice of a finite cubic family and its actual two-layer supports gives an
eventual whole-space physical source and both full wide errors along the given σ. -/
theorem exists_originalTransportPatchFamily
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hsg : ∀ n, IsSymmetric (g n)) (hnd : ∀ n, IsNondegenerate (g n))
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (hconv : LocallyUniformlyConverges r g B)
    (hDh : AuxiliaryAdmissibility.CompactDhBound r B g)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (c : AtlasChart M) (K Kplus V : Set E)
    (hK : IsCompact K) (hKp : IsCompact Kplus) (hnested : K ⊆ interior Kplus)
    (hVK : Kplus ⊆ V) (hV : IsCompact V) (hVcv : Convex ℝ V) (hVU : V ⊆ c.chart.target)
    (p : ℝ) (hp : 3 < p) (e : ℕ → ℝ) (en : ∀ n, 0 ≤ e n) (he : Tendsto e atTop (𝓝 0))
    (herr : ∀ n x, x ∈ Kplus →
      ‖metricComponents (fixedForm (g n) c) x - metricComponents (fixedForm B c) x‖ ≤ e n) :
    ∃ (ℓ₁ Msrc C i o Ccoeff : ℝ) (Ccut : ℕ → ℝ) (Cp : {q : ℝ // 1 < q} → ℝ),
      0 < ℓ₁ ∧ 0 < i ∧ i < o ∧ 0 ≤ Msrc ∧ 0 ≤ C ∧ 0 ≤ Ccoeff ∧
      (∀ k, 0 ≤ Ccut k) ∧ (∀ q, 0 ≤ Cp q) ∧
      ∀ (ℓ : ℝ), 0 < ℓ → ℓ < ℓ₁ →
      ∃ (s : Finset LatticeIndex) (χ χplus : LatticeIndex → E → ℝ),
        (∀ x ∈ thickening ℓ K, ∑ j ∈ s, χ j x ^ 3 = 1) ∧
        (∀ x ∈ thickening ℓ K, ∀ v : E, ∑ j ∈ s, χ j x ^ 2 * fderiv ℝ (χ j) x v = 0) ∧
        (∑ j ∈ s, (volume : Measure E) (closedBall (patchCenter ℓ j) (6 * ℓ))) ≤
          ((17 ^ 4 : ℕ) : ℝ≥0∞) * volume Kplus ∧
        ∀ j ∈ s, let x₀ := patchCenter ℓ j
        let P := closedBall x₀ (6 * ℓ)
        let m := chartInverseMetric B c x₀
        ∃ (dχ : D) (hχU : tsupport (dχ : E → ℝ) ⊆ c.chart.target)
          (hm : WideScreenFrequencySmooth i o m),
          (dχ : E → ℝ) = χ j ∧ ContDiff ℝ ∞ (χplus j) ∧
          (∀ x, 0 ≤ χ j x ∧ χplus j x ∈ Icc (0 : ℝ) 1) ∧
          tsupport (χ j) ⊆ closedBall x₀ (4 * ℓ) ∧
          tsupport (χplus j) ⊆ P ∧ P ⊆ interior Kplus ∧
          (∀ x ∈ thickening ℓ (tsupport (χ j)), χplus j x = 1) ∧
          (∀ k x, ‖iteratedFDeriv ℝ k (χ j) x‖ ≤ Ccut k * ℓ⁻¹ ^ k ∧
            ‖iteratedFDeriv ℝ k (χplus j) x‖ ≤ Ccut k * ℓ⁻¹ ^ k) ∧
          let z := receivingCutoffFluctuation B g hB hg c dχ hχU
          (∀ᶠ n in atTop, ∃ (a : ProjectedSourceCoefficients) (d : Index → Index → SchwartzMap E ℝ),
            (∀ k l x, a.entry k l x = ((m k l + d k l x : ℝ) : ℂ)) ∧
            (∀ k l x, d k l x = correctionCoefficientPart (χplus j)
              (matrixInverse ∘ metricComponents (fixedForm (g (σ n)) c)) m x k l) ∧
            (∀ k l, d k l = d l k) ∧
            (∀ k l x, |d k l x| ≤ Ccoeff * (ℓ + e (σ n))) ∧
            (∀ k l x, ‖fderiv ℝ (d k l : E → ℝ) x‖ ≤ 4 * Ccoeff * (1 + e (σ n) / ℓ)) ∧
            ‖projectedSourceDivergenceL2 a (projectionFullSchwartz (z (σ n)))‖ ≤
              Msrc * (volume P ^ ((1 : ℝ) / 2)).toReal * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e (σ n)) ∧
            ∀ q : {q : ℝ // 1 < q}, ProjectedPatchLpBounds q.val (z (σ n)) P
              (Cp q * e (σ n)) (Cp q * (1 + e (σ n) / ℓ))) ∧
          let T₁ := actualFrozenScreenErrorMultiplier i o m hm
          let T₂ := actualFrozenPhaseErrorMultiplier i o m hm
          (∀ n, MemLp (orderedGradientValue (fun a : Index × OrderedPair =>
              multiplierCoordinateDerivative T₁ (z (σ n)) a.1 a.2)) 3 volume ∧
            MemLp (orderedGradientValue (fun a : Index × OrderedPair =>
              multiplierCoordinateDerivative T₂ (z (σ n)) a.1 a.2)) 3 volume) ∧
          ∀ ε > 0, ∀ᶠ n in atTop,
            max (wideErrorGradientL3Norm T₁ (z (σ n))) (wideErrorGradientL3Norm T₂ (z (σ n))) ≤
              C * ℓ ^ frozenErrorExponent p * ((volume : Measure E) P).toReal ^ (1 / 3 : ℝ) + ε := by
  let G := fun n => metricComponents (fixedForm (g n) c)
  let G₀ := metricComponents (fixedForm B c)
  have hKU := hVK.trans hVU
  obtain ⟨D₀, hD₀, hJ⟩ := fixedForm_firstJet_uniform_bound_on_compact r g B hg hB
    hSig.isNondegenerate hconv hDh c hKp hKU
  obtain ⟨ℓ₀, Msrc, Ccoeff, Ccut, Cp, hℓ₀, hMsrc, hCcoeff, hCcut, hCp, patches⟩ :=
    exists_original_projectedPatchSource_family c.chart.target K Kplus c.chart.open_target hK hKp
      hnested hKU G₀ G (fixedForm_components_smooth B hB c)
      (fun n => fixedForm_components_smooth (g n) (hg n) c)
      (fun _ hx => fixedForm_det_ne_zero B hSig.isNondegenerate c hx)
      (fun n _ hx => fixedForm_det_ne_zero (g n) (hnd n) c hx)
      (fun x _ a b => hSig.isSymmetric (c.chart.symm x) _ _)
      (fun n x _ a b => hsg n (c.chart.symm x) _ _)
      (fun n x hx => fixedForm_coordinateVacuum_of_intrinsic (g n) (hg n) (hsg n) (hnd n) (hv n) c x hx)
      (fixed_components_uniform_of_physical_C0loc r g B hconv c Kplus hKp hKU)
      D₀ hD₀ hJ e en he herr
  obtain ⟨i, o, L, C, η, hf, hi, ho, hL, hC, hη, wide⟩ :=
    exists_originalWideL3_consumeC03Source r B g hB hg hSig hconv σ hσ A hA hPair
      c V hV hVcv hVU p hp e he Cp hCp
  let b := min ℓ₀ (min (1 / 6 : ℝ) (η / (6 * (L + 1))))
  have hL₁ : 0 < 6 * (L + 1) := by positivity
  have hb : 0 < b := lt_min hℓ₀ (lt_min (by norm_num) (div_pos hη hL₁))
  refine ⟨b, Msrc, C, i, o, Ccoeff, Ccut, Cp, hb, hi, ho, hMsrc, hC, hCcoeff, hCcut, hCp, ?_⟩
  intro ℓ hℓ hbℓ
  have hsmall : ℓ < ℓ₀ := hbℓ.trans_le (min_le_left _ _)
  have h₆ : ℓ < (1 / 6 : ℝ) := hbℓ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h₆' : ℓ < η / (6 * (L + 1)) := hbℓ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hband : L * (6 * ℓ) ≤ η := by nlinarith [(lt_div_iff₀ hL₁).mp h₆']
  obtain ⟨s, χ, χplus, cube, cancel, sum, cuts, eventual⟩ := patches ℓ hℓ hsmall
  refine ⟨s, χ, χplus, cube, cancel, sum, ?_⟩
  intro j hj x₀ P m
  obtain ⟨hχ, hχplus, hPos, innerSupport, outerSupport, inside, plateau, hJets⟩ := cuts j hj
  have hP : P ⊆ V := inside.trans (interior_subset.trans hVK)
  have hχP : tsupport (χ j) ⊆ P := innerSupport.trans (closedBall_subset_closedBall (by linarith))
  let dχ : D := ⟨χ j, hχ, (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hχP⟩
  have hχU : tsupport (dχ : E → ℝ) ⊆ c.chart.target := hχP.trans (hP.trans hVU)
  have hx : x₀ ∈ P := mem_closedBall_self (mul_nonneg (by norm_num) hℓ.le)
  have hm := hf x₀ (hP hx)
  let z := receivingCutoffFluctuation B g hB hg c dχ hχU
  have c02Input : ∀ᶠ n in atTop, ∃ w : ProjectionSchwartzMatrix,
      (∀ k l x, w k l x = ((χ j x * (G n x k l - G₀ x k l) : ℝ) : ℂ)) ∧
      ∀ q : {q : ℝ // 1 < q}, ProjectedPatchLpBounds q.val w P
        (Cp q * e n) (Cp q * (1 + e n / ℓ)) := by
    filter_upwards [eventual] with n hn
    obtain ⟨_, w, _, _, _, _, _, _, hw, _, hpq⟩ := hn j hj
    exact ⟨w, hw, hpq⟩
  have both := wide ℓ hℓ (by linarith) hband j hP (χ j) hχ hχP c02Input
  refine ⟨dχ, hχU, hm, rfl, hχplus, hPos, innerSupport, outerSupport, inside, plateau, hJets,
    ?_, both.1, ?_⟩
  · filter_upwards [hσ.tendsto_atTop.eventually eventual] with n hn
    obtain ⟨coeff, w, d, entry, formula, hSym, hMag, hSlope, hw, src, hpq⟩ := hn j hj
    have hid : z (σ n) = w := receivingCutoffFluctuation_eq_originalSourceInput B g hB hg c dχ hχU (σ n) w hw
    change ∃ (a : ProjectedSourceCoefficients) (d : Index → Index → SchwartzMap E ℝ), _
    refine ⟨coeff, d, entry, formula, hSym, hMag, hSlope, ?_, ?_⟩
    · change ‖projectedSourceDivergenceL2 coeff (projectionFullSchwartz (z (σ n)))‖ ≤ _
      rw [hid]
      exact src
    · intro q
      change ProjectedPatchLpBounds q.val (z (σ n)) P _ _
      rw [hid]
      exact hpq q
  · intro ε hε
    filter_upwards [both.2 ε hε] with n hn
    exact max_le hn.1 hn.2

end Burnett.C02
