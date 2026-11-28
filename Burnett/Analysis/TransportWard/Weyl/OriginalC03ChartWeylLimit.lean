import Burnett.Analysis.TransportWard.Weyl.OriginalChartCubicGeometry
import Burnett.Analysis.TransportWard.Weyl.OriginalWeylRetestedPatchLimit
import Burnett.Analysis.TransportWard.Weyl.OriginalChartOrderedPrincipalLimit
import Burnett.Analysis.TransportPatches.OriginalTransportPatchFamily

set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 6000

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter MeasureTheory Metric Set Burnett.Geometry Burnett.RicciSymbol Burnett.Fourier
open ConnectionDifference InverseField ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart
open UnitNullCompactness CotangentAngularExtension Burnett.C03 Burnett.C04 Burnett.C02
open Burnett.A03 Burnett.A02.FrequencySplit Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.C01 (patchCenter realTestComplexSchwartz)
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ComplexConjugate ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The exact C03 family for the original Weyl window converges, with the
same chart and subsequence, to the tested physical transport integral.
The same family retains the scale and support data for C02 and V11. -/
theorem exists_originalChartWeylC03_retested_cubic_limit
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hSig : HasLorentzSignature B) (hg : ∀ n, IsSmooth (g n))
    (hSigG : ∀ n, HasLorentzSignature (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (μ : Measure (Cosphere r)) (hμ : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ)
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball))
    (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (f : CotangentBundle M → ℝ) (hfTest : IsDegreeOneTransportTest f) (hfOdd : IsAntipodallyOdd f)
    (hfLocal : HasCompactTransportBaseSupportIn f (q.cutoffLocusAbove (1 / 2))) :
    let c := AtlasChart.atPoint q.center
    let a (x ξ : E) := originalChartTransportSymbol q.center f x (WithLp.ofLp ξ)
    let β (x ξ : E) := (fixedInfraredSymbol wardFixedTestCutoff 0 (a x) ξ : ℂ)
    let b (x : E) (i : OrderedPair) := assembleMetricComponents orthonormalMetricDirection
      (normalizedChartMetric B q.center x) i.1 i.2
    ∃ (χ : D) (θ : SchwartzMap E ℝ) (R : ℝ) (Kplus L : Set E)
      (_hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
      (hAmp : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R),
      IsCompact L ∧ (∀ x ∈ L, θ x = 1) ∧ (∀ x ∉ L, ∀ ξ, a x ξ = 0) ∧
      HasCompactSupport (θ : E → ℝ) ∧ ContDiff ℝ ∞ (uncurry β) ∧ IsCompact Kplus ∧
      tsupport (θ : E → ℝ) ⊆ interior Kplus ∧ Kplus ⊆ q.ball.closedBall ∧
      IsCompact q.ball.closedBall ∧ Convex ℝ q.ball.closedBall ∧ (∀ x ∈ Kplus, (χ : E → ℝ) x = 1) ∧
      ∃ (e : ℕ → ℝ) (ℓ₀ Msrc Ccoeff : ℝ) (Ccut : ℕ → ℝ) (Cp : {p : ℝ // 1 < p} → ℝ),
        (∀ n, 0 ≤ e n) ∧ Tendsto e atTop (𝓝 0) ∧
        (∀ n x, x ∈ Kplus → ‖metricComponents (fixedForm (g n) c) x -
          metricComponents (fixedForm B c) x‖ ≤ e n) ∧
        0 < ℓ₀ ∧ 0 ≤ Msrc ∧ 0 ≤ Ccoeff ∧ (∀ k, 0 ≤ Ccut k) ∧ (∀ p, 0 ≤ Cp p) ∧
        ∀ ℓ : ℝ, 0 < ℓ → ℓ < ℓ₀ →
          ∃ (s : Finset LatticeIndex) (d : LatticeIndex → D) (ψ : LatticeIndex → E → ℝ)
            (hd : ∀ j, tsupport (d j : E → ℝ) ⊆ c.chart.target),
            let P (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6 * ℓ)
            let z (n : ℕ) (j : LatticeIndex) (i : OrderedPair) :=
              receivingCutoffFluctuation B g hB hg c (d j) (hd j) (σ n) i.1 i.2
            let C (p q : Index) (i j k : OrderedPair) (x : E) := Complex.ofReal
              (localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis b (χ : E → ℝ) p q i j k x)
            let T (w : SchwartzMap E ℂ) (x : E) :=
              (-Complex.I) * firstOrderAction (windowedWeylLeftSymbol θ β R hAmp) w x
            (∀ x ∈ thickening ℓ (tsupport (θ : E → ℝ)), ∑ j ∈ s, (d j : E → ℝ) x ^ 3 = 1) ∧
            (∑ j ∈ s, (volume : Measure E) (P j)) ≤ ((17 ^ 4 : ℕ) : ℝ≥0∞) * volume Kplus ∧
            (∀ j ∈ s, ContDiff ℝ ∞ (ψ j) ∧ (∀ x, 0 ≤ (d j : E → ℝ) x ∧ ψ j x ∈ Icc (0 : ℝ) 1) ∧
              tsupport (d j : E → ℝ) ⊆ closedBall (patchCenter ℓ j) (4 * ℓ) ∧ tsupport (ψ j) ⊆ P j ∧
              P j ⊆ interior Kplus ∧ (∀ x ∈ thickening ℓ (tsupport (d j : E → ℝ)), ψ j x = 1) ∧
              ∀ k x, ‖iteratedFDeriv ℝ k (d j : E → ℝ) x‖ ≤ Ccut k * ℓ⁻¹ ^ k ∧
                ‖iteratedFDeriv ℝ k (ψ j) x‖ ≤ Ccut k * ℓ⁻¹ ^ k) ∧
            (∀ j ∈ s, ∀ᶠ n in atTop,
              let m := chartInverseMetric B c (patchCenter ℓ j)
              let u (i k : Index) := z n j (i,k)
              ∃ (a : ProjectedSourceCoefficients) (v : Index → Index → SchwartzMap E ℝ),
                (∀ i k x, a.entry i k x = ((m i k + v i k x : ℝ) : ℂ)) ∧
                (∀ i k x, v i k x = correctionCoefficientPart (ψ j)
                  (matrixInverse ∘ metricComponents (fixedForm (g (σ n)) c)) m x i k) ∧
                (∀ i k, v i k = v k i) ∧
                (∀ i k x, |v i k x| ≤ Ccoeff * (ℓ + e (σ n))) ∧
                (∀ i k x, ‖fderiv ℝ (v i k : E → ℝ) x‖ ≤ 4 * Ccoeff * (1 + e (σ n) / ℓ)) ∧
                ‖projectedSourceDivergenceL2 a (projectionFullSchwartz u)‖ ≤
                  Msrc * (volume (P j) ^ ((1 : ℝ) / 2)).toReal *
                    (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e (σ n)) ∧
                ∀ p : {p : ℝ // 1 < p}, ProjectedPatchLpBounds p.val u (P j)
                  (Cp p * e (σ n)) (Cp p * (1 + e (σ n) / ℓ))) ∧
            Tendsto (fun n => ∑ j ∈ s, ∫ x, (principalVariationDensity C (z n j)
              (fun i => T (z n j i)) x).re) atTop
              (𝓝 (4 * ∫ p in {p : Cosphere r | p.val.proj ∈ (chartAt E q.center).source},
                chartHamiltonDerivative q.center B hSig.isNondegenerate f p.val ∂μ)) := by
  classical
  intro c a β b
  obtain ⟨χ, θ, R, Kplus, L, hχ, hAmp, hL, hθL, haOff, hθc, hβ, _, hKplus, hθIn,
    hKplusV, hV, hConvex, hχKplus, Z, W, hZ, hW, hWS, hLimit⟩ :=
    exists_originalChartWeylOrderedPrincipalLimit r B g hB hSig hg hSigG hconv hb hv σ hσ A hA μ hμ
      q ν hf hRep f hfTest hfOdd hfLocal
  have hKU : Kplus ⊆ c.chart.target := hKplusV.trans q.ball_in_chart
  obtain ⟨e, he, heT, heBound⟩ :=
    exists_originalChart_component_error_modulus r B g hB hg hconv c Kplus hKplus hKU
  obtain ⟨ℓ₀, Msrc, _, _, _, Ccoeff, Ccut, Cp, hℓ₀, _, _, hMsrc, _, hCcoeff, hCcut, hCp, hFamily⟩ :=
    exists_originalTransportPatchFamily r B g hB hg hSig
      (fun n => (hSigG n).isSymmetric) (fun n => (hSigG n).isNondegenerate)
      hv hconv hb σ hσ A hA hPair c _ Kplus q.ball.closedBall hθc hKplus hθIn hKplusV
      hV hConvex q.ball_in_chart 4 (by norm_num) e he heT heBound
  obtain ⟨S, hS, hSTest, hSOff⟩ := hfLocal
  have hSChart : S ⊆ (chartAt E q.center).source := fun x hx => (hSTest hx).1
  obtain ⟨_, _, hHom, _, _, _, _, _, _, _⟩ :=
    originalChartCubic_fixedInfrared_data q.center f hfTest hfOdd hS hSChart hSOff
  obtain ⟨_, _, _, C, A₀, hA₀, hC, hCoe⟩ :=
    originalChartCubic_metric_and_coefficient B hB hSig q.center χ hχ Kplus hχKplus
  refine ⟨χ, θ, R, Kplus, L, hχ, hAmp, hL, hθL, haOff, hθc, hβ, hKplus, hθIn, hKplusV,
    hV, hConvex, hχKplus, e, ℓ₀, Msrc, Ccoeff, Ccut, Cp, he, heT, heBound, hℓ₀, hMsrc,
    hCcoeff, hCcut, hCp, ?_⟩
  intro ℓ hℓ hℓsmall
  obtain ⟨s, φ, ψ, hCube, _, hVolume, hCuts⟩ := hFamily ℓ hℓ hℓsmall
  let zeroTest : D := ⟨0, contDiff_const, by
    change IsCompact (closure (Function.support (0 : E → ℝ)))
    rw [Function.support_zero, closure_empty]
    exact isCompact_empty⟩
  let d (j : LatticeIndex) : D := if hj : j ∈ s then (hCuts j hj).choose else zeroTest
  have hd : ∀ j, tsupport (d j : E → ℝ) ⊆ c.chart.target := by
    intro j
    by_cases hj : j ∈ s
    · simpa only [d, dif_pos hj] using (hCuts j hj).choose_spec.choose
    · simp [d, hj, zeroTest, tsupport]
  have hInput (j : LatticeIndex) (hj : j ∈ s) := (hCuts j hj).choose_spec.choose_spec.choose_spec
  have hdφ (j : LatticeIndex) (hj : j ∈ s) : (d j : E → ℝ) = φ j := by
    simpa only [d, dif_pos hj] using (hInput j hj).1
  have hCube' (x : E) (hx : x ∈ thickening ℓ (tsupport (θ : E → ℝ))) :
      ∑ j ∈ s, (d j : E → ℝ) x ^ 3 = 1 := by
    rw [Finset.sum_congr rfl (fun j hj => by rw [hdφ j hj])]
    exact hCube x hx
  refine ⟨s, d, ψ, hd, hCube', hVolume, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨_, hSmooth, hPos, hInner, hOuter, hIn, hPl, hD, _, _, _⟩ := hInput j hj
    simpa only [hdφ j hj] using And.intro hSmooth
      (And.intro hPos (And.intro hInner (And.intro hOuter (And.intro hIn (And.intro hPl hD)))))
  · intro j hj
    simpa only [d, dif_pos hj] using (hInput j hj).2.2.2.2.2.2.2.2.1
  · let u (n : ℕ) (j : LatticeIndex) (i : OrderedPair) :=
      receivingCutoffFluctuation B g hB hg c (d j) (hd j) (σ n) i.1 i.2
    let C' (p q : Index) (i j k : OrderedPair) (x : E) := Complex.ofReal
      (localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis b (χ : E → ℝ) p q i j k x)
    have hOne (j : LatticeIndex) (hj : j ∈ s) (x : E) (hx : x ∈ tsupport (d j : E → ℝ)) :
        (χ : E → ℝ) x = 1 := by
      obtain ⟨_, _, _, hInner, _, hIn, _, _, _, _, _⟩ := hInput j hj
      rw [hdφ j hj] at hx
      exact hχKplus x (interior_subset (hIn ((hInner.trans (closedBall_subset_closedBall (by linarith))) hx)))
    have hχθ : ∀ x ∈ tsupport (θ : E → ℝ), (χ : E → ℝ) x = 1 :=
      fun x hx => hχKplus x (interior_subset (hθIn hx))
    have hError := tendsto_originalWeyl_retested_cubic_partition_error_zero r B g hB hg hSig.isNondegenerate
      hconv hb c χ hχ σ hσ s d (fun j _ => hd j) hOne a L hL haOff (fun t ht x ξ => hHom x t ht ξ)
      wardFixedTestCutoff wardFixedTestCutoff_real wardFixedTestCutoff_profile_one
      wardFixedTestCutoff_profile_zero hβ θ hθc hθL hχθ ℓ hℓ hCube' R hAmp C A₀ hA₀ hC
      W hWS hW
    have hReindex (n : ℕ) (j : LatticeIndex) (hj : j ∈ s) (i : OrderedPair) :
        energyProduct (realTestComplexSchwartz (d j))
          (fixedWeylPerturbationSchwartz B g hB hg c χ hχ (σ n) i) = u n j i := by
      obtain ⟨p, q⟩ := i
      rw [fixedWeylPerturbationSchwartz_eq_receivingCutoffFluctuation]
      exact receivingCutoffFluctuation_eq_patch_product_of_plateau B g hB hg c χ (d j) hχ
        (hd j) (hOne j hj) (σ n) p q
    have hC' : (fun p q i j k x => C p q i j k x) = C' := by
      funext p q i j k x
      exact hCoe p q i j k x
    have hZFun (n : ℕ) : (Z n).val = fixedWeylPerturbationSchwartz B g hB hg c χ hχ (σ n) :=
      funext (hZ n)
    have hLimit' := hError.add hLimit
    simp only [zero_add] at hLimit'
    refine hLimit'.congr fun n => ?_
    simp only [hC', hZFun]
    rw [sub_add_cancel]
    exact Finset.sum_congr rfl fun j hj => by
      let v (i : OrderedPair) := energyProduct (realTestComplexSchwartz (d j))
        (fixedWeylPerturbationSchwartz B g hB hg c χ hχ (σ n) i)
      let T (w : SchwartzMap E ℂ) (x : E) :=
        (-Complex.I) * firstOrderAction (windowedWeylLeftSymbol θ β R hAmp) w x
      have eq : v = u n j := funext (hReindex n j hj)
      change (∫ x, (principalVariationDensity C' v (fun i => T (v i)) x).re) =
        ∫ x, (principalVariationDensity C' (u n j) (fun i => T (u n j i)) x).re
      rw [eq]

end Burnett.V03.Palatini
