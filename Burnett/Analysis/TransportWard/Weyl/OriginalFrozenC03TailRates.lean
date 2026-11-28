import Burnett.Analysis.TransportWard.Weyl.OriginalFrozenC03TailInterface
import Burnett.Analysis.TransportWard.Weyl.OriginalReceivingPatchProjectedNorms
import Burnett.Analysis.TransportWard.Weyl.OriginalCubicInfraredInput
import Burnett.Analysis.FrozenTransport.OriginalThinCubicReceivingGradientPair
import Burnett.Analysis.FrozenTransport.PatchCorrection.OriginalCorrectionSuppliedChartPatches
import Burnett.Analysis.FrozenTransport.Ward.OriginalChartNearPhaseRates
import Burnett.Analysis.FrozenTransport.Ward.OriginalFrozenPatchTail

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 22000000

noncomputable section

namespace Burnett.V03.Palatini

section RateStatement

open Filter MeasureTheory Metric Set Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference InverseField ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart
open UnitNullCompactness CotangentAngularExtension Burnett.C01 Burnett.C02 Burnett.C03 Burnett.C04
open Burnett.A02.FrequencySplit Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.P01
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ComplexConjugate ContDiff ENNReal Manifold Matrix.Norms.Elementwise Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M] [SecondCountableTopology M]

def HasOriginalFrozenC03TailAtExponent
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (σ : ℕ → ℕ) (c₀ : M) (f : CotangentBundle M → ℝ) (p : ℝ) : Prop :=
  let α := frozenErrorExponent p
  let ν := 2 * (p - 3) / (p - 2)
  let c := AtlasChart.atPoint c₀
  let a (x ξ : E) := originalChartTransportSymbol c₀ f x (WithLp.ofLp ξ)
  let β (x ξ : E) := fixedInfraredSymbol wardFixedTestCutoff 0 (a x) ξ
  ∀ K V : Set E, IsCompact K → IsCompact V → K ⊆ V → Convex ℝ V → V ⊆ c.chart.target →
    ∀ (e : ℕ → ℝ), (∀ n, 0 ≤ e n) → Tendsto e atTop (𝓝 0) →
      (∀ n x, x ∈ K → ‖metricComponents (fixedForm (g n) c) x -
        metricComponents (fixedForm B c) x‖ ≤ e n) →
      ∀ (Msrc Ccoeff : ℝ) (Ccut : ℕ → ℝ) (Cp : {p : ℝ // 1 < p} → ℝ),
        0 ≤ Msrc → 0 ≤ Ccoeff → (∀ k, 0 ≤ Ccut k) → (∀ p, 0 ≤ Cp p) →
        ∃ Cnear δ₀ : ℝ, 0 < α ∧ 0 < ν ∧ 0 < δ₀ ∧
          ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ R G ℓ₀ : ℝ, 0 < ℓ₀ ∧
            ∀ ℓ : ℝ, 0 < ℓ → ℓ < ℓ₀ → ∀ (s : Finset LatticeIndex) (d : LatticeIndex → D)
              (ψ : LatticeIndex → E → ℝ) (hd : ∀ j, tsupport (d j : E → ℝ) ⊆ c.chart.target),
              let P (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6 * ℓ)
              let z (n : ℕ) (j : LatticeIndex) := receivingCubicPatchField B g hB hg c (d j) (hd j) (σ n)
              (∀ j ∈ s, ContDiff ℝ ∞ (ψ j) ∧ (∀ x, 0 ≤ (d j : E → ℝ) x ∧ ψ j x ∈ Icc (0 : ℝ) 1) ∧
                tsupport (d j : E → ℝ) ⊆ closedBall (patchCenter ℓ j) (4 * ℓ) ∧ tsupport (ψ j) ⊆ P j ∧
                P j ⊆ interior K ∧ (∀ x ∈ thickening ℓ (tsupport (d j : E → ℝ)), ψ j x = 1) ∧
                ∀ k x, ‖iteratedFDeriv ℝ k (d j : E → ℝ) x‖ ≤ Ccut k * ℓ⁻¹ ^ k ∧
                  ‖iteratedFDeriv ℝ k (ψ j) x‖ ≤ Ccut k * ℓ⁻¹ ^ k) →
              (∀ j ∈ s, ∀ᶠ n in atTop,
                let m := chartInverseMetric B c (patchCenter ℓ j)
                let u (i k : Index) := (z n j).val (i,k)
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
                    (Cp p * e (σ n)) (Cp p * (1 + e (σ n) / ℓ))) →
              (∑ j ∈ s, (volume : Measure E) (P j)) ≤ ((17 ^ 4 : ℕ) : ℝ≥0∞) * volume K →
              let frozen (n : ℕ) (j : LatticeIndex) :=
                let x := patchCenter ℓ j
                let G₀ := metricComponents (fixedForm B c) x
                completeCubicEnergy (frozenActionCubicLinear G₀) (frozenActionCubicQuadratic G₀) (β x) (z n j)
              ∀ ε > 0, ∀ᶠ n in atTop, (∑ j ∈ s, |frozen n j|) ≤
                (Cnear * δ ^ ν + R * ℓ ^ α + G * ℓ) * ((17 ^ 4 : ℝ) * (volume K).toReal) + ε

end RateStatement

open Filter Metric MeasureTheory Set Matrix Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart
open UnitNullCompactness CotangentAngularExtension
open Burnett.A02.FrequencySplit Burnett.C02 Burnett.C03 Burnett.C04 Burnett.Fourier Burnett.V06
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.Analysis.ProjectiveNullCaps (descendingProfile descendingProfile_contDiff descendingProfile_range
  descendingProfile_eq_zero descendingProfile_eq_one)
open Burnett.Analysis.TransportWardSymbol (inverseMatrix metricDensity)
open Burnett.C01 (patchCenter)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix receivingCutoffFluctuation)
open Burnett.X02.SobolevTestJet (D test_smooth)
open scoped BigOperators ComplexConjugate ContDiff ENNReal Manifold Matrix Matrix.Norms.Elementwise Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The rate-specific frozen C03 tail for any fixed finite exponent `p > 3`
on the already supplied patches of the original chart. The wide screen, near bound and all constraints on the
thin parameters precede `δ`. The replacement, phase and correction
constants at that `δ` precede the localization scale. -/
theorem hasOriginalFrozenC03TailAtExponent_of_originalChartWard
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hSig : HasLorentzSignature B) (hg : ∀ n, IsSmooth (g n))
    (hgSym : ∀ n, IsSymmetric (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (c₀ : M) (f : CotangentBundle M → ℝ) (hfTest : IsDegreeOneTransportTest f) (hfOdd : IsAntipodallyOdd f)
    (S : Set M) (hS : IsCompact S) (hSChart : S ⊆ (chartAt E c₀).source)
    (hSOff : ∀ p ∈ puncturedCotangent, p.proj ∉ S → f p = 0)
    (p : ℝ) (hp : 3 < p) :
    HasOriginalFrozenC03TailAtExponent B g hB hg σ c₀ f p := by
  classical
  unfold HasOriginalFrozenC03TailAtExponent
  intro α ν c a₀ β K V hK hV hKV hConvex hVU e he hE hError Msrc Ccoeff Ccut Cp hMsrc hCcoeff hCcut hCp
  let a (p : Joint) := a₀ p.1 p.2
  let G := metricComponents (fixedForm B c)
  let m := chartInverseMetric B c
  have hKU : K ⊆ c.chart.target := hKV.trans hVU
  obtain ⟨_, _, _, hSmooth, hHom₀, hOdd₀⟩ := originalChartTransportSymbol_properties c₀ f hfTest hfOdd hS hSChart hSOff
  let T := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)
  let lift (p : Joint) := (p.1, T p.2)
  have hLift : ContDiff ℝ ∞ lift := contDiff_fst.prodMk (T.contDiff.comp contDiff_snd)
  have ha : ContDiffOn ℝ ∞ a (c.chart.target ×ˢ {ξ : E | ξ ≠ 0}) := by
    apply hSmooth.comp hLift.contDiffOn
    intro p hp
    exact ⟨mem_univ p.1, fun h => hp.2 (T.injective (h.trans (map_zero T).symm))⟩
  have hOdd (x ξ : E) : a₀ x (-ξ) = -a₀ x ξ := by
    change originalChartTransportSymbol c₀ f x (T (-ξ)) = -originalChartTransportSymbol c₀ f x (T ξ)
    rw [map_neg]
    exact hOdd₀ x (T ξ)
  have hHom (x : E) (t : ℝ) (ht : 0 < t) (ξ : E) : a₀ x (t • ξ) = t * a₀ x ξ := by
    by_cases hξ : ξ = 0
    · subst ξ
      have hzero := hOdd x 0
      rw [neg_zero] at hzero
      have hzero' : a₀ x 0 = 0 := by linarith
      simp only [smul_zero, hzero', mul_zero]
    · change originalChartTransportSymbol c₀ f x (T (t • ξ)) = t * originalChartTransportSymbol c₀ f x (T ξ)
      rw [map_smul]
      exact hHom₀ x t ht (T ξ) (fun h => hξ (T.injective (h.trans (map_zero T).symm)))
  have hFiber (x : E) (hx : x ∈ K) : ContDiffOn ℝ ∞ (a₀ x) {ξ : E | ξ ≠ 0} := by
    have hs : ContDiff ℝ ∞ (fun ξ : E => (x, ξ)) := contDiff_const.prodMk contDiff_id
    exact ha.comp hs.contDiffOn (fun _ hξ => ⟨hKU hx, hξ⟩)
  obtain ⟨Djet, hDjet, hJets⟩ := Burnett.V11.exists_uniform_originalFrequencyTest_jets
    c.chart.target K c.chart.open_target hK hKU a ha 16
  obtain ⟨CpWhole, hCpWhole, rawLp⟩ := Burnett.V03.exists_originalReceivingPatch_projectedLp_wholeSequence
    r B g hB hg hSig.isNondegenerate hconv hb c K hK hKU e he hError Ccut hCcut
  obtain ⟨Mraw, _, rawEuclidean⟩ := exists_receivingCubicPatch_volume_budget
    r B g hB hg hSig.isNondegenerate hconv hb c K hK hKU σ hσ e he hE hError (Ccut 0) (Ccut 1) (hCcut 0) (hCcut 1)
  let p₃ : {p : ℝ // 1 < p} := ⟨3, by norm_num⟩
  let C₃ := CpWhole p₃
  have hα : 0 < α := (frozenErrorExponent_bounds hp).1
  have hν : 0 < ν := div_pos (mul_pos (by norm_num) (sub_pos.mpr hp)) (by linarith)
  let ϑ := descendingProfile (1 / 4) 1
  have hϑ : ContDiff ℝ ∞ ϑ := descendingProfile_contDiff _ _
  have hCut (t : ℝ) (ht : 1 ≤ t) : ϑ t = 0 := descendingProfile_eq_zero (by norm_num) ht
  have hFlat (t : ℝ) (_ : 0 ≤ t) (ht : t ≤ 1 / 4) : ϑ t = 1 := descendingProfile_eq_one (by norm_num) ht
  have hBounded (t : ℝ) : |ϑ t| ≤ 1 := by
    change |descendingProfile (1 / 4) 1 t| ≤ 1
    rw [abs_of_nonneg (descendingProfile_range (1 / 4) 1 t).1]
    exact (descendingProfile_range (1 / 4) 1 t).2
  have hRange (t : ℝ) (_ : 0 ≤ t) : ‖ϑ t‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using hBounded t
  let κ : ℝ := 1 / 32
  have hκ : 0 < κ := by norm_num [κ]
  have hκsmall : κ < 1 / 16 := by norm_num [κ]
  let inn : ℝ := 1
  let out : ℝ := 2
  have hin : 0 < inn := by norm_num [inn]
  have hio : inn < out := by norm_num [inn, out]
  have hout : 0 < out := hin.trans hio
  obtain ⟨wi, wo, Lw, ηw, Vopen, wide₀, hVopen, hVop, hVchart, hJoint, _, _, hLw, hηw, thinBudget⟩ :=
    exists_originalThinCubicReceivingFamily_withFixedJointScreen_andGradientPair r B g hB hg hSig hconv
      σ hσ A hA hPair c K V hK hV hConvex hKV hVU p hp e hE CpWhole hCpWhole
      wardFixedTestCutoff 0 wardFixedTestCutoff_real (fun _ => by simp) a ha (fun x _ => hHom x)
  have hKVopen := hKV.trans hVop
  have haOpen := ha.mono (Set.prod_mono hVchart Subset.rfl)
  let wide (x : E) (hx : x ∈ K) : WideScreenFrequencySmooth wi wo (m x) :=
    wideScreen_frequencySmooth_of_joint hJoint (hKVopen hx)
  obtain ⟨cN, δN, Cphase, hcN, hδN, hδN₁, _, nearPhase⟩ := Burnett.V03.exists_originalChartWardNearPhaseRates
    B hB hSig c K Vopen hK hVopen hKVopen hVchart wi wo hJoint a haOpen
    (fun x _ => hOdd x) (fun x _ => hHom x) ϑ hϑ hRange hCut hFlat κ inn out p C₃
    hκ hκsmall hin.le hio hp (hCpWhole p₃)
  obtain ⟨cF, εwin, hcF, hεwin, hWindow, correction⟩ :=
    Burnett.V11.exists_originalCorrectionPatchFourierTail_of_suppliedChartPatches B g hB hSig hg
      c Vopen K hVopen hK hKVopen hVchart σ hσ e he hE Msrc Ccoeff hMsrc hCcoeff Cp hCp
      wi wo hJoint a haOpen (fun x _ => hOdd x) (fun x _ => hHom x) ϑ hϑ hCut hFlat hBounded κ hκ hκsmall out hout.le
  obtain ⟨_, hFrame⟩ := Burnett.V11.compact_chartInverseMetric_family B hB hSig c K hK hKU
  let cThin := min cN cF
  have hcThin : 0 < cThin := lt_min hcN hcF
  obtain ⟨Cnear, hCnear, rates⟩ := nearPhase cThin hcThin (min_le_left _ _)
  have hδDen : 0 < 1 + cThin * κ * out := by positivity
  let δ₀ := min δN (εwin / (1 + cThin * κ * out))
  have hδ₀ : 0 < δ₀ := lt_min hδN (div_pos hεwin hδDen)
  refine ⟨Cnear, δ₀, hα, hν, hδ₀, ?_⟩
  intro δ hδ hδSmall
  have hδNear : δ ∈ Ioc (0 : ℝ) δN := ⟨hδ, hδSmall.le.trans (min_le_left _ _)⟩
  have hδ₁ : δ ≤ 1 := hδNear.2.trans hδN₁
  let η := cThin * κ * δ^2
  have hη : 0 < η := mul_pos (mul_pos hcThin hκ) (pow_pos hδ _)
  have hThinWindow : out * η ≤ εwin := by
    have hsq : δ^2 ≤ δ := by nlinarith only [mul_nonneg hδ.le (sub_nonneg.mpr hδ₁)]
    have hδWin := (le_div_iff₀ hδDen).mp (hδSmall.le.trans (min_le_right _ _))
    calc
      out * η = cThin * κ * out * δ^2 := by dsimp only [η]; ring
      _ ≤ cThin * κ * out * δ := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ δ * (1 + cThin * κ * out) := by nlinarith only [hδ.le]
      _ ≤ εwin := hδWin
  obtain ⟨Ce, Ccubic, Lt, hCe, hCcubic, hLt, thin⟩ := thinBudget κ δ cThin inn out hκ hδ hcThin hin hio
  obtain ⟨CFG, _, farGauge⟩ := correction δ hδ hδ₁ cThin hcThin (min_le_right _ _) inn out hin.le hio le_rfl
  let Pphase := Cphase * Ce * (128 * (2 * C₃) + Ce)^2
  let ℓ₀ := min (1 / 6 : ℝ) (min (ηw / (6 * (1 + Lw))) (inn * η / (6 * (1 + Lt))))
  have hℓ₀ : 0 < ℓ₀ := lt_min (by norm_num) (lt_min (div_pos hηw (by positivity)) (div_pos (mul_pos hin hη) (by positivity)))
  refine ⟨Ccubic + Pphase, 3 * CFG, ℓ₀, hℓ₀, ?_⟩
  intro ℓ hℓ hℓSmall s d ψ hd P raw hCuts hSource hVol frozen ε hε
  have hSix : 6 * ℓ ≤ 1 := by
    have h := hℓSmall.le.trans (min_le_left (1 / 6 : ℝ) _)
    linarith
  have hℓ₁ : ℓ ≤ 1 := by linarith
  have hLwℓ : Lw * (6 * ℓ) ≤ ηw := by
    have hSmall : ℓ ≤ ηw / (6 * (1 + Lw)) := hℓSmall.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    calc
      _ ≤ ℓ * (6 * (1 + Lw)) := by nlinarith only [hℓ.le]
      _ ≤ _ := (le_div_iff₀ (by positivity)).mp hSmall
  have hLtℓ : Lt * (6 * ℓ) ≤ inn * η := by
    have hSmall : ℓ ≤ inn * η / (6 * (1 + Lt)) := hℓSmall.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    calc
      _ ≤ ℓ * (6 * (1 + Lt)) := by nlinarith only [hℓ.le]
      _ ≤ _ := (le_div_iff₀ (by positivity)).mp hSmall
  let x (j : s) := patchCenter ℓ j
  let Z (j : LatticeIndex) (n : ℕ) := receivingCutoffFluctuation B g hB hg c (d j) (hd j) n
  have hPatch (j : LatticeIndex) (hj : j ∈ s) : P j ⊆ K := (hCuts j hj).2.2.2.2.1.trans interior_subset
  have hc (j : s) : x j ∈ K := hPatch j j.property (mem_closedBall_self (by positivity))
  have hOriginal (j : LatticeIndex) (hj : j ∈ s) := rawLp ℓ hℓ (patchCenter ℓ j) (d j) (hd j)
    (hCuts j hj).2.2.1 (hPatch j hj) (fun k y => ((hCuts j hj).2.2.2.2.2.2 k y).1)
  let χ (j : LatticeIndex) := (d j : E → ℝ)
  have hC02Cut (j : LatticeIndex) (hj : j ∈ s) : ContDiff ℝ ∞ (χ j) ∧ tsupport (χ j) ⊆ P j ∧ P j ⊆ K :=
    ⟨test_smooth (d j), (hCuts j hj).2.2.1.trans (closedBall_subset_closedBall (by linarith)), hPatch j hj⟩
  have hC02Raw (j : LatticeIndex) (hj : j ∈ s) : ∀ᶠ n in atTop, ∃ z : ProjectionSchwartzMatrix,
      (∀ i k y, z i k y = ((χ j y * (metricComponents (fixedForm (g n) c) y i k - G y i k) : ℝ) : ℂ)) ∧
      ∀ q : {q : ℝ // 1 < q}, ProjectedPatchLpBounds q.val z (P j)
        (CpWhole q * e n) (CpWhole q * (1 + e n / ℓ)) :=
    Eventually.of_forall (fun n => ⟨Z j n, fun _ _ _ => rfl, hOriginal j hj n⟩)
  have hThin := (thin ℓ hℓ hSix hLwℓ hLtℓ s χ hC02Cut hC02Raw).2
  have hRaw₃ (j : LatticeIndex) (hj : j ∈ s) : ∀ᶠ n in atTop,
      ProjectedPatchLpBounds 3 (Z j n) (P j) (C₃ * e n) (C₃ * (1 + e n / ℓ)) :=
    Eventually.of_forall (fun n => hOriginal j hj n p₃)
  obtain ⟨hNear, hSeven, phase⟩ := rates δ hδNear s ℓ hℓ hℓ₁ hPatch Z e hE σ hσ hRaw₃
  have hPhase := phase Ce α hCe hα.le (fun j t ht => (hThin t ht).mono (fun _ hn => (hn j).2))
  let W := (17 ^ 4 : ℝ) * (volume K).toReal
  have hMass : (∑ j ∈ s, (volume (P j)).toReal) ≤ W := by
    have hRight : (((17 ^ 4 : ℕ) : ℝ≥0∞) * (volume : Measure E) K) ≠ ⊤ :=
      (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hK.measure_lt_top).ne
    have h := ENNReal.toReal_mono hRight hVol
    rw [ENNReal.toReal_sum (fun _ _ => (isCompact_closedBall _ _).measure_lt_top.ne), ENNReal.toReal_mul] at h
    simpa only [W, ENNReal.toReal_natCast, Nat.cast_pow, Nat.cast_ofNat] using h
  have hCorrection := farGauge ℓ hℓ s d ψ hd hPatch W hMass hSource
  have hUnit (j : s) := (Matrix.isUnit_iff_isUnit_det (G (x j))).mpr
    (isUnit_iff_ne_zero.mpr (fixedForm_det_ne_zero B hSig.isNondegenerate c (hKU (hc j))))
  have hSym (j : s) : IsSymmetricTensor (G (x j)) := fun _ _ => hSig.isSymmetric (c.chart.symm (x j)) _ _
  let frame (j : s) : TensorFrame.LorentzFrame (m (x j)) := Classical.choice (hFrame _ ⟨x j, hc j, rfl⟩)
  have hz (j : s) (n : ℕ) (i k : Index) (y : E) : conj (Z j (σ n) i k y) = Z j (σ n) i k y := Complex.conj_ofReal _
  have hzSym (j : s) (n : ℕ) (i k : Index) : Z j (σ n) i k = Z j (σ n) k i := by
    ext y
    change Complex.ofReal ((d j : E → ℝ) y * (metricComponents (fixedForm (g (σ n)) c) y i k - G y i k)) =
      Complex.ofReal ((d j : E → ℝ) y * (metricComponents (fixedForm (g (σ n)) c) y k i - G y k i))
    have h1 : metricComponents (fixedForm (g (σ n)) c) y i k = metricComponents (fixedForm (g (σ n)) c) y k i :=
      hgSym (σ n) (c.chart.symm y) _ _
    have h2 : G y i k = G y k i := hSig.isSymmetric (c.chart.symm y) _ _
    rw [h1, h2]
  let E₀ (j : s) := completeCubicEnergy (frozenActionCubicLinear (G (x j))) (frozenActionCubicQuadratic (G (x j))) (β (x j))
  let thinField (j : s) (n : ℕ) := originalCubicThinScreen (m (x j)) wi wo (wide (x j) (hc j)) hη inn out
    (Z j (σ n)) (hz j n) + originalCubicGauge (Z j (σ n)) (hz j n)
  have hReplace (j : s) (t : ℝ) (ht : 0 < t) : ∀ᶠ n in atTop,
      |frozen n j - E₀ j (thinField j n)| ≤ Ccubic * ℓ^α * (volume (P j)).toReal + t := by
    have hχ₀ (y : E) (_ : y ∈ tsupport (d j : E → ℝ)) : ‖(d j : E → ℝ) y‖ ≤ Ccut 0 := by
      simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using ((hCuts j j.property).2.2.2.2.2.2 0 y).1
    have hχ₁ (y : E) (_ : y ∈ tsupport (d j : E → ℝ)) : ‖iteratedFDeriv ℝ 1 (d j : E → ℝ) y‖ ≤ Ccut 1 * ℓ⁻¹ := by
      simpa only [pow_one] using ((hCuts j j.property).2.2.2.2.2.2 1 y).1
    have rawNorm := rawEuclidean ℓ hℓ (x j) (d j) (hd j) (hCuts j j.property).2.2.1 (hPatch j j.property) hχ₀ hχ₁
    have hIR := Burnett.V03.tendsto_originalRawCubic_sub_physicalGauge_zero (fun n => Z j (σ n)) (hz j)
      rawNorm.2.1 _ rawNorm.2.2 (frozenActionCubicLinear (G (x j))) (frozenActionCubicLinear_symmetry (G (x j)))
      (frozenActionCubicQuadratic (G (x j))) wardFixedTestCutoff wardFixedTestCutoff_real (a₀ (x j))
      (hFiber (x j) (hc j)) (hHom (x j)) Djet hDjet (hJets (x j) (hc j))
    filter_upwards [(tendsto_order.1 hIR).2 (t / 2) (half_pos ht), hThin (t / 2) (half_pos ht)] with n hnIR hnThin
    let H := E₀ j (originalCubicPhysical (Z j (σ n)) (hz j n) + originalCubicGauge (Z j (σ n)) (hz j n))
    change |frozen n j - H| < t / 2 at hnIR
    have hn : |H - E₀ j (thinField j n)| ≤ Ccubic * ℓ^α * (volume (P j)).toReal + t / 2 := (hnThin j).1
    have hAdd := abs_add_le (frozen n j - H) (H - E₀ j (thinField j n))
    rw [show frozen n j - H + (H - E₀ j (thinField j n)) = frozen n j - E₀ j (thinField j n) by ring] at hAdd
    linarith only [hnIR, hn, hAdd]
  have hMassS := hMass
  rw [← Finset.sum_coe_sort] at hMassS
  have h := Burnett.V03.eventually_originalFrozenWardPatchSum_bound s σ ℓ W hℓ G a Z ϑ κ δ cThin wi wo inn out
    εwin hκ hδ hcThin hin.le hio hThinWindow Djet hDjet Cnear ν Ccubic Pphase α CFG hCnear hCcubic
    hMassS hUnit hSym frame (fun j => hFiber (x j) (hc j)) (fun j => hOdd (x j))
    (fun j => hHom (x j)) (fun j => hJets (x j) (hc j)) (fun j => wide (x j) (hc j)) (fun j => hWindow (x j) (hc j))
    hzSym hz hNear hReplace hSeven hPhase hCorrection ε hε
  filter_upwards [h] with n hn
  rw [← Finset.sum_coe_sort]
  exact hn

end Burnett.V03.Palatini
