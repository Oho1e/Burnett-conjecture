import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualPatchFourierSum
import Burnett.Analysis.FrozenTransport.PatchCorrection.IntrinsicCommonWideCorrectionJets
import Burnett.Analysis.GaugeProjection.MaximalChartFirstJet
import Burnett.Geometry.MaximalChart.VacuumTransfer

set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxRecDepth 6800

noncomputable section

namespace Burnett.V11

open Set Filter Metric MeasureTheory Matrix
open Burnett.Geometry Burnett.P01 Burnett.C02 Burnett.C03 Burnett.V08 Burnett.RicciSymbol
open ConnectionDifference CurvatureDifference InverseField ManifoldMetric ManifoldBilinear
open ManifoldMetricSequence MaximalChart
open Burnett.V10.OriginalGaugeCompatibility
open Burnett.A02.FrequencySplit (E Joint tau)
open Burnett.Analysis.TransportWardSymbol (inverseMatrix)
open Burnett.C01 (patchCenter)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open scoped ContDiff Topology ENNReal Matrix BigOperators ComplexConjugate

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The original C03 constants are available before the joint wide screen.
The compact phase guard then precedes every thin width. The original
patches, source and whole-sequence bounds apply to the literal pair of
Fourier corrections along the given subsequence. -/
theorem exists_originalCorrectionPatchFourierTail
    (r : ManifoldMetric.Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hSig : HasLorentzSignature B) (hg : ∀ n, IsSmooth (g n))
    (hgs : ∀ n, IsSymmetric (g n)) (hgn : ∀ n, IsNondegenerate (g n))
    (hVac : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (hconv : LocallyUniformlyConverges r g B) (hDh : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (K Kplus : Set E) (hK : IsCompact K) (hKplus : IsCompact Kplus)
    (hNested : K ⊆ interior Kplus) (hKU : Kplus ⊆ c.chart.target)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    let g₀ := metricComponents (fixedForm B c)
    let G (n : ℕ) := metricComponents (fixedForm (g n) c)
    ∃ e : ℕ → ℝ, (∀ n, 0 ≤ e n) ∧ Tendsto e atTop (𝓝 0) ∧
    (∀ n x, x ∈ Kplus → ‖G n x - g₀ x‖ ≤ e n) ∧
    ∃ (ℓ₀ : ℝ) (Ccut : ℕ → ℝ) (Cp : {p : ℝ // 1 < p} → ℝ),
    0 < ℓ₀ ∧ (∀ k, 0 ≤ Ccut k) ∧ (∀ p, 0 ≤ Cp p) ∧
    ∀ D : ℝ, 0 ≤ D →
    ∃ c₀ b : ℝ, 0 < c₀ ∧ 0 < b ∧
    ∀ (V : Set E), IsOpen V → ∀ (hKV : Kplus ⊆ V), V ⊆ c.chart.target →
    ∀ (i o : ℝ) (joint : HasJointWideScreen B c i o V),
    ∀ (a : Joint → ℝ), ContDiffOn ℝ ∞ a (V ×ˢ {ξ : E | ξ ≠ 0}) →
      (∀ x ∈ Kplus, ∀ ξ : E, a (x, -ξ) = -a (x, ξ)) →
      (∀ x ∈ Kplus, ∀ t : ℝ, 0 < t → ∀ ξ : E, a (x, t • ξ) = t * a (x, ξ)) →
    ∀ (ϑ : ℝ → ℝ), ContDiff ℝ ∞ ϑ → (∀ t : ℝ, 1 ≤ t → ϑ t = 0) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1) → (∀ t : ℝ, |ϑ t| ≤ 1) →
    ∀ (κ : ℝ) (hκ : 0 < κ), κ < 1 / 16 →
    ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
    ∀ (cThin : ℝ) (hcThin : 0 < cThin), cThin ≤ c₀ →
    ∀ inn out : ℝ, 0 ≤ inn → inn < out → out ≤ D →
    let η := cThin * κ * δ ^ 2
    let hη : 0 < η := by dsimp only [η]; positivity
    let wide (x : E) (hx : x ∈ Kplus) :
        WideScreenFrequencySmooth i o (inverseMatrix (g₀ x)) :=
      wideScreen_frequencySmooth_of_joint joint (hKV hx)
    ∃ (B₁ : ℝ) (S : E → GaugeScreen), 1 ≤ B₁ ∧
      (∀ x (hx : x ∈ Kplus), S x = (thinScreenAngular (inverseMatrix (g₀ x)) i o
        (wide x hx) hη inn out).matrix) ∧
      (∀ x (hx : x ∈ Kplus), ActualFarPhaseIdentities (g₀ x) (fun ξ => a (x, ξ))
        ϑ κ δ b i o (wide x hx) hη inn out) ∧
    ∀ ℓ : ℝ, 0 < ℓ → ℓ < ℓ₀ →
    ∃ (s : Finset LatticeIndex) (χ χplus : LatticeIndex → E → ℝ),
      let W (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6 * ℓ)
      let C := (16 ^ 3 : ℝ) * (6 * B₁ ^ 5)
      (∀ x ∈ thickening ℓ K, ∑ j ∈ s, χ j x ^ 3 = 1) ∧
      (∀ x ∈ thickening ℓ K, ∀ v : E, ∑ j ∈ s, χ j x ^ 2 * fderiv ℝ (χ j) x v = 0) ∧
      (∑ j ∈ s, volume (W j)) ≤ ((17 ^ 4 : ℕ) : ℝ≥0∞) * volume Kplus ∧
      (∀ j ∈ s, ContDiff ℝ ∞ (χ j) ∧ ContDiff ℝ ∞ (χplus j) ∧
        (∀ x, 0 ≤ χ j x ∧ χplus j x ∈ Icc (0 : ℝ) 1) ∧
        tsupport (χ j) ⊆ closedBall (patchCenter ℓ j) (4 * ℓ) ∧
        tsupport (χplus j) ⊆ W j ∧ W j ⊆ interior Kplus ∧
        (∀ x ∈ thickening ℓ (tsupport (χ j)), χplus j x = 1) ∧
        (∀ k x, ‖iteratedFDeriv ℝ k (χ j) x‖ ≤ Ccut k * ℓ⁻¹ ^ k ∧
          ‖iteratedFDeriv ℝ k (χplus j) x‖ ≤ Ccut k * ℓ⁻¹ ^ k)) ∧
      (∀ j ∈ s, ∀ᶠ n in atTop, ∃ z : ProjectionSchwartzMatrix,
        (∀ i k x, z i k x = ((χ j x * (G n x i k - g₀ x i k) : ℝ) : ℂ)) ∧
        ∀ p : {p : ℝ // 1 < p}, ProjectedPatchLpBounds p.val z (W j)
          (Cp p * e n) (Cp p * (1 + e n / ℓ))) ∧
      (∀ᶠ n in atTop, ∀ j ∈ s,
        let x₀ := patchCenter ℓ j
        let m := matrixInverse (g₀ x₀)
        ∃ (A : ProjectedSourceCoefficients) (z : ProjectionSchwartzMatrix)
          (d : Index → Index → SchwartzMap E ℝ),
          (∀ i k x, z i k x = ((χ j x * (G (σ n) x i k - g₀ x i k) : ℝ) : ℂ)) ∧
          (∀ i k x, A.entry i k x = ((m i k + d i k x : ℝ) : ℂ)) ∧
          (∀ i k x, d i k x = correctionCoefficientPart (χplus j) (matrixInverse ∘ G (σ n)) m x i k) ∧
          (∀ i k, d i k = d k i) ∧
          GaugePatchCoefficientBounds B₁ ℓ (e (σ n)) d z (W j) ∧
          (‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤
            B₁ * (volume (W j) ^ ((1 : ℝ) / 2)).toReal *
              (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e (σ n))) ∧
          (∀ p : {p : ℝ // 1 < p}, ProjectedPatchLpBounds p.val z (W j)
            (Cp p * e (σ n)) (Cp p * (1 + e (σ n) / ℓ)))) ∧
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ Z : LatticeIndex → ProjectionSchwartzMatrix,
        (∀ j ∈ s, ∀ i k x, Z j i k x = ((χ j x * (G (σ n) x i k - g₀ x i k) : ℝ) : ℂ)) →
        let x := patchCenter ℓ
        let NWG (j : LatticeIndex) :=
          originalGaugePhysicalNumerator ϑ κ (g₀ (x j)) (fun ξ => a (x j, ξ)) (S (x j)) (Z j)
        let NWF (j : LatticeIndex) : Joint → ℂ := by
          classical
          exact if hx : x j ∈ Kplus then originalFarPatchFourierWeight (g₀ (x j)) (fun ξ => a (x j, ξ))
            ϑ κ δ i o (wide (x j) hx) hη inn out (Z j) else 0
        (∀ j ∈ s, Integrable (NWG j) ∧ Integrable (NWF j)) ∧
        (∑ j ∈ s, (‖(tau ^ 8)⁻¹ • ∫ y, NWG j y‖ + ‖(tau ^ 8)⁻¹ • ∫ y, NWF j y‖)) ≤
          C * (17 ^ 4 : ℝ) * (volume Kplus).toReal * ℓ + ε := by
  classical
  intro g₀ G
  have hG₀ (i j : Index) : ContDiffOn ℝ ∞ (fun x => g₀ x i j) c.chart.target :=
    fixedForm_components_smooth B hB c i j
  have hG (n : ℕ) (i j : Index) : ContDiffOn ℝ ∞ (fun x => G n x i j) c.chart.target :=
    fixedForm_components_smooth (g n) (hg n) c i j
  have hSym₀ (x : E) (_ : x ∈ c.chart.target) : IsSymmetricTensor (g₀ x) :=
    fun i j => hSig.isSymmetric (c.chart.symm x) _ _
  have hSym (n : ℕ) (x : E) (_ : x ∈ c.chart.target) : IsSymmetricTensor (G n x) :=
    fun i j => hgs n (c.chart.symm x) _ _
  have hConv : TendstoUniformlyOn G g₀ atTop Kplus :=
    fixed_components_uniform_of_physical_C0loc r g B hconv c Kplus hKplus hKU
  let errors (n : ℕ) := insert (0 : ℝ) ((fun x => ‖G n x - g₀ x‖) '' Kplus)
  let e (n : ℕ) := sSup (errors n)
  have hCont₀ : ContinuousOn g₀ Kplus :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => ((hG₀ i j).continuousOn.mono hKU)
  have hCont (n : ℕ) : ContinuousOn (G n) Kplus :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => ((hG n i j).continuousOn.mono hKU)
  have hBdd (n : ℕ) : BddAbove (errors n) :=
    (hKplus.bddAbove_image (((hCont n).sub hCont₀).norm)).insert _
  have he₀ (n : ℕ) : 0 ≤ e n := le_csSup (hBdd n) (Set.mem_insert _ _)
  have hError (n : ℕ) (x : E) (hx : x ∈ Kplus) : ‖G n x - g₀ x‖ ≤ e n :=
    le_csSup (hBdd n) (Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩)
  have he : Tendsto e atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (he₀ n), ?_⟩
    intro a ha
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hConv (a / 2) (half_pos ha)] with n hn
    have hSup : e n ≤ a / 2 := by
      apply csSup_le (Set.insert_nonempty _ _)
      intro v hv
      rcases Set.mem_insert_iff.mp hv with rfl | ⟨x, hx, rfl⟩
      · exact (half_pos ha).le
      have hxErr := hn x hx
      rw [dist_comm, dist_eq_norm] at hxErr
      exact hxErr.le
    exact hSup.trans_lt (half_lt_self ha)
  obtain ⟨Djet, hDjet, hJet⟩ :=
    fixedForm_firstJet_uniform_bound_on_compact r g B hg hB hSig.isNondegenerate hconv hDh c hKplus hKU
  obtain ⟨ℓ₀, Ccut, Cp, hℓ₀, hCut, hCp, budget⟩ :=
    exists_commonFarGauge_patchBudget c.chart.target K Kplus c.chart.open_target hK hKplus hNested hKU g₀ G
      hG₀ hG
      (fun _ => fixedForm_det_ne_zero B hSig.isNondegenerate c)
      (fun n _ => fixedForm_det_ne_zero (g n) (hgn n) c)
      hSym₀ hSym (fun n x hx => fixedForm_coordinateVacuum_of_intrinsic
        (g n) (hg n) (hgs n) (hgn n) (hVac n) c x hx) hConv Djet hDjet hJet e he₀ he hError σ hσ
  refine ⟨e, he₀, he, hError, ℓ₀, Ccut, Cp, hℓ₀, hCut, hCp, ?_⟩
  intro D hD
  obtain ⟨hCompact, hFrame⟩ := compact_chartInverseMetric_family B hB hSig c Kplus hKplus hKU
  obtain ⟨_, _, _, _, _, selectGuard⟩ := exists_originalFarPatch_selectGuard
  obtain ⟨c₀, b, hc₀, hb, guard⟩ := selectGuard hCompact hFrame D hD
  refine ⟨c₀, b, hc₀, hb, ?_⟩
  intro V hV hKV hVU i o joint a ha odd hom ϑ hϑ cut flat bounded κ hκ hsmall
    δ hδ hd cThin hcThin hcThin' inn out hin hio hout η hη wide
  have hFiber (x : E) (hx : x ∈ Kplus) :
      ContDiffOn ℝ ∞ (fun ξ => a (x, ξ)) ({0}ᶜ : Set E) := by
    have smooth : ContDiff ℝ ∞ (fun ξ : E => (x, ξ)) := contDiff_const.prodMk contDiff_id
    exact ha.comp smooth.contDiffOn (fun _ hξ => ⟨hKV hx, hξ⟩)
  have phase (x : E) (hx : x ∈ Kplus) :
      ActualFarPhaseIdentities (g₀ x) (fun ξ => a (x, ξ)) ϑ κ δ b i o (wide x hx) hη inn out :=
    (guard (g₀ x) ⟨x, hx, rfl⟩ (fun ξ => a (x, ξ)) (fun ξ _ => odd x hx ξ)
      (fun t ht ξ _ => hom x hx t ht ξ) (hFiber x hx) ϑ hϑ cut flat κ hκ hsmall δ hδ hd
      cThin hcThin hcThin' i o (wide x hx) inn out hin hio hout hη).1
  obtain ⟨S, same, jets⟩ :=
    exists_intrinsicCorrection_jets_of_jointWideScreen B hB hSig c V Kplus hV hKplus hKV hVU
      i o joint a ha ϑ hϑ κ hκ δ b hη inn out
  obtain ⟨B₁, hB₁, patches⟩ := budget ϑ cut κ hκ hsmall a (by simpa using hFiber) odd hom
    δ b i o wide hη inn out S same jets
  refine ⟨B₁, S, hB₁, same, phase, ?_⟩
  intro ℓ hℓ hℓsmall
  obtain ⟨s, χ, χplus, unity, derivative, volumeBound, cutoff, allP, source, tail⟩ := patches ℓ hℓ hℓsmall
  refine ⟨s, χ, χplus, unity, derivative, volumeBound, cutoff, allP, ?_, ?_⟩
  · filter_upwards [source] with n hn
    intro j hj
    obtain ⟨A, z, d, hz, hA, hd, hds, hCoeff, hSource, hNorms, _⟩ := hn j hj
    exact ⟨A, z, d, hz, hA, hd, hds, hCoeff, hSource, hNorms⟩
  have hCenters (j : LatticeIndex) (hj : j ∈ s) : patchCenter ℓ j ∈ Kplus := by
    obtain ⟨_, _, _, _, _, hWin, _, _⟩ := cutoff j hj
    exact interior_subset (hWin (mem_closedBall_self (by positivity)))
  have hTranspose (x : E) (hx : x ∈ Kplus) : (g₀ x)ᵀ = g₀ x :=
    funext fun i => funext fun j => hSym₀ x (hKU hx) j i
  obtain ⟨J, hJ, jet⟩ := jets 0
  intro ε hε
  filter_upwards [tail ε hε] with n hn
  intro Z hZ
  have realZ (j : LatticeIndex) (hj : j ∈ s) (i k : Index) (x : E) :
      conj (Z j i k x) = Z j i k x := by
    rw [hZ j hj i k x]
    exact Complex.conj_ofReal _
  exact originalCorrectionFourierSum_of_sharedBudget g₀ Kplus hTranspose a hFiber odd hom
    ϑ hϑ cut bounded κ hκ hsmall δ b i o wide hη inn out S same phase J hJ
    (fun x hx k j l => (jet x hx k j l).2) ℓ s hCenters Z realZ _ (hn Z hZ)

end Burnett.V11
