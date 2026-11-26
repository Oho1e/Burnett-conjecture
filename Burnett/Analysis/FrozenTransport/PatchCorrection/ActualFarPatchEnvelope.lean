import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualFarA08Pair
import Burnett.Analysis.TransportPatches.PatchCorrectionOperatorPatchBound
import Burnett.Analysis.FrozenTransport.PatchCorrection.UniformAngularJets

set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option maxRecDepth 4800

noncomputable section

namespace Burnett.V10.OriginalGaugeCompatibility

open Set Metric MeasureTheory Burnett.A06 Burnett.A07 Burnett.A08 Burnett.P01 Burnett.C02 Burnett.C03 Burnett.V03
open Burnett.Analysis.TransportWardSymbol (Mat inverseMatrix)
open Burnett.Analysis.ProjectiveNullCaps (Vec)
open Burnett.A02.FrequencySplit (E Joint radianFourier)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.V11 (GaugeProfileBound)
open scoped ContDiff ENNReal BigOperators Matrix.Norms.Elementwise

theorem correctionInputWindow_smooth : ContDiff ℝ ∞ correctionInputWindow :=
  gaugeProjectionInfrared_contDiff.comp (contDiff_const.mul contDiff_id)

theorem correctionInputWindow_zero (s : ℝ) (hs : s ≤ 1 / 2) : correctionInputWindow s = 0 :=
  gaugeProjectionInfrared_zero (by linarith)

theorem correctionInputWindow_one (s : ℝ) (hs : 1 ≤ s) : correctionInputWindow s = 1 :=
  gaugeProjectionInfrared_one (by linarith)

theorem correctionRatioWindow_smooth : ContDiff ℝ ∞ correctionRatioWindow :=
  contDiff_const.sub (gaugeProjectionInfrared_contDiff.comp (contDiff_const.mul contDiff_id))

theorem correctionRatioWindow_zero (s : ℝ) (hs : (1 / 4 : ℝ) ^ 2 ≤ s) : correctionRatioWindow s = 0 := by
  rw [correctionRatioWindow, gaugeProjectionInfrared_one (show 2 ≤ 64 * s by linarith), sub_self]

def actualFarPatchEnergy (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ) (κ δ b i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (z : ProjectionSchwartzMatrix) : ℂ :=
  let m := inverseMatrix g
  let f := projectionFullSchwartz z
  ∑ I : OrderedPair, ∑ J : OrderedPair, ∑ k : OrderedPair,
    let F := actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k J I
    Complex.I * (radianHighPair F (f k.1 k.2) (f J.1 J.2) (constantWave m (f I.1 I.2)) -
      radianHighPair F (f k.1 k.2) (constantWave m (f J.1 J.2)) (f I.1 I.2))

/-- The exact far correction consumes the original C03 scalar source and
gradient bounds, using the same original physical projection in all slots. -/
theorem exists_actualFar_projectedPatch_envelope :
    ∃ (K : ℕ) (Co Cw : ℝ), 0 ≤ Co ∧ 0 ≤ Cw ∧
      ∀ (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ), (∀ s : ℝ, 1 ≤ s → ϑ s = 0) →
      ∀ (κ : ℝ), 0 < κ → κ < 1 / 16 → ∀ (δ b i o : ℝ),
      ∀ (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ),
      ∀ M : ℝ, 0 ≤ M → (∀ k J I, GaugeProfileBound K M
        (actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k J I)) →
      ∀ (d : Fin 4 → Fin 4 → SchwartzMap E ℝ) (A : ProjectedSourceCoefficients) (z : ProjectionSchwartzMatrix)
        (W : Set E) (B ℓ e : ℝ), 1 ≤ B → 0 < ℓ → 0 ≤ e → Co * M ≤ B → 2 * Cw * M ≤ B →
      (∀ r s, d r s = d s r) → (∀ r s x, A.entry r s x = ((inverseMatrix g r s + d r s x : ℝ) : ℂ)) →
      (∀ r s x, |d r s x| ≤ B * (ℓ + e)) → (∀ r s x, ‖fderiv ℝ (d r s : E → ℝ) x‖ ≤ B * (1 + e / ℓ)) →
      (‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤
        B * (volume W ^ ((1 : ℝ) / 2)).toReal * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e)) →
      (∃ v, ProjectedPatchLpBounds 2 z W v ((B / 4) * (1 + e / ℓ))) →
      ProjectedPatchLpBounds 4 z W (B * e) ((B / 4) * (1 + e / ℓ)) →
      ‖actualFarPatchEnergy g a ϑ κ δ b i o hm hη inn out z‖ ≤
        (16 ^ 3 : ℝ) * (3 * B ^ 5) * (volume W).toReal * Burnett.C04.correctionEnvelope ℓ e := by
  classical
  obtain ⟨K, _, _, Co, Cw, hCo, hCw, analytic⟩ := exists_originalAngular_projectedPatch_envelope
    correctionInputWindow correctionRatioWindow (r := 1 / 2) (ρ := 1 / 4) (R₀ := 1)
    (by norm_num) (by norm_num) (by norm_num) le_rfl correctionInputWindow_smooth
    correctionInputWindow_zero correctionInputWindow_one correctionRatioWindow_smooth correctionRatioWindow_zero
  refine ⟨K, Co, Cw, hCo, hCw, ?_⟩
  intro g a ϑ cut κ hκ hs δ b i o hm η hη inn out M hM jets d A z W B ℓ e hB hℓ he ho hw hd hA hD hL hSrc h₂ h₄
  let f := projectionFullSchwartz z
  let m := inverseMatrix g
  let F (k J I : OrderedPair) := actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k J I
  let val (I J k : OrderedPair) := Complex.I *
    (radianHighPair (F k J I) (f k.1 k.2) (f J.1 J.2) (constantWave m (f I.1 I.2)) -
      radianHighPair (F k J I) (f k.1 k.2) (constantWave m (f J.1 J.2)) (f I.1 I.2))
  let budget := (3 * B ^ 5) * (volume W).toReal * Burnett.C04.correctionEnvelope ℓ e
  have one (I J k : OrderedPair) : ‖val I J k‖ ≤ budget := by
    obtain ⟨V, hV, sub, smooth, hjet⟩ := jets k J I
    obtain ⟨P, bound⟩ := analytic hV sub smooth M hM (fun n hn p hp x => hjet n hn (p, (x : E)) ⟨hp, x.property⟩)
    have low (p : E) (hp : ‖p‖ ≤ 1) : radianFourier (f k.1 k.2) p = 0 := by
      simp [f, projectionFullSchwartz_radianFourier, regularizedComplexGaugeProjection, gaugeProjectionInfrared_zero hp]
    have actual (u v : SchwartzMap E ℂ) : inner ℂ (v.toLp 2 volume) (P.fullForward (f k.1 k.2) u) =
        radianHighPair (F k J I) (f k.1 k.2) u v := (P.fullPairs (f k.1 k.2) u v).1.trans
      (actualFarA08_pair g a ϑ cut κ hκ hs δ b i o hm hη inn out k J I (f k.1 k.2) low u v).symm
    have h := (bound m d A z W B ℓ e hB hℓ he ho hw hd hA hD hL hSrc h₂ h₄ f (Or.inl rfl)
      J.1 J.2 I.1 I.2 k.1 k.2).1
    change ‖Complex.I * weakConstantWaveCommutatorPair m (P.fullForward (f k.1 k.2))
      (f J.1 J.2) (f I.1 I.2)‖ ≤ budget at h
    simpa only [weakConstantWaveCommutatorPair, actual, val] using h
  change ‖∑ I, ∑ J, ∑ k, val I J k‖ ≤ _
  calc
    _ ≤ ∑ _I : OrderedPair, ∑ _J : OrderedPair, ∑ _k : OrderedPair, budget :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun J _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => one I J k)))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, budget]
      ring

end Burnett.V10.OriginalGaugeCompatibility
