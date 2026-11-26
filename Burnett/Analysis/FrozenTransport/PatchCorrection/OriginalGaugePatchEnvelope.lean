import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualLowTriadInfrared
import Burnett.Analysis.TransportPatches.PatchCorrectionOperatorPatchBound
import Burnett.Analysis.FrozenTransport.PatchCorrection.UniformAngularJets

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option maxRecDepth 5500

noncomputable section
namespace Burnett.V11

open Set Metric Matrix MeasureTheory Burnett.P01 Burnett.A06 Burnett.A07 Burnett.A08 Burnett.V08 Burnett.C03
open Burnett.A02.FrequencySplit (E Joint)
open scoped ContDiff Matrix BigOperators ENNReal

def originalGaugePatchEnergy (θ : ℝ → ℝ) (κ : ℝ) (m : Fin 4 → Fin 4 → ℝ) (w : ℝ)
    (a : E → ℝ) (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen) (z : ProjectionSchwartzMatrix) : ℂ :=
  let u := projectionFullSchwartz z
  let T := originalGaugeRadianPair θ gaugeCorrectionInfrared gaugeCorrectionInfrared κ m w a C S z
  ∑ I : TensorSlot, ∑ J : TensorSlot, Complex.I * (T I J (u J.1 J.2) (constantWave m (u I.1 I.2)) -
    T I J (constantWave m (u J.1 J.2)) (u I.1 I.2))

/-- The universal jet order and both analytic constants are selected before
any patch, metric, test value or low field. The full matrix has 16³ ordered
low/input/output component contributions and retains both infrared factors. -/
theorem exists_originalGauge_patchEnvelope :
    ∃ (K : ℕ) (Co Cw : ℝ), 0 ≤ Co ∧ 0 ≤ Cw ∧
    ∀ (θ : ℝ → ℝ), (∀ t : ℝ, 1 ≤ t → θ t = 0) →
    ∀ (κ : ℝ), 0 < κ → κ < 1/16 → ∀ (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ),
    ContDiffOn ℝ ∞ a {x : E | x ≠ 0} → (∀ x, a (-x) = -a x) →
    (∀ t : ℝ, 0 < t → ∀ x, a (t • x) = t*a x) →
    ∀ (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen), (∀ t : ℝ, 0 < t → ∀ x, S (t • x) = S x) →
    ∀ M : ℝ, 0 ≤ M → (∀ k I J, GaugeProfileBound K M (gaugeTriadAngularProfile θ κ m w a C S k I J)) →
    ∀ (d : Fin 4 → Fin 4 → SchwartzMap E ℝ) (A : ProjectedSourceCoefficients) (z : ProjectionSchwartzMatrix)
      (W : Set E) (B ℓ e : ℝ), 1 ≤ B → 0 < ℓ → 0 ≤ e → Co*M ≤ B → 2*Cw*M ≤ B →
    (∀ r s, d r s = d s r) → (∀ r s x, A.entry r s x = ((m r s + d r s x : ℝ) : ℂ)) →
    (∀ r s x, |d r s x| ≤ B*(ℓ+e)) → (∀ r s x, ‖fderiv ℝ (d r s : E → ℝ) x‖ ≤ B*(1+e/ℓ)) →
    (‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤ B*(volume W ^ ((1:ℝ)/2)).toReal*(1+ℓ⁻¹+(ℓ^2)⁻¹*e)) →
    (∃ v, ProjectedPatchLpBounds 2 z W v ((B/4)*(1+e/ℓ))) →
    ProjectedPatchLpBounds 4 z W (B*e) ((B/4)*(1+e/ℓ)) →
    ‖originalGaugePatchEnergy θ κ m w a C S z‖ ≤ (16^3 : ℝ)*(3*B^5)*(volume W).toReal*Burnett.C04.correctionEnvelope ℓ e := by
  classical
  let η := gaugeCorrectionInfrared
  obtain ⟨K,C₀,C₁,Co,Cw,hCo,hCw,analytic⟩ := exists_originalAngular_projectedPatch_envelope η gaugeRatioGuard
    (r:=1/2) (ρ:=1/4) (R₀:=1) (by norm_num) (by norm_num) (by norm_num) le_rfl gaugeCorrectionInfrared_smooth
    gaugeCorrectionInfrared_zero gaugeCorrectionInfrared_one gaugeRatioGuard_smooth (fun _ h => gaugeRatioGuard_vanishes h)
  refine ⟨K,Co,Cw,hCo,hCw,?_⟩
  intro θ hcut κ hκ hsmall m w a ha hOdd hHom C S hS M hM jets d A z W B ℓ e hB hℓ he ho hw hd hA hD hL hSrc h₂ h₄
  let f := projectionFullSchwartz z
  let H (k : TensorSlot) := projectedGaugeComplement z k.1 k.2
  let b (k I J : TensorSlot) := gaugeRawEntry θ η η κ m w a C S k I J
  let val (I J k : TensorSlot) := Complex.I * (radianHighPair (b k I J) (H k) (f J.1 J.2) (constantWave m (f I.1 I.2)) -
    radianHighPair (b k I J) (H k) (constantWave m (f J.1 J.2)) (f I.1 I.2))
  let budget := (3*B^5)*(volume W).toReal*Burnett.C04.correctionEnvelope ℓ e
  have one (I J k : TensorSlot) : ‖val I J k‖ ≤ budget := by
    obtain ⟨V,hV,sub,smooth,hjet⟩ := jets k I J
    obtain ⟨P,bound⟩ := analytic hV sub smooth M hM (fun n hn p hp x => hjet n hn (p,(x:E)) ⟨hp,x.property⟩)
    have actual (u v : SchwartzMap E ℂ) : inner ℂ (v.toLp 2 volume) (P.fullForward (H k) u) =
        radianHighPair (b k I J) (H k) u v := (P.fullPairs (H k) u v).1.trans
      (actualGaugeA08_pair θ hcut κ hκ hsmall m w a ha hOdd hHom C S hS k I J (H k) (gaugeLow_spectrum_zero z k) u v).symm
    have h := (bound m d A z W B ℓ e hB hℓ he ho hw hd hA hD hL hSrc h₂ h₄ (projectedGaugeComplement z) (Or.inr rfl)
      J.1 J.2 I.1 I.2 k.1 k.2).1
    change ‖Complex.I * weakConstantWaveCommutatorPair m (P.fullForward (H k)) (f J.1 J.2) (f I.1 I.2)‖ ≤ budget at h
    simpa only [weakConstantWaveCommutatorPair, actual, val] using h
  have expand : originalGaugePatchEnergy θ κ m w a C S z = ∑ I, ∑ J, ∑ k, val I J k := by
    simp only [originalGaugePatchEnergy,originalGaugeRadianPair,← Finset.sum_sub_distrib,Finset.mul_sum,val,b,H,f,η]
  rw [expand]
  calc
    _ ≤ ∑ _I : TensorSlot, ∑ _J : TensorSlot, ∑ _k : TensorSlot, budget :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun J _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => one I J k)))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,budget]; ring

end Burnett.V11
