import Burnett.Analysis.AllScaleTransfer.SignedCapEndpointM0
import Burnett.Analysis.AllScaleTransfer.PositiveRatioTrace

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.A05

open Set Metric MeasureTheory
open Burnett.Analysis CapFourier LowRatio ProjectiveNullCaps
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open scoped ContDiff ENNReal

/-- The actual capped low-pass trace estimate uses the same one-sided
C100 budget as the article. A constant ratio lift changes no zero trace. -/
theorem exists_actual_cap_radian_M0_bound_of_oneSidedC100
    (B tube outer enlarged b : ℝ) (hB : 0 < B) (hTube : 0 < tube)
    (hOut : 0 ≤ outer) (hOE : outer < enlarged) (hb : 0 < b) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧ ∀ (U : Set Angles), IsOpen U →
      closedBall (0 : EndpointAngle) R ×ˢ closedBall (0 : EndpointAngle) R ⊆ U →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : E → E → ℝ → ℂ) (A : ℝ), 0 ≤ A →
        (∀ signs : CapSigns, ContDiffOn ℝ 100 (signedEndpointProfile M signs) (U ×ˢ Ico (0 : ℝ) b) ∧
          ∀ j ≤ 100, ∀ z ∈ U ×ˢ Ico (0 : ℝ) b,
            ‖iteratedFDerivWithin ℝ j (signedEndpointProfile M signs) (U ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) →
        ∀ (m : Form) (u : Vec) (F : NullCapChart m u),
          ‖u‖ = 1 → ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
          ∀ (δ : ℝ) (hδ : 0 < δ), 4 * B * (5 * δ) ≤ 1 → ∀ (gap : ℕ) (f g h : SchwartzMap E ℂ),
            EndpointFiniteAnnulus f → EndpointFiniteAnnulus g →
            let L := capFrequencyEquiv F hδ.ne'
            let K := tsupport (enlargedCapMultiplier m δ (tube * δ^2) outer enlarged u)
            (∀ p, radianFourier f p ≠ 0 → L p ∈ K) → (∀ q, radianFourier g q ≠ 0 → L q ∈ K) →
            ‖radianTrilinearForm (fun p => capEndpointM0Symbol M p * capEndpointWindowSum gap p) f g h‖ ≤
              C * A * ‖f.toLp (ENNReal.ofReal 3) volume‖ * ‖g.toLp (ENNReal.ofReal 3) volume‖ *
                ‖h.toLp (ENNReal.ofReal 3) volume‖ := by
  obtain ⟨α,r,R,_,_,hr,hrR,hR,old⟩ := exists_actual_cap_radian_M0_bound B tube outer enlarged hB hTube hOut hOE
  refine ⟨R,hr.trans hrR,hR,?_⟩
  intro U hU hChart
  obtain ⟨C,hC,estimate⟩ := old U hU (-1) 1 4 (by norm_num) (by norm_num) (by norm_num) hChart
  refine ⟨C,hC,?_⟩
  intro M A hA source m u F hu hInv δ hδ hSmall gap f g h hf hg L K hF hG
  let M' (p q : E) (_ : ℝ) := M p q 0
  have hJet (signs : CapSigns) :
      ContDiffOn ℝ 100 (signedEndpointProfile M' signs) (Window U (-1) 1) ∧
      ∀ j ≤ 100, ∀ z ∈ Window U (-1) 1, ‖iteratedFDeriv ℝ j (signedEndpointProfile M' signs) z‖ ≤ A := by
    have e : signedEndpointProfile M' signs = zeroRatioTraceExtension (signedEndpointProfile M signs) := rfl
    rw [e]
    exact zeroRatioTraceExtension_jets_of_oneSidedC100 hU hb (-1) 1
      (signedEndpointProfile M signs) A hA (source signs).1 (source signs).2
  have result := estimate M' A hA hJet m u F hu hInv δ hδ hSmall gap f g h hf hg hF hG
  exact result.2

end Burnett.A05
