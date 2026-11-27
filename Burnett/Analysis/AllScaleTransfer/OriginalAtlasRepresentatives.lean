import Burnett.Analysis.AllScaleTransfer.UnscaledEndpointTrace

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.A05

open Filter MeasureTheory Metric Set
open Burnett.Analysis.CapFourier Burnett.C02 Burnett.A02.FrequencySplit
open Burnett.Analysis.LowRatio (Point)
open scoped ContDiff

/-- The ordinary unscaled low-budget consumer obtains all three traces
from its positive-ratio chart formulas. -/
theorem analyticNearUnscaledLowBudget_of_positiveAtlas
    (ϑ : ℝ → ℝ) (κ b A : ℝ) (hb : 0 < b) (hA : 0 ≤ A) (m : Joint → ℂ)
    (atlas : ∀ slot : Fin 3, ∃ M : WardPairChart → Point → ℂ,
      (∀ i, ContDiffOn ℝ 100 (M i) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) b)) ∧
      (∀ i n, n ≤ 100 → ∀ z ∈ wardPairChartDomain i ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n (M i) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) ∧
      ∀ i pq, pq ∈ wardPairChartAnnulus i → ∀ t : ℝ, 0 < t →
        let ρ := t*(‖pq.1‖/‖pq.2‖)
        ρ ∈ Ioo (0 : ℝ) b →
          radianFourBranchSymbol ϑ κ (radianLowSlotView m slot) 0 (t • pq.1,pq.2) =
            M i (wardPairChartAngles i pq,ρ)) :
    AnalyticNearUnscaledLowBudget ϑ κ b A m := by
  intro slot
  obtain ⟨M,hM,hJets,hPositive⟩ := atlas slot
  obtain ⟨M₀,_,_,hTrace⟩ := exists_wardPair_zeroRatioTrace_of_positiveAgreement b A hb hA
    (radianFourBranchSymbol ϑ κ (radianLowSlotView m slot) 0) M hM hJets hPositive
  exact ⟨M,M₀,hM,hJets,hTrace,hPositive⟩

/-- The nonzero signed triads in the frequency plane. -/
def nonzeroSignedTriads : Set Joint := {pq | pq.1 ≠ 0 ∧ pq.2 ≠ 0 ∧ -(pq.1 + pq.2) ≠ 0}

theorem isOpen_nonzeroSignedTriads : IsOpen nonzeroSignedTriads :=
  (isOpen_ne_fun continuous_fst continuous_const).inter
    ((isOpen_ne_fun continuous_snd continuous_const).inter
      (isOpen_ne_fun (continuous_fst.add continuous_snd).neg continuous_const))

theorem ae_nonzeroSignedTriads : ∀ᵐ pq ∂(volume : Measure Joint), pq ∈ nonzeroSignedTriads := by
  rw [Measure.volume_eq_prod, Measure.ae_prod_mem_iff_ae_ae_mem isOpen_nonzeroSignedTriads.measurableSet]
  filter_upwards [Set.countable_singleton (0 : E) |>.ae_notMem volume] with p hp
  filter_upwards [Set.countable_singleton (0 : E) |>.ae_notMem volume,
    Set.countable_singleton (-p) |>.ae_notMem volume] with q hq hsum
  refine ⟨fun h => hp (mem_singleton_iff.mpr h),fun h => hq (mem_singleton_iff.mpr h),fun h => ?_⟩
  have hpq : p + q = 0 := neg_eq_zero.mp h
  apply hsum
  rw [mem_singleton_iff]
  calc
    q = -p + (p + q) := by abel
    _ = -p := by rw [hpq,add_zero]

/-- A bounded homogeneous symbol specified on the nonzero triads has an
actual bounded Borel representative and the same radian trilinear form. -/
theorem exists_analyticNearSymbol_of_nonzeroSignedTriads
    (m : Joint → ℂ) (A : ℝ) (hA : 0 ≤ A) (hCont : ContinuousOn m nonzeroSignedTriads)
    (hBound : ∀ p ∈ nonzeroSignedTriads, ‖m p‖ ≤ A)
    (hHom : ∀ t : ℝ, 0 < t → ∀ p ∈ nonzeroSignedTriads, m (t • p) = m p) :
    ∃ b : Joint → ℂ, AnalyticNearSymbol b ∧ (∀ p ∈ nonzeroSignedTriads, b p = m p) ∧
      ∀ f g w : SchwartzMap E ℂ, radianTrilinearForm b f g w = radianTrilinearForm m f g w := by
  classical
  let b := nonzeroSignedTriads.piecewise m (fun _ => 0)
  have coincide (p : Joint) (hp : p ∈ nonzeroSignedTriads) : b p = m p := by
    simp [b,hp]
  have dilation (t : ℝ) (ht : 0 < t) (p : Joint) : t • p ∈ nonzeroSignedTriads ↔ p ∈ nonzeroSignedTriads := by
    rcases p with ⟨p,q⟩
    simp only [nonzeroSignedTriads,mem_setOf_eq,Prod.smul_mk,← smul_add,← smul_neg,
      ne_eq,smul_eq_zero,ht.ne',false_or]
  refine ⟨b,⟨hCont.measurable_piecewise continuousOn_const isOpen_nonzeroSignedTriads.measurableSet,
      ⟨A,hA,?_⟩,?_⟩,coincide,?_⟩
  · intro p
    by_cases hp : p ∈ nonzeroSignedTriads
    · rw [coincide p hp]
      exact hBound p hp
    · simp [b,hp,hA]
  · intro t ht p
    by_cases hp : p ∈ nonzeroSignedTriads
    · rw [coincide p hp,coincide (t • p) ((dilation t ht p).mpr hp),hHom t ht p hp]
    · have htp : t • p ∉ nonzeroSignedTriads := fun h => hp ((dilation t ht p).mp h)
      simp [b,hp,htp]
  · intro f g w
    unfold radianTrilinearForm
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_nonzeroSignedTriads] with p hp
    simp only [radianTrilinearWeight,coincide p hp]

end Burnett.A05

#print axioms Burnett.A05.analyticNearUnscaledLowBudget_of_positiveAtlas
#print axioms Burnett.A05.exists_analyticNearSymbol_of_nonzeroSignedTriads
