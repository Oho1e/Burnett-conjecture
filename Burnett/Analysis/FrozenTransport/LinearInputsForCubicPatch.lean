import Burnett.Analysis.FrozenTransport.ActualThinSchwartzField
import Burnett.Analysis.FrozenTransport.OriginalCubicPatchNorms
import Burnett.Analysis.TransportPatches.CompactFrequencyJets

set_option autoImplicit false
set_option maxRecDepth 5100
set_option maxHeartbeats 7200000
noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Metric Burnett.Fourier Burnett.RicciSymbol
open Burnett.A02.FrequencySplit Burnett.A02.FieldAndCoefficientReview
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix projectionFullSchwartz projectionInfraredAction
  radianFourier_projectionInfraredAction gaugeProjectionInfrared)
open Burnett.C03 (projectedGaugeComplement ProjectedPatchLpBounds)
open scoped BigOperators ComplexConjugate ContDiff ENNReal FourierTransform Topology

open private exists_angularOutput_finiteLp from Burnett.Analysis.TransportPatches.WideProjectedGradientLp
open private realFourier_reflection from Burnett.Analysis.FrozenTransport.FourierSchwartzTransportInputs

/-- A fixed actual thin screen is (L^3)-bounded on the undifferentiated
projected fields as well. Its bound here is used only for convergence of the
values with the patch and its cone parameters fixed. -/
theorem exists_actualThinSchwartzField_valueLp (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ProjectionSchwartzMatrix,
      euclideanFieldValueL3 (actualThinSchwartzField m wi wo hm hη i o z) ≤
        C * euclideanFieldValueL3 (fun k : OrderedPair => projectionFullSchwartz z k.1 k.2) := by
  let S := thinScreenAngular m wi wo hm hη i o
  let F (k j : OrderedPair) (w : E × E) := S.matrix w.2 k j
  have hf (k j : OrderedPair) : ContDiffOn ℝ ∞ (F k j) ((univ : Set E) ×ˢ ({0}ᶜ : Set E)) :=
    (S.smooth k j).comp contDiff_snd.contDiffOn fun _ hp => hp.2
  choose jBound hjBound hJets using fun k j =>
    compactChartFamily_uniform_frequency_jets {0} univ isCompact_singleton isOpen_univ
      (subset_univ _) (F k j) (hf k j)
  let J := ∑ k : OrderedPair, ∑ j : OrderedPair, jBound k j
  have hJ : 0 ≤ J := Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun j _ => hjBound k j))
  have hJdom (k j : OrderedPair) : jBound k j ≤ J :=
    (Finset.single_le_sum (fun a _ => hjBound k a) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun b _ => Finset.sum_nonneg (fun a _ => hjBound b a)) (Finset.mem_univ k))
  have hJet (k j : OrderedPair) (n : ℕ) (hn : n ≤ 6) (ξ : E) (hξ : ξ ∈ sphere (0 : E) 1) :
      ‖iteratedFDeriv ℝ n (fun ζ => S.matrix ζ k j) ξ‖ ≤ J :=
    (hJets k j 0 (mem_singleton 0) n hn ξ hξ).trans (hJdom k j)
  obtain ⟨K, hK, hOp⟩ := exists_angularOutput_finiteLp 3 (by norm_num)
  refine ⟨256 * (K * J), by positivity, fun z => ?_⟩
  let u (k : OrderedPair) := projectionFullSchwartz z k.1 k.2
  let v := actualThinSchwartzField m wi wo hm hη i o z
  let A := ∑ j : OrderedPair, eLpNorm (u j : E → ℂ) 3 volume
  have hThree : ENNReal.ofReal (3 : ℝ) = 3 := by norm_num
  have hA : A < ⊤ := ENNReal.sum_lt_top.2 (fun j _ => ((u j).memLp 3 volume).eLpNorm_lt_top)
  have hVal : eLpNorm (fieldValueArray u) 3 volume < ⊤ := (fieldValueArray_memLp u 3).eLpNorm_lt_top
  have hAVal : A.toReal ≤ 16 * euclideanFieldValueL3 u := by
    have h := component_values_L3_le_euclidean u
    rw [hThree, show Fintype.card OrderedPair = 16 by decide] at h
    have hb := ENNReal.toReal_mono
      ((ENNReal.mul_lt_top (by norm_num : (16 : ℝ≥0∞) < ⊤) hVal).ne) h
    simpa only [A, euclideanFieldValueL3, hThree, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hb
  have hRow (k : OrderedPair) : (eLpNorm (v k : E → ℂ) 3 volume).toReal ≤
      (K * J) * (16 * euclideanFieldValueL3 u) := by
    have hOutput : (v k).toLp 2 volume = S.output (fun j => (u j).toLp 2 volume) k := by
      rw [actualThinSchwartzField_toLp]
      change S.afterOriginalProjection.output (fun j => (z j.1 j.2).toLp 2 volume) k = _
      rw [S.afterOriginalProjection_output,
        show originalOrderedProjectedField (fun j => (z j.1 j.2).toLp 2 volume) =
          (fun j => (u j).toLp 2 volume) from funext (fun j =>
            (originalProjectedMatrixMultiplier_output _ j).symm.trans
              (originalProjectedMatrixMultiplier_output_eq_schwartz z j))]
    have h := (hOp S J hJ hJet u k).2
    change eLpNorm (S.output (fun j => (u j).toLp 2 volume) k : E → ℂ) (ENNReal.ofReal 3) volume ≤
      ENNReal.ofReal (K * J) * ∑ j, eLpNorm (u j : E → ℂ) (ENNReal.ofReal 3) volume at h
    rw [hThree, ← hOutput, eLpNorm_congr_ae ((v k).coeFn_toLp 2 volume)] at h
    have H := ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA).ne h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hK hJ)] at H
    exact H.trans (mul_le_mul_of_nonneg_left hAVal (mul_nonneg hK hJ))
  calc
    euclideanFieldValueL3 v ≤ ∑ k, (eLpNorm (v k : E → ℂ) 3 volume).toReal :=
      euclideanFieldValueL3_le_entry_sum v
    _ ≤ ∑ _k : OrderedPair, (K * J) * (16 * euclideanFieldValueL3 u) :=
      Finset.sum_le_sum fun k _ => hRow k
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, show Fintype.card OrderedPair = 16 by decide, nsmul_eq_mul]
      norm_num
      ring

private theorem projectionInfraredAction_real (f : SchwartzMap E ℂ)
    (hf : ∀ x, conj (f x) = f x) (x : E) :
    conj (projectionInfraredAction f x) = projectionInfraredAction f x := by
  let w := projectionInfraredAction f
  let W := 𝓕 (w : E → ℂ)
  have hFourier (ξ : E) : W ξ = (gaugeProjectionInfrared ‖tau • ξ‖ : ℂ) * 𝓕 (f : E → ℂ) ξ := by
    change 𝓕 (w : E → ℂ) ξ = _
    rw [← radianFourier_scaled, radianFourier_projectionInfraredAction, radianFourier_scaled]
  have hW : (fun ξ => conj (W ξ)) = (fun ξ => W (-ξ)) := by
    funext ξ
    rw [hFourier, hFourier, map_mul, Complex.conj_ofReal, smul_neg, norm_neg, realFourier_reflection f hf]
  have hi : 𝓕⁻ W = (w : E → ℂ) :=
    w.continuous.fourier_inversion w.integrable (SchwartzMap.fourierTransformCLM ℂ w).integrable
  change conj ((w : E → ℂ) x) = (w : E → ℂ) x
  rw [← hi, ← fourier_conj_eq_conj_inverse, hW, ← Real.fourierIntegralInv_eq_fourierIntegral_comp_neg]

theorem projectedGaugeComplement_real_of_source (z : ProjectionSchwartzMatrix)
    (hz : ∀ a b x, conj (z a b x) = z a b x) (k : OrderedPair) (x : E) :
    conj (projectedGaugeComplement z k.1 k.2 x) = projectedGaugeComplement z k.1 k.2 x := by
  simp only [projectedGaugeComplement, SchwartzMap.sub_apply, map_sub,
    projectionInfraredAction_real _ (hz k.1 k.2), projectionFullSchwartz_real_of_source z hz k]

/-- Actual original, thin-screen and gauge fields on the same patch all have
vanishing (L^3) values. The two unaltered first derivatives keep their
explicit (64 C_{{grad}}|P|^{1/3}) budgets. -/
theorem actualLinearFields_C03_budget (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ℕ → ProjectionSchwartzMatrix) (P : Set E) (value : ℕ → ℝ) (grad : ℝ)
    (hSmall : Tendsto value atTop (𝓝 0))
    (hSource : ∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (z n) P (value n) grad) :
    let u (n : ℕ) (k : OrderedPair) := projectionFullSchwartz (z n) k.1 k.2
    let v (n : ℕ) := actualThinSchwartzField m wi wo hm hη i o (z n)
    let G (n : ℕ) (k : OrderedPair) := projectedGaugeComplement (z n) k.1 k.2
    let V := ((volume : Measure E) P).toReal ^ (1 / 3 : ℝ)
    Tendsto (fun n => euclideanFieldValueL3 (u n)) atTop (𝓝 0) ∧
      Tendsto (fun n => euclideanFieldValueL3 (v n)) atTop (𝓝 0) ∧
      Tendsto (fun n => euclideanFieldValueL3 (G n)) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, euclideanFieldGradientL3 (u n) ≤ (64 * grad) * V ∧
        euclideanFieldGradientL3 (G n) ≤ (64 * grad) * V := by
  intro u v G V
  have hBudget := hSource.mono (fun n h => originalPatch_euclideanLp_of_C03 (z n) P (value n) grad h)
  have hZero : Tendsto (fun n => 16 * value n * V) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (tendsto_const_nhds.mul hSmall).mul tendsto_const_nhds
  have hU : Tendsto (fun n => euclideanFieldValueL3 (u n)) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) (hBudget.mono fun _ h => h.1) hZero
  have hG : Tendsto (fun n => euclideanFieldValueL3 (G n)) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) (hBudget.mono fun _ h => h.2.1) hZero
  obtain ⟨C, _, hThin⟩ := exists_actualThinSchwartzField_valueLp m wi wo hm hη i o
  have hV : Tendsto (fun n => euclideanFieldValueL3 (v n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => hThin (z n))
      (by simpa only [mul_zero] using tendsto_const_nhds.mul hU)
  exact ⟨hU, hV, hG, hBudget.mono fun _ h => h.2.2⟩

end Burnett.C02
