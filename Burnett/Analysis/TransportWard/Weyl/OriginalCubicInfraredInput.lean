import Burnett.Analysis.FrozenTransport.ActualThinCubicReplacement
import Burnett.Analysis.FrozenTransport.FixedWindowDerivativeRemainder

set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 4400

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Set Burnett.A02.FrequencySplit Burnett.C02 Burnett.P01 Burnett.RicciSymbol
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.C03 (projectedGaugeComplement)
open Burnett.A07 (coordinateDerivative exists_fixedInfraredSchwartz_Lp_bound)
open scoped BigOperators ComplexConjugate ContDiff ENNReal Topology

open private fieldValueL3_sub_le fieldGradientL3_sub_le from Burnett.Analysis.FrozenTransport.OriginalCubicPatchNorms

/-- The original physical field and gauge field add to the literal fixed
high-pass input, entry by entry, with the same C03 raw field in both. -/
theorem originalCubicPhysical_add_gauge_val (z : ProjectionSchwartzMatrix)
    (hz : ∀ i j x, conj (z i j x) = z i j x) (k : OrderedPair) :
    (originalCubicPhysical z hz + originalCubicGauge z hz).val k = projectionInfraredAction (z k.1 k.2) := by
  change projectionFullSchwartz z k.1 k.2 +
    (projectionInfraredAction (z k.1 k.2) - projectionFullSchwartz z k.1 k.2) = _
  abel

private theorem tendsto_projectionInfrared_remainder_L3_zero (f : ℕ → SchwartzMap E ℂ)
    (hf : Tendsto (fun n => (eLpNorm (f n : E → ℂ) 3 volume).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => (eLpNorm ((f n - projectionInfraredAction (f n) : SchwartzMap E ℂ) : E → ℂ)
      3 volume).toReal) atTop (𝓝 0) := by
  obtain ⟨C, hC, hBound⟩ := exists_fixedInfraredSchwartz_Lp_bound gaugeProjectionInfrared
    gaugeProjectionInfrared_contDiff 1 2 zero_lt_one (fun _ h => gaugeProjectionInfrared_zero h)
    (fun _ h => gaugeProjectionInfrared_one h) 3 (by norm_num)
  have h₃ : ENNReal.ofReal (3 : ℝ) = 3 := by norm_num
  have hScale (g : SchwartzMap E ℂ) : eLpNorm (projectionInfraredAction g : E → ℂ) 3 volume ≤
      C * eLpNorm (g : E → ℂ) 3 volume := by
    simpa only [← h₃, projectionInfraredAction] using hBound g
  have hZero : Tendsto (fun n => (1 + C).toReal * (eLpNorm (f n : E → ℂ) 3 volume).toReal)
      atTop (𝓝 0) := by simpa only [mul_zero] using hf.const_mul (1 + C).toReal
  refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => ?_) hZero
  let g := f n
  let h := projectionInfraredAction g
  have hE : eLpNorm ((g - h : SchwartzMap E ℂ) : E → ℂ) 3 volume ≤ (1 + C) * eLpNorm (g : E → ℂ) 3 volume := by
    have he := eLpNorm_sub_le (g.memLp 3 volume).1 (h.memLp 3 volume).1 (by norm_num : (1 : ℝ≥0∞) ≤ 3)
    change eLpNorm ((g : E → ℂ) - (h : E → ℂ)) 3 volume ≤ _
    exact he.trans ((add_le_add_left (hScale g) _).trans_eq (by rw [add_mul, one_mul]))
  have hFinite : (1 + C) * eLpNorm (g : E → ℂ) 3 volume < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨by simp, hC⟩) (g.memLp 3 volume).eLpNorm_lt_top
  exact (ENNReal.toReal_mono hFinite.ne hE).trans_eq ENNReal.toReal_mul

/-- Both the value and the differentiated fixed low remainder tend to
zero on the original C03 field. No derivative smallness of that field
is needed to remove this fixed high-pass replacement. -/
theorem tendsto_originalCubicInfrared_remainder_W13_zero
    (z : ℕ → ProjectionSchwartzMatrix)
    (hY : Tendsto (fun n => euclideanFieldValueL3 (fun k : OrderedPair => z n k.1 k.2)) atTop (𝓝 0)) :
    Tendsto (fun n => euclideanFieldW13
      (fun k : OrderedPair => z n k.1 k.2 - projectionInfraredAction (z n k.1 k.2))) atTop (𝓝 0) := by
  let u (n : ℕ) (j : OrderedPair) := z n j.1 j.2
  let f (n : ℕ) (j : OrderedPair) := u n j - projectionInfraredAction (u n j)
  have h₃ : ENNReal.ofReal (3 : ℝ) = 3 := by norm_num
  have entry (j : OrderedPair) : Tendsto (fun n => (eLpNorm (u n j : E → ℂ) 3 volume).toReal) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => ?_) hY
    have hNorm : eLpNorm (u n j : E → ℂ) (ENNReal.ofReal 3) volume ≤
        eLpNorm (fieldValueArray (u n)) (ENNReal.ofReal 3) volume :=
      eLpNorm_mono (fun x => PiLp.norm_apply_le (fieldValueArray (u n) x) j)
    simpa only [h₃, euclideanFieldValueL3] using
      ENNReal.toReal_mono (fieldValueArray_memLp (u n) (ENNReal.ofReal 3)).eLpNorm_lt_top.ne hNorm
  have hValue (j : OrderedPair) := tendsto_projectionInfrared_remainder_L3_zero (fun n => u n j) (entry j)
  have hGrad (j : Index × OrderedPair) : Tendsto (fun n =>
      (eLpNorm (coordinateDerivative j.1 (f n j.2) : E → ℂ) 3 volume).toReal) atTop (𝓝 0) := by
    simpa only [h₃, f] using tendsto_projectionInfrared_coordinateDerivative_remainder_Lp_zero j.1 3
      (by norm_num) (fun n => u n j.2) (by simpa only [h₃] using entry j.2)
  have hValSum : Tendsto (fun n => ∑ j : OrderedPair, (eLpNorm (f n j : E → ℂ) 3 volume).toReal) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun j _ => hValue j)
  have hGradSum : Tendsto (fun n => ∑ j : Index × OrderedPair,
      (eLpNorm (coordinateDerivative j.1 (f n j.2) : E → ℂ) 3 volume).toReal) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun j _ => hGrad j)
  have hValZero : Tendsto (fun n => euclideanFieldValueL3 (f n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => euclideanFieldValueL3_le_entry_sum (f n)) hValSum
  have hGradZero : Tendsto (fun n => euclideanFieldGradientL3 (f n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => euclideanFieldGradientL3_le_entry_sum (f n)) hGradSum
  simpa only [euclideanFieldW13_eq, add_zero, f, u] using hValZero.add hGradZero

/-- Lower-frequency removal in the field costs a vanishing cubic error.
The frozen coefficients and the infrared symbol of the tested energy are
identical before and after this replacement. -/
theorem tendsto_originalRawCubic_sub_physicalGauge_zero
    (z : ℕ → ProjectionSchwartzMatrix) (hz : ∀ n i j x, conj (z n i j x) = z n i j x)
    (hY : Tendsto (fun n => euclideanFieldValueL3 (fun k : OrderedPair => z n k.1 k.2)) atTop (𝓝 0))
    (M : ℝ)
    (hX : ∀ᶠ n in atTop, euclideanFieldGradientL3 (fun k : OrderedPair => z n k.1 k.2) ≤ M)
    (c : EnergyIndex OrderedPair → OrderedPair → ℝ)
    (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l)
    (q : Index → Index → OrderedPair → OrderedPair → OrderedPair → ℝ)
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (D : ℝ) (hD : 0 ≤ D)
    (hJets : ∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ Metric.sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) :
    let β := fixedInfraredSymbol cut 0 b
    let raw (n : ℕ) : RealEnergyField OrderedPair := ⟨fun j => z n j.1 j.2, fun j => hz n j.1 j.2⟩
    let hi (n : ℕ) := originalCubicPhysical (z n) (hz n) + originalCubicGauge (z n) (hz n)
    Tendsto (fun n => |completeCubicEnergy c q β (raw n) - completeCubicEnergy c q β (hi n)|) atTop (𝓝 0) := by
  intro β raw hi
  let E₀ (v : RealEnergyField OrderedPair) := completeCubicEnergy c q β v
  let W (v : RealEnergyField OrderedPair) := euclideanFieldW13 v.val
  obtain ⟨A,hA,estimate⟩ := fixed_infrared_complete_continuity_euclidean c hc q cut 0 hcut (fun _ => by simp)
  have hEq (n : ℕ) : (raw n - hi n).val = fun k => z n k.1 k.2 - projectionInfraredAction (z n k.1 k.2) := by
    funext j
    change (raw n).val j - (hi n).val j = _
    rw [originalCubicPhysical_add_gauge_val (z n) (hz n) j]
  have hSmall : Tendsto (fun n => W (raw n - hi n)) atTop (𝓝 0) := by
    simpa only [W, hEq] using tendsto_originalCubicInfrared_remainder_W13_zero z hY
  have Wsub (v u : RealEnergyField OrderedPair) : W (v - u) ≤ W v + W u := by
    change euclideanFieldW13 (v.val - u.val) ≤ euclideanFieldW13 v.val + euclideanFieldW13 u.val
    simp only [euclideanFieldW13_eq]
    linarith only [fieldValueL3_sub_le v.val u.val, fieldGradientL3_sub_le v.val u.val]
  let B := 2 * (M + 1) + 1
  have hPair : ∀ᶠ n in atTop, W (raw n) + W (hi n) ≤ B := by
    filter_upwards [hX, (tendsto_order.1 hY).2 1 zero_lt_one, (tendsto_order.1 hSmall).2 1 zero_lt_one]
      with n hxn hyn hdn
    have hW : W (raw n) ≤ M + 1 := by
      change euclideanFieldW13 (raw n).val ≤ M + 1
      rw [euclideanFieldW13_eq]
      exact (add_le_add hyn.le hxn).trans_eq (add_comm _ _)
    have hHi := Wsub (raw n) (raw n - hi n)
    rw [sub_sub_cancel] at hHi
    dsimp only [B]
    linarith
  have hUpper : Tendsto (fun n => (A * (D + 1)) * W (raw n - hi n) * B ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hSmall.const_mul (A * (D + 1))).mul_const (B ^ 2)
  refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hUpper
  filter_upwards [hPair] with n hn
  have hNonneg : 0 ≤ W (raw n) + W (hi n) := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  change |E₀ (raw n) - E₀ (hi n)| ≤ _
  exact (estimate b hb hom D hD hJets (raw n) (hi n)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hNonneg hn _)
      (mul_nonneg (mul_nonneg hA (by positivity)) (show 0 ≤ W (raw n - hi n) from ENNReal.toReal_nonneg)))

end Burnett.V03
