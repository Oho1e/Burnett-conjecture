import Burnett.Analysis.AngularCaps.CapDistribution
import Burnett.Analysis.AngularCaps.ScaledCapHeightMoments
import Mathlib.Data.ENNReal.BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.Analysis.CapFourier

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι] {μ : Measure X}
variable {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]

private theorem cap_level_split (hq : 3 < q)
    (T : ι → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (U : ι → Lp ℂ (ENNReal.ofReal q) μ →L[ℂ] Lp ℂ (ENNReal.ofReal q) μ)
    (hTU : ∀ (i : ι) (f : X → ℂ) (f₂ : MemLp f 2 μ) (fq : MemLp f (ENNReal.ofReal q) μ),
      (U i (fq.toLp f) : X → ℂ) =ᵐ[μ] (T i (f₂.toLp f) : X → ℂ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (sqBound : ∀ f, (∑ i, ‖T i f‖^2) ≤ A * ‖f‖^2)
    (qBound : ∀ f, (∑ i, ‖U i f‖^q) ≤ B * ‖f‖^q)
    (f : X → ℂ) (hfm : Measurable f) (hf₂ : MemLp f 2 μ)
    (hfq : MemLp f (ENNReal.ofReal q) μ) (k : ℝ) {t : ℝ} (ht : 0 < t) :
    (∑ i, μ {x | 2*t < ‖T i (hf₂.toLp f) x‖} * (ENNReal.ofReal t)^(2:ℕ)) ≤
      ENNReal.ofReal A * (∫⁻ x in {x | t < k*‖f x‖}, (ENNReal.ofReal ‖f x‖)^(2:ℕ) ∂μ) +
        ENNReal.ofReal B * ((∫⁻ x in {x | k*‖f x‖ ≤ t}, (ENNReal.ofReal ‖f x‖)^q ∂μ) *
          ENNReal.ofReal (t^(2-q))) := by
  classical
  let H : Set X := {x | t < k*‖f x‖}
  let L : Set X := {x | k*‖f x‖ ≤ t}
  have hH : MeasurableSet H := measurableSet_lt measurable_const (hfm.norm.const_mul k)
  have hL : MeasurableSet L := measurableSet_le (hfm.norm.const_mul k) measurable_const
  let hi := (hf₂.indicator hH).toLp (H.indicator f)
  let lo := (hfq.indicator hL).toLp (L.indicator f)
  let lo₂ := (hf₂.indicator hL).toLp (L.indicator f)
  have split : hf₂.toLp f = hi + lo₂ := by
    change hf₂.toLp f = (hf₂.indicator hH).toLp (H.indicator f) +
      (hf₂.indicator hL).toLp (L.indicator f)
    rw [← MemLp.toLp_add,MemLp.toLp_eq_toLp_iff]
    refine Eventually.of_forall ?_
    intro x
    change f x = H.indicator f x + L.indicator f x
    by_cases hx : t < k*‖f x‖
    · simp [H,L,Set.indicator,hx,not_le_of_gt hx]
    · simp [H,L,Set.indicator,hx,le_of_not_gt hx]
  have split_ae (i : ι) : (T i (hf₂.toLp f) : X → ℂ) =ᵐ[μ] fun x => T i hi x + U i lo x := by
    rw [split,map_add]
    refine (Lp.coeFn_add _ _).trans ?_
    filter_upwards [(hTU i (L.indicator f) (hf₂.indicator hL) (hfq.indicator hL)).symm] with x hx
    change T i hi x + T i lo₂ x = T i hi x + U i lo x
    rw [show T i lo₂ x = U i lo x from hx]
  have tail (i : ι) : μ {x | 2*t < ‖T i (hf₂.toLp f) x‖} ≤
      μ {x | t < ‖T i hi x‖} + μ {x | t < ‖U i lo x‖} := by
    refine (measure_mono_ae ?_).trans (measure_union_le _ _)
    filter_upwards [split_ae i] with x he
    intro hx
    change 2*t < ‖T i (hf₂.toLp f) x‖ at hx
    rw [he] at hx
    change t < ‖T i hi x‖ ∨ t < ‖U i lo x‖
    by_contra h
    have hparts := not_or.mp h
    have htri := norm_add_le (T i hi x) (U i lo x)
    linarith only [htri,hx,le_of_not_gt hparts.1,le_of_not_gt hparts.2]
  have hq₀ : 0 < q := by linarith
  have hqp : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq₀
  let W := (ENNReal.ofReal t)^(2:ℕ)
  let V := ENNReal.ofReal (t^(2-q))
  have cheb₂ (i : ι) : W * μ {x | t < ‖T i hi x‖} ≤ ENNReal.ofReal (‖T i hi‖^2) := by
    simpa only [W,ENNReal.toReal_ofNat,sub_self,Real.rpow_zero,ENNReal.ofReal_one,one_mul,Real.rpow_two]
      using lp_tail_weighted_square (by norm_num) (by norm_num) (T i hi) ht
  have chebq (i : ι) : W * μ {x | t < ‖U i lo x‖} ≤ V * ENNReal.ofReal (‖U i lo‖^q) := by
    simpa only [W,V,ENNReal.toReal_ofReal hq₀.le] using
      lp_tail_weighted_square hqp ENNReal.ofReal_ne_top (U i lo) ht
  have moment₂ : ENNReal.ofReal (‖hi‖^2) =
      ∫⁻ x in H, (ENNReal.ofReal ‖f x‖)^(2:ℕ) ∂μ := by
    simpa only [hi,ENNReal.toReal_ofNat,Real.rpow_two,ENNReal.rpow_two,ofReal_norm_eq_enorm]
      using lp_indicator_moment (by norm_num) (by norm_num) hf₂ hH
  have momentq : ENNReal.ofReal (‖lo‖^q) = ∫⁻ x in L, (ENNReal.ofReal ‖f x‖)^q ∂μ := by
    simpa only [lo,ENNReal.toReal_ofReal hq₀.le,ofReal_norm_eq_enorm]
      using lp_indicator_moment hqp ENNReal.ofReal_ne_top hfq hL
  have sum₂ : (∑ i, ENNReal.ofReal (‖T i hi‖^2)) ≤
      ENNReal.ofReal A * (∫⁻ x in H, (ENNReal.ofReal ‖f x‖)^(2:ℕ) ∂μ) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖T i hi‖),
      ← moment₂,← ENNReal.ofReal_mul hA]
    exact ENNReal.ofReal_le_ofReal (sqBound hi)
  have sumq : (∑ i, ENNReal.ofReal (‖U i lo‖^q)) ≤
      ENNReal.ofReal B * (∫⁻ x in L, (ENNReal.ofReal ‖f x‖)^q ∂μ) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (U i lo)) q),
      ← momentq,← ENNReal.ofReal_mul hB]
    exact ENNReal.ofReal_le_ofReal (qBound lo)
  calc
    _ ≤ ∑ i, (ENNReal.ofReal (‖T i hi‖^2) + V * ENNReal.ofReal (‖U i lo‖^q)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [mul_comm _ W]
      exact (mul_le_mul_left' (tail i) W).trans (by
        rw [mul_add]
        exact add_le_add (cheb₂ i) (chebq i))
    _ = (∑ i, ENNReal.ofReal (‖T i hi‖^2)) + V * (∑ i, ENNReal.ofReal (‖U i lo‖^q)) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ ENNReal.ofReal A * (∫⁻ x in H, (ENNReal.ofReal ‖f x‖)^(2:ℕ) ∂μ) +
        V * (ENNReal.ofReal B * (∫⁻ x in L, (ENNReal.ofReal ‖f x‖)^q ∂μ)) :=
      add_le_add sum₂ (mul_le_mul_left' sumq V)
    _ = _ := by
      change _ + V * (ENNReal.ofReal B * (∫⁻ x in L, (ENNReal.ofReal ‖f x‖)^q ∂μ)) =
        _ + ENNReal.ofReal B * ((∫⁻ x in L, (ENNReal.ofReal ‖f x‖)^q ∂μ) * V)
      ac_rfl

/-- Fixed-exponent distribution argument for the finite cap sum. The two
endpoints act identically on their common inputs. -/
theorem cap_cube_moment_of_endpoints [SigmaFinite μ] (hq : 3 < q)
    (T : ι → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (U : ι → Lp ℂ (ENNReal.ofReal q) μ →L[ℂ] Lp ℂ (ENNReal.ofReal q) μ)
    (hTU : ∀ (i : ι) (f : X → ℂ) (f₂ : MemLp f 2 μ) (fq : MemLp f (ENNReal.ofReal q) μ),
      (U i (fq.toLp f) : X → ℂ) =ᵐ[μ] (T i (f₂.toLp f) : X → ℂ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (sqBound : ∀ f, (∑ i, ‖T i f‖^2) ≤ A * ‖f‖^2)
    (qBound : ∀ f, (∑ i, ‖U i f‖^q) ≤ B * ‖f‖^q)
    (f : X → ℂ) (hfm : Measurable f) (hf₂ : MemLp f 2 μ)
    (hfq : MemLp f (ENNReal.ofReal q) μ) {k : ℝ} (hk : 0 < k) :
    (∑ i, ∫⁻ x, ‖T i (hf₂.toLp f) x‖ₑ^(3:ℕ) ∂μ) ≤
      (24 * (ENNReal.ofReal A * ENNReal.ofReal k +
        ENNReal.ofReal B * ENNReal.ofReal (k^(3-q)/(q-3)))) *
        ∫⁻ x, ‖f x‖ₑ^(3:ℕ) ∂μ := by
  classical
  let g (x : X) := ‖f x‖
  let H (t : ℝ) := ∫⁻ x in {x | t < k*g x}, (ENNReal.ofReal (g x))^(2:ℕ) ∂μ
  let L (t : ℝ) := (∫⁻ x in {x | k*g x ≤ t}, (ENNReal.ofReal (g x))^q ∂μ) *
    ENNReal.ofReal (t^(2-q))
  let D (i : ι) (t : ℝ) := μ {x | 2*t < ‖T i (hf₂.toLp f) x‖} * (ENNReal.ofReal t)^(2:ℕ)
  have hg : Measurable g := hfm.norm
  have hHm : Measurable H := by
    let F (t : ℝ) (x : X) := if t < k*g x then (ENNReal.ofReal (g x))^(2:ℕ) else 0
    have mF : Measurable (Function.uncurry F) := by
      apply Measurable.ite (measurableSet_lt measurable_fst ((hg.comp measurable_snd).const_mul k))
      · fun_prop
      · exact measurable_const
    have e (t : ℝ) : H t = ∫⁻ x, F t x ∂μ := by
      unfold H
      rw [← lintegral_indicator (measurableSet_lt measurable_const (hg.const_mul k))]
      rfl
    rw [funext e]
    exact mF.lintegral_prod_right
  have hLm : Measurable L := by
    let F (t : ℝ) (x : X) := if k*g x ≤ t then (ENNReal.ofReal (g x))^q else 0
    have mF : Measurable (Function.uncurry F) := by
      apply Measurable.ite (measurableSet_le ((hg.comp measurable_snd).const_mul k) measurable_fst)
      · fun_prop
      · exact measurable_const
    have e (t : ℝ) : L t = (∫⁻ x, F t x ∂μ) * ENNReal.ofReal (t^(2-q)) := by
      unfold L
      rw [← lintegral_indicator (measurableSet_le (hg.const_mul k) measurable_const)]
      rfl
    rw [funext e]
    exact mF.lintegral_prod_right.mul (by fun_prop)
  have hDm (i : ι) : Measurable (D i) := by
    have htail : Antitone (fun t : ℝ => μ {x | 2*t < ‖T i (hf₂.toLp f) x‖}) := by
      intro t s hts
      apply measure_mono
      intro x hx
      exact (mul_le_mul_of_nonneg_left hts (by norm_num)).trans_lt hx
    exact htail.measurable.mul (by fun_prop)
  have layer (i : ι) :
      (∫⁻ x, ‖T i (hf₂.toLp f) x‖ₑ^(3:ℕ) ∂μ) = 24 * ∫⁻ t in Ioi (0:ℝ), D i t :=
    cube_moment_eq_halfNorm_layer _ (Lp.aestronglyMeasurable _)
  simp_rw [layer]
  rw [← Finset.mul_sum,← lintegral_finset_sum Finset.univ (fun i _ => hDm i)]
  have ih : (∫⁻ t in Ioi (0:ℝ), H t) = ENNReal.ofReal k * ∫⁻ x, ‖f x‖ₑ^(3:ℕ) ∂μ := by
    simpa only [H,g,ofReal_norm_eq_enorm] using integrated_upper_square_at_scaled_height (μ := μ) g hg hk
  have il : (∫⁻ t in Ioi (0:ℝ), L t) =
      ENNReal.ofReal (k^(3-q)/(q-3)) * ∫⁻ x, ‖f x‖ₑ^(3:ℕ) ∂μ := by
    simpa only [L,g,ofReal_norm_eq_enorm] using
      integrated_lower_power_at_scaled_height (μ := μ) g hg (fun x => norm_nonneg (f x)) hk hq
  have levels :
      (∫⁻ t in Ioi (0:ℝ), ∑ i, D i t) ≤
        ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal A * H t + ENNReal.ofReal B * L t := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
    exact cap_level_split hq T U hTU hA hB sqBound qBound f hfm hf₂ hfq k ht
  rw [lintegral_add_left (measurable_const.mul hHm),lintegral_const_mul _ hHm,
    lintegral_const_mul _ hLm,ih,il] at levels
  exact (mul_le_mul_left' levels 24).trans_eq (by rw [mul_assoc (24 : ℝ≥0∞),add_mul]; ac_rfl)

end Burnett.Analysis.CapFourier
