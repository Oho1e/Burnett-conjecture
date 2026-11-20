import Burnett.Analysis.CubicEnergy.FrequencySplit
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualDensity
import Burnett.Analysis.SignedFourierWindow.KernelDualPower

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section

namespace Burnett.A02.FrequencySplit.CMBilinearDual
open Burnett.Analysis.SignedFourierWindow

open MeasureTheory Metric Set Filter
open scoped ComplexConjugate ENNReal Topology

private theorem norming_power {p q : ℝ} (hpq : p.HolderConjugate q) {u : E → ℂ}
    (hu : MemLp u (ENNReal.ofReal p) volume) :
    let h := kernelDualPower p u
    MemLp h (ENNReal.ofReal q) volume ∧
      eLpNorm h (ENNReal.ofReal q) volume = (eLpNorm u (ENNReal.ofReal p) volume) ^ (p - 1) ∧
      ‖∫ x, u x * h x‖ₑ = (eLpNorm u (ENNReal.ofReal p) volume) ^ p := by
  intro h
  have hpm := hpq.sub_one_pos
  have hm : AEStronglyMeasurable h volume :=
    (Complex.continuous_conj.comp_aestronglyMeasurable hu.1).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (hu.1.norm.aemeasurable.pow_const (p - 2)).aestronglyMeasurable)
  have hn (x : E) : ‖h x‖ = ‖u x‖ ^ (p - 1) := by
    change ‖conj (u x) * ((‖u x‖ ^ (p - 2) : ℝ) : ℂ)‖ = _
    rw [norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), mul_comm,
      ← Real.rpow_add_one' (norm_nonneg _) (show p - 2 + 1 ≠ 0 by linarith)]
    congr 1
    ring
  have ev : eLpNorm h (ENNReal.ofReal q) volume =
      (eLpNorm u (ENNReal.ofReal p) volume) ^ (p - 1) := by
    calc
      _ = eLpNorm (fun x => ‖u x‖ ^ (p - 1)) (ENNReal.ofReal q) volume := by
        apply eLpNorm_congr_norm_ae
        filter_upwards with x
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact hn x
      _ = _ := by
        rw [eLpNorm_norm_rpow u hpm, ← ENNReal.ofReal_mul hpq.symm.pos.le,
          mul_comm q, hpq.sub_one_mul_conj]
  refine ⟨⟨hm, ev.trans_lt (ENNReal.rpow_lt_top_of_nonneg hpm.le hu.2.ne)⟩, ev, ?_⟩
  have product (x : E) : u x * h x = ((‖u x‖ ^ p : ℝ) : ℂ) := by
    change u x * (conj (u x) * ((‖u x‖ ^ (p - 2) : ℝ) : ℂ)) = _
    rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
    congr 1
    have rpow := Real.rpow_add' (x := ‖u x‖) (y := 2) (z := p - 2) (norm_nonneg _)
      (show 2 + (p - 2) ≠ 0 by linarith [hpq.pos])
    rw [Real.rpow_two, show 2 + (p - 2) = p by ring] at rpow
    exact rpow.symm
  have pint : Integrable (fun x => ‖u x‖ ^ p) := by
    simpa only [ENNReal.toReal_ofReal hpq.pos.le] using
      hu.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hpq.pos).ne' ENNReal.ofReal_ne_top
  have rpow_nonneg (x : E) : 0 ≤ ‖u x‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  have intEq : (∫ x, u x * h x) = ((∫ x, ‖u x‖ ^ p : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall product)
  have normEq := eLpNorm_norm_rpow (μ := (volume : Measure E)) (p := (1 : ℝ≥0∞)) u hpq.pos
  rw [one_mul, eLpNorm_one_eq_lintegral_enorm] at normEq
  rw [intEq, ← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg rpow_nonneg),
    ofReal_integral_eq_lintegral_ofReal pint (Eventually.of_forall rpow_nonneg)]
  exact (lintegral_congr fun x => by
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (rpow_nonneg x)]).trans normEq

private def lpBilinearTest (P Q : ℝ≥0∞) [Fact (1 ≤ Q)] [ENNReal.HolderConjugate P Q]
    {u : E → ℂ} (hu : MemLp u P volume) : Lp ℂ Q (volume : Measure E) →L[ℂ] ℂ :=
  let pair : Lp ℂ Q (volume : Measure E) →ₗ[ℂ] ℂ :=
    { toFun := fun h => ∫ x, u x * h x
      map_add' := by
        intro a b
        change (∫ x, u x * (a + b) x) = (∫ x, u x * a x) + ∫ x, u x * b x
        have ia : Integrable (fun x => u x * a x) := hu.integrable_mul (Lp.memLp a)
        have ib : Integrable (fun x => u x * b x) := hu.integrable_mul (Lp.memLp b)
        rw [← integral_add ia ib]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add a b] with x hx
        simp only [hx, Pi.add_apply, mul_add]
      map_smul' := by
        intro c a
        change (∫ x, u x * (c • a) x) = c * ∫ x, u x * a x
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c a] with x hx
        simp only [hx, Pi.smul_apply, smul_eq_mul]
        ring }
  pair.mkContinuous (eLpNorm u P volume).toReal (by
    intro h
    change ‖∫ x, u x * h x‖ ≤ (eLpNorm u P volume).toReal * ‖h‖
    have hB : ‖∫ x, u x * h x‖ₑ ≤ eLpNorm u P volume * eLpNorm (h : E → ℂ) Q volume := by
      calc
        _ ≤ ∫⁻ x, ‖u x * h x‖ₑ := enorm_integral_le_lintegral_enorm _
        _ = eLpNorm (u • (h : E → ℂ)) 1 volume := eLpNorm_one_eq_lintegral_enorm.symm
        _ ≤ _ := eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable h) hu.1
    rw [← Lp.enorm_def] at hB
    exact (by simpa only [toReal_enorm, ENNReal.toReal_mul] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top hu.2.ne enorm_ne_top) hB))

/-- A bound on Schwartz pairings of an Lᵖ function controls its full Lᵖ norm
with the same constant. The pairing is complex bilinear. -/
theorem eLpNorm_le_of_schwartz_pairing {p q : ℝ} (hpq : p.HolderConjugate q)
    {u : E → ℂ} (hu : MemLp u (ENNReal.ofReal p) volume) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (tests : ∀ h : SchwartzMap E ℂ, ‖∫ x, u x * h x‖ₑ ≤
      C * eLpNorm (h : E → ℂ) (ENNReal.ofReal q) volume) :
    eLpNorm u (ENNReal.ofReal p) volume ≤ C := by
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal q
  letI : Fact (1 ≤ Q) := ⟨by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hpq.symm.lt.le⟩
  letI : ENNReal.HolderConjugate P Q := hpq.ennrealOfReal
  let pair := lpBilinearTest P Q hu
  have agree (h : E → ℂ) (hh : MemLp h Q volume) :
      pair (hh.toLp h) = ∫ x, u x * h x := by
    change (∫ x, u x * hh.toLp h x) = ∫ x, u x * h x
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp] with x hx
    rw [hx]
  have bound (h : Lp ℂ Q (volume : Measure E)) : ‖pair h‖ ≤ C.toReal * ‖h‖ := by
    have dense := schwartz_toLp_denseRange (V := E) Q ENNReal.ofReal_ne_top
    apply dense.induction_on (p := fun a => ‖pair a‖ ≤ C.toReal * ‖a‖) h
    · exact isClosed_le pair.continuous.norm (continuous_const.mul continuous_norm)
    · intro g
      have eq : pair (g.toLp Q volume) = ∫ x, u x * g x :=
        agree (g : E → ℂ) (g.memLp Q volume)
      rw [eq, SchwartzMap.norm_toLp]
      simpa only [toReal_enorm, ENNReal.toReal_mul] using
        ENNReal.toReal_mono (ENNReal.mul_ne_top hC (g.memLp Q volume).2.ne) (tests g)
  let h := kernelDualPower p u
  let N := eLpNorm u P volume
  obtain ⟨hh, hnorm, hpair⟩ := norming_power hpq hu
  have bnd := bound (hh.toLp h)
  rw [agree h hh, Lp.norm_toLp] at bnd
  have bndₑ : ‖∫ x, u x * h x‖ₑ ≤ C * eLpNorm h Q volume := by
    apply (ENNReal.toReal_le_toReal enorm_ne_top (ENNReal.mul_ne_top hC hh.2.ne)).mp
    simpa only [toReal_enorm, ENNReal.toReal_mul] using bnd
  have moment : N ^ p ≤ C * N ^ (p - 1) := hpair.symm.le.trans (bndₑ.trans_eq (congrArg (C * ·) hnorm))
  change N ≤ C
  by_cases hz : N = 0
  · rw [hz]
    exact zero_le _
  have hpm := hpq.sub_one_pos
  have positive := ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hz) hpm.le
  have finite := ENNReal.rpow_lt_top_of_nonneg hpm.le hu.2.ne
  apply (ENNReal.mul_le_mul_right positive.ne' finite.ne).mp
  have split : N * N ^ (p - 1) = N ^ p := by
    have e := ENNReal.rpow_add_of_nonneg (x := N) 1 (p - 1) (by norm_num) hpm.le
    rw [ENNReal.rpow_one, show 1 + (p - 1) = p by ring] at e
    exact e.symm
  exact split.le.trans moment

/-- Local Lᵖ membership and a uniform bound on compactly supported Schwartz
tests imply the global bound for the actual function. -/
theorem memLp_of_compact_schwartz_pairing {p q : ℝ} (hpq : p.HolderConjugate q)
    {u : E → ℂ} (hu : ∀ n : ℕ, MemLp u (ENNReal.ofReal p) ((volume : Measure E).restrict (closedBall 0 n)))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (tests : ∀ h : SchwartzMap E ℂ, HasCompactSupport (h : E → ℂ) →
      ‖∫ x, u x * h x‖ₑ ≤ C * eLpNorm (h : E → ℂ) (ENNReal.ofReal q) volume) :
    MemLp u (ENNReal.ofReal p) volume ∧ eLpNorm u (ENNReal.ofReal p) volume ≤ C := by
  let P := ENNReal.ofReal p
  let b (n : ℕ) : ContDiffBump (0 : E) :=
    ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  let ψ (n : ℕ) := schwartzBump (b n)
  let w (n : ℕ) : E → ℂ := fun x => u x * ψ n x
  have bound_one (n : ℕ) (x : E) : ‖ψ n x‖ ≤ 1 := by
    rw [schwartzBump_apply, Complex.norm_real, Real.norm_of_nonneg (b n).nonneg]
    exact (b n).le_one
  have loc (n : ℕ) : MemLp (w n) P volume := by
    let S := closedBall (0 : E) (↑(n + 2 : ℕ) : ℝ)
    have hi : MemLp (S.indicator u) P volume :=
      (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (hu (n + 2))
    have hm : MemLp (fun x => S.indicator u x * ψ n x) P volume :=
      ((ψ n).memLp_top volume).mul' hi
    apply hm.ae_eq
    filter_upwards with x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
    · have hdist : (b n).rOut ≤ dist x 0 := by
        change (n : ℝ) + 2 ≤ dist x 0
        exact (lt_of_not_ge (by
          simpa only [S, mem_closedBall, Nat.cast_add, Nat.cast_ofNat] using hx)).le
      have hz : ψ n x = 0 := by
        rw [schwartzBump_apply, (b n).zero_of_le_dist hdist, Complex.ofReal_zero]
      simp only [w, hz, mul_zero]
  have uniform (n : ℕ) : eLpNorm (w n) P volume ≤ C := by
    apply eLpNorm_le_of_schwartz_pairing hpq (loc n) hC
    intro h
    let g := SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (ψ n).hasTemperateGrowth h
    have hψ : HasCompactSupport (ψ n : E → ℂ) := by
      change HasCompactSupport (fun x : E => (b n x : ℂ))
      exact (b n).hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero
    have hg : HasCompactSupport (g : E → ℂ) := by
      change HasCompactSupport ((h : E → ℂ) * (ψ n : E → ℂ))
      exact hψ.mul_left
    have hnorm : eLpNorm (g : E → ℂ) (ENNReal.ofReal q) volume ≤
        eLpNorm (h : E → ℂ) (ENNReal.ofReal q) volume := by
      apply eLpNorm_mono
      intro x
      change ‖h x * ψ n x‖ ≤ ‖h x‖
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (bound_one n x)
    have hpair : (∫ x, w n x * h x) = ∫ x, u x * g x := by
      apply integral_congr_ae
      filter_upwards with x
      change u x * ψ n x * h x = u x * (h x * ψ n x)
      ring
    rw [hpair]
    exact (tests g hg).trans (mul_le_mul_left' hnorm C)
  have lim : ∀ᵐ x ∂(volume : Measure E), Tendsto (fun n => w n x) atTop (𝓝 (u x)) := by
    filter_upwards with x
    obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    have hcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hin : x ∈ closedBall 0 (b n).rIn := mem_closedBall_iff_norm.mpr (by
      simp only [sub_zero]
      change ‖x‖ ≤ (n : ℝ) + 1
      linarith)
    simp only [w, ψ, schwartzBump_apply, (b n).one_of_mem_closedBall hin, Complex.ofReal_one, mul_one]
  have est : eLpNorm u P volume ≤ C :=
    (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (loc n).1) u lim).trans
      ((liminf_le_liminf (Eventually.of_forall uniform)).trans_eq (liminf_const _))
  exact ⟨⟨aestronglyMeasurable_of_tendsto_ae atTop (fun n => (loc n).1) lim,
    est.trans_lt hC.lt_top⟩, est⟩

/-- The pairing-to-norm bridge for an actual continuous output, including
outputs for which only local integrability is known beforehand. -/
theorem memLp_of_schwartz_pairing {p q : ℝ} (hpq : p.HolderConjugate q)
    {u : E → ℂ} (hu : Continuous u) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (tests : ∀ h : SchwartzMap E ℂ,
      ‖∫ x, u x * h x‖ₑ ≤ C * eLpNorm (h : E → ℂ) (ENNReal.ofReal q) volume) :
    MemLp u (ENNReal.ofReal p) volume ∧ eLpNorm u (ENNReal.ofReal p) volume ≤ C := by
  apply memLp_of_compact_schwartz_pairing hpq (fun n => ?_) hC (fun h _ => tests h)
  let S := closedBall (0 : E) (n : ℝ)
  obtain ⟨M, hM⟩ : BddAbove ((fun x => ‖u x‖) '' S) :=
    (isCompact_closedBall (0 : E) (n : ℝ)).bddAbove_image hu.norm.continuousOn
  letI : IsFiniteMeasure ((volume : Measure E).restrict S) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  have htop : MemLp u ⊤ ((volume : Measure E).restrict S) :=
    memLp_top_of_bound hu.aestronglyMeasurable M
      ((ae_restrict_mem measurableSet_closedBall).mono fun x hx => hM (mem_image_of_mem _ hx))
  exact htop.mono_exponent le_top

end Burnett.A02.FrequencySplit.CMBilinearDual
