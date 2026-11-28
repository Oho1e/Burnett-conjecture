import Burnett.Analysis.CubicEnergy.AngularCorrection.LipschitzWeakDivergenceForm

set_option autoImplicit false
set_option maxHeartbeats 9500000

noncomputable section

namespace Burnett.A08

open Filter MeasureTheory Burnett.A06 Burnett.A07 Burnett.A02.FrequencySplit Burnett.Fourier
open scoped ComplexConjugate ENNReal NNReal Topology

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ
private abbrev LP2 := FirstOrderLp 2

open private inner_coefficientCommutatorOutput
  from Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalWeakDivergenceCommutator
open private realSchwartzRoughOutput_pair
  from Burnett.Analysis.CubicEnergy.AngularCorrection.CorrectionGlobalRoughOutputs

private theorem coefficientProductInner_integral (d : BoundedSymbol E) (v : Test) (y : LP2) :
    inner ℂ (symbolCLM d (v.toLp 2 volume)) y = ∫ x, conj (d x * v x) * y x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [symbolL2_ae d (v.toLp 2 volume), v.coeFn_toLp 2 volume] with x h₁ h₂
  change inner ℂ (symbolL2 d (v.toLp 2 volume) x) (y x) = _
  rw [h₁, h₂, RCLike.inner_apply']

private theorem schwartzProductInner_integral (d : SchwartzMap E ℝ) (v : Test) (y : LP2) :
    inner ℂ ((realSchwartzMultiply d v).toLp 2 volume) y =
      ∫ x, conj ((d x : ℂ) * v x) * y x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(realSchwartzMultiply d v).coeFn_toLp 2 volume] with x hx
  rw [hx, realSchwartzMultiply_apply, RCLike.inner_apply']

private theorem coefficientProductInner_tendsto
    (D : ℕ → SchwartzMap E ℝ) (d : E → ℝ) (L : ℝ≥0)
    (hLip : ∀ n, LipschitzWith L (D n)) (hzero : ∀ n, D n 0 = 0)
    (hlim : ∀ x, Tendsto (fun n => D n x) atTop (𝓝 (d x)))
    (dL2 : BoundedSymbol E) (hRep : ∀ x, dL2 x = (d x : ℂ)) (v : Test) (y : LP2) :
    Tendsto (fun n => inner ℂ ((realSchwartzMultiply (D n) v).toLp 2 volume) y) atTop
      (𝓝 (inner ℂ (symbolCLM dL2 (v.toLp 2 volume)) y)) := by
  simp only [schwartzProductInner_integral, coefficientProductInner_integral, hRep]
  let S : ℝ := SchwartzMap.seminorm ℝ 0 0 v
  let W (x : E) := ((L : ℝ)^2 * S) * (‖x‖^2 * ‖v x‖) + ‖y x‖^2
  have hy : Integrable (fun x : E => ‖y x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable y)).mp (Lp.memLp y)
  have hW : Integrable W := ((v.integrable_pow_mul volume 2).const_mul ((L : ℝ)^2 * S)).add hy
  refine tendsto_integral_of_dominated_convergence W ?_ hW ?_ ?_
  · intro n
    have h : Continuous (fun x => conj ((D n x : ℂ) * v x)) :=
      Complex.continuous_conj.comp ((Complex.continuous_ofReal.comp (D n).continuous).mul v.continuous)
    exact h.aestronglyMeasurable.mul (Lp.aestronglyMeasurable y)
  · intro n
    filter_upwards with x
    have hD : |D n x| ≤ (L : ℝ) * ‖x‖ := by
      simpa only [hzero n, sub_zero, Real.norm_eq_abs] using (hLip n).norm_sub_le x 0
    have hv : ‖v x‖ ^ 2 ≤ S * ‖v x‖ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (v.norm_le_seminorm ℝ x) (norm_nonneg _)
    calc
      ‖conj ((D n x : ℂ) * v x) * y x‖ = |D n x| * ‖v x‖ * ‖y x‖ := by
        rw [norm_mul, Complex.norm_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ((L : ℝ)*‖x‖*‖v x‖) * ‖y x‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD (norm_nonneg _)) (norm_nonneg _)
      _ ≤ ((L : ℝ)*‖x‖*‖v x‖)^2 + ‖y x‖^2 := by
        nlinarith [sq_nonneg (((L : ℝ)*‖x‖*‖v x‖) - ‖y x‖)]
      _ = ((L : ℝ)^2 * ‖x‖^2) * ‖v x‖^2 + ‖y x‖^2 := by ring
      _ ≤ W x := by
        refine add_le_add_right ((mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq ?_) _
        dsimp only [W]
        ring
  · filter_upwards with x
    have h₁ := (Complex.continuous_ofReal.continuousAt.tendsto.comp (hlim x)).mul
      (tendsto_const_nhds (x := v x))
    have h₂ := Complex.continuous_conj.continuousAt.tendsto.comp h₁
    exact h₂.mul (tendsto_const_nhds (x := y x))

private theorem coefficientProduct_sub_const (d d₀ : BoundedSymbol E) (r : ℝ)
    (hRep : ∀ x, d₀ x = d x - (r : ℂ)) (v : LP2) :
    symbolCLM d₀ v = symbolCLM d v - (r : ℂ) • v := by
  change symbolL2 d₀ v = symbolL2 d v - (r : ℂ) • v
  apply Lp.ext
  filter_upwards [symbolL2_ae d₀ v, symbolL2_ae d v,
    Lp.coeFn_sub (symbolL2 d v) ((r : ℂ) • v), Lp.coeFn_smul (r : ℂ) v] with x h₁ h₂ h₃ h₄
  rw [h₁, h₃]
  simp only [Pi.sub_apply, h₂, h₄, Pi.smul_apply, smul_eq_mul, hRep, sub_mul]

/-- The true coefficient commutator tested with the actual high adjoint.
Multiplication of the Schwartz vectors is taken in L². -/
def boundedCoefficientCorrectionCommutatorPair {b : Joint → ℂ} {C : ℝ}
    (P : OriginalAnalyticCorrectionBounds b C) (d : BoundedSymbol E) (H v w : Test) : ℂ :=
  inner ℂ (symbolCLM d (w.toLp 2 volume)) (P.forward H v) -
  inner ℂ (P.adjoint H w) (symbolCLM d (v.toLp 2 volume))

/-- The commutator used in the weak divergence is the actual Fourier
distribution of the global real Lipschitz coefficient. -/
theorem boundedCoefficientCorrectionCommutatorPair_fourier {a : Joint → ℂ} {C : ℝ}
    (P : OriginalAnalyticCorrectionBounds a C)
    (b : Joint → ℂ) (hb : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (hsize : ∀ p, ‖b p‖ ≤ B * (1 + ‖p.1‖ + ‖p.2‖)) (hRep : b =ᵐ[volume] a)
    (d : E → ℝ) (L : ℝ≥0) (hd : LipschitzWith L d)
    (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ x, |d x| ≤ D)
    (H v w : Test) :
    boundedCoefficientCorrectionCommutatorPair P
      (boundedRealCoefficient d D hD hd.continuous.measurable hbound) H v w =
        -radianHighCommutatorPair a d H v w := by
  obtain ⟨K,_,approx⟩ := exists_realSchwartz_normalized_Lipschitz_approximation
  obtain ⟨Dseq,hzero,hLip,hlim⟩ := approx d L hd
  let h (x : E) := d x - d 0
  have hh (x : E) : |h x| ≤ 2*D := by
    have q : |d x - d 0| ≤ |d x| + |d 0| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (d x) (d 0)
    exact q.trans (by linarith [hbound x, hbound 0])
  let dL2 := boundedRealCoefficient d D hD hd.continuous.measurable hbound
  let d₀ := boundedRealCoefficient h (2*D) (by positivity)
    (hd.continuous.measurable.sub measurable_const) hh
  have shifted (x : E) : d₀ x = dL2 x - (d 0 : ℂ) := Complex.ofReal_sub _ _
  have Llim := coefficientProductInner_tendsto Dseq h (K*L) hLip hzero hlim d₀ (fun _ => rfl)
    w (P.forward H v)
  have Rlim : Tendsto (fun n => inner ℂ (P.adjoint H w) ((realSchwartzMultiply (Dseq n) v).toLp 2 volume))
      atTop (𝓝 (inner ℂ (P.adjoint H w) (symbolCLM d₀ (v.toLp 2 volume)))) := by
    have h' := coefficientProductInner_tendsto Dseq h (K*L) hLip hzero hlim d₀ (fun _ => rfl)
      v (P.adjoint H w)
    have h'' : Tendsto (fun n => conj (inner ℂ ((realSchwartzMultiply (Dseq n) v).toLp 2 volume)
        (P.adjoint H w))) atTop
        (𝓝 (conj (inner ℂ (symbolCLM d₀ (v.toLp 2 volume)) (P.adjoint H w)))) :=
      Complex.continuous_conj.continuousAt.tendsto.comp h'
    simpa only [inner_conj_symm] using h''
  have hSchwartz (n : ℕ) :
      inner ℂ ((realSchwartzMultiply (Dseq n) w).toLp 2 volume) (P.forward H v) -
        inner ℂ (P.adjoint H w) ((realSchwartzMultiply (Dseq n) v).toLp 2 volume) =
      -radianHighCommutatorPair a (Dseq n) H v w := by
    rw [← P.adjoint_duality H (realSchwartzMultiply (Dseq n) v) w, ← inner_coefficientCommutatorOutput]
    exact realSchwartzRoughOutput_pair a H (P.forward H) (P.forward_pair H) (Dseq n) v w
  have hFourier := tendsto_radianHighCommutatorPair_normalizedCoefficient
    b hb B hB hsize (fun n x => Dseq n x) h (K*L) hLip hzero hlim H v w
  have normalized : radianHighCommutatorPair b h H v w = radianHighCommutatorPair b d H v w :=
    radianHighCommutatorPair_sub_value_at_zero b hb B hB hsize d L hd H v w
  rw [normalized] at hFourier
  have hlimPair : Tendsto (fun n => -radianHighCommutatorPair a (Dseq n) H v w)
      atTop (𝓝 (-radianHighCommutatorPair a d H v w)) := by
    simpa only [radianHighCommutatorPair_congr_ae_symbol hRep] using hFourier.neg
  have hId : boundedCoefficientCorrectionCommutatorPair P d₀ H v w =
      -radianHighCommutatorPair a d H v w :=
    tendsto_nhds_unique ((Llim.sub Rlim).congr hSchwartz) hlimPair
  have hConst : boundedCoefficientCorrectionCommutatorPair P d₀ H v w =
      boundedCoefficientCorrectionCommutatorPair P dL2 H v w := by
    unfold boundedCoefficientCorrectionCommutatorPair
    rw [coefficientProduct_sub_const dL2 d₀ (d 0) shifted,
      coefficientProduct_sub_const dL2 d₀ (d 0) shifted]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [P.adjoint_duality H v w]
    ring
  exact hConst.symm.trans hId

end Burnett.A08
