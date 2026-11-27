import Burnett.Analysis.PrincipalEnergy.Freezing.ParametricRadianBounds

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal FourierTransform

/-- The base Fourier frequency is \(\eta\), the input frequency is \(\xi\).
The left endpoint has \(\sigma=0\) and Weyl has \(\sigma=1/2\). -/
def slantedRadianSymbol (σ : ℝ) (b : E → ℝ) (q : E × E) : ℝ :=
  b (q.2 + tau • (σ • q.1))

def separatedRadianQuantization (σ : ℝ) (b : E → ℝ) (f u : SchwartzMap E ℂ) : E → ℂ :=
  radianFourierAverage (slantedRadianSymbol σ b) f u

theorem slanted_radian_symbol_measurable (σ : ℝ) (b : E → ℝ) (hb : Measurable b) :
    Measurable (slantedRadianSymbol σ b) := by
  have h : Continuous (fun q : E × E => q.2 + tau • (σ • q.1)) :=
    continuous_snd.add (continuous_const.smul (continuous_const.smul continuous_fst))
  exact hb.comp h.measurable

theorem slanted_radian_symbol_growth (σ : ℝ) (b : E → ℝ) (A : ℝ) (A0 : 0 ≤ A)
    (h : ∀ ξ, ‖b ξ‖ ≤ A * (1 + ‖ξ‖)) :
    RadianAverageGrowth (slantedRadianSymbol σ b) := by
  have τ0 : 0 ≤ tau := by unfold tau; positivity
  let B := 1 + tau + tau * ‖σ‖
  refine ⟨A * B, by unfold B; positivity, ?_⟩
  intro η ξ
  let W := (1 + ‖η‖) * (1 + ‖ξ‖)
  have w₁ : (1 : ℝ) ≤ W := by
    dsimp only [W]
    nlinarith only [norm_nonneg η, norm_nonneg ξ, mul_nonneg (norm_nonneg η) (norm_nonneg ξ)]
  have wη : ‖η‖ ≤ W := by
    dsimp only [W]
    nlinarith only [norm_nonneg η, norm_nonneg ξ, mul_nonneg (norm_nonneg η) (norm_nonneg ξ)]
  have wξ : ‖ξ‖ ≤ W := by
    dsimp only [W]
    nlinarith only [norm_nonneg η, norm_nonneg ξ, mul_nonneg (norm_nonneg η) (norm_nonneg ξ)]
  have sub : ‖tau • ξ + tau • (σ • η)‖ ≤ tau * ‖ξ‖ + tau * ‖σ‖ * ‖η‖ := by
    refine (norm_add_le _ _).trans_eq ?_
    simp only [norm_smul, Real.norm_of_nonneg τ0, mul_assoc]
  calc
    _ ≤ A * (1 + ‖tau • ξ + tau • (σ • η)‖) := h _
    _ ≤ A * (1 + tau * ‖ξ‖ + (tau * ‖σ‖) * ‖η‖) :=
      mul_le_mul_of_nonneg_left (by linarith only [sub]) A0
    _ ≤ A * (W + tau * W + (tau * ‖σ‖) * W) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add w₁ (mul_le_mul_of_nonneg_left wξ τ0))
          (mul_le_mul_of_nonneg_left wη (mul_nonneg τ0 (norm_nonneg _)))) A0
    _ = _ := by dsimp only [B, W]; ring

theorem separated_radian_quantization_left (b : E → ℝ) (hb : Measurable b)
    (grow : RadianAverageGrowth (slantedRadianSymbol 0 b)) (f u : SchwartzMap E ℂ) (x : E) :
    separatedRadianQuantization 0 b f u x = f x * radianAction b u x := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  have inv := congrFun (f.continuous.fourier_inversion f.integrable F.integrable) x
  rw [Real.fourierIntegralInv_eq'] at inv
  have fi : (∫ η, patchFourierPhase η x * 𝓕 (f : E → ℂ) η) = f x :=
    by simpa only [Burnett.Microlocal.Overlap.baseFourierPhase, tau, smul_eq_mul] using inv
  rw [separatedRadianQuantization, radian_fourier_average_eq_integral _ (slanted_radian_symbol_measurable _ _ hb) grow]
  simp only [slantedRadianSymbol, zero_smul, smul_zero, add_zero]
  rw [integral_mul_const, fi]

/-- The difference of the slanted and left quantizations, before the common
skew factor \(-i\). -/
def separatedRadianSlantRemainder (σ : ℝ) (b : E → ℝ) (f u : SchwartzMap E ℂ) : E → ℂ :=
  fun x => separatedRadianQuantization σ b f u x - f x * radianAction b u x

private theorem homogeneous_linear_bound (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (D : ℝ) (D0 : 0 ≤ D)
    (jet : ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ 1 b ξ‖ ≤ D) (ξ : E) :
    ‖b ξ‖ ≤ D * (1 + ‖ξ‖) := by
  have h := norm_symbol_shift_sub_le b hb hom D D0 jet ξ 0
  rw [zero_add, homogeneous_value_zero hom, sub_zero] at h
  exact h.trans (by nlinarith only [D0])

/-- For genuine Weyl half-shifts the constant is the same formula evaluated
at \(\sigma=1/2\). The derivative uses only a first derivative of the field. -/
theorem exists_separated_radian_slant_remainder_W13 :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 7 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (σ : ℝ) (f u : SchwartzMap E ℂ),
        let p := ENNReal.ofReal 3
        let R := separatedRadianSlantRemainder σ b f u
        MemLp R p volume ∧
          eLpNorm R p volume ≤ ENNReal.ofReal (K * ‖σ‖ * D * patchFourierMoment 1 f) *
            eLpNorm (u : E → ℂ) p volume ∧
          Differentiable ℝ R ∧
          ∀ j : Index, let d (x : E) := fderiv ℝ R x (EuclideanSpace.single j 1)
            MemLp d p volume ∧
            eLpNorm d p volume ≤
              ENNReal.ofReal (K * ‖σ‖ * D * patchFourierMoment 1 f) *
                eLpNorm (energyPartial j u : E → ℂ) p volume +
              ENNReal.ofReal (K * ‖σ‖ * D * patchFourierMoment 1 (energyPartial j f)) *
                eLpNorm (u : E → ℂ) p volume := by
  obtain ⟨K, K0, shift⟩ := exists_radian_shift_difference_L3_bound
  have τ0 : 0 ≤ tau := by unfold tau; positivity
  refine ⟨tau * K, mul_nonneg τ0 K0, ?_⟩
  intro b hb hom D D0 jet σ f u p R
  let a := slantedRadianSymbol σ b
  let c := slantedRadianSymbol 0 b
  let Δ (z : E × E) := a z - c z
  let B := tau * ‖σ‖ * D
  let W (η : E) := B * ‖η‖
  have bM := measurable_of_continuousOn_compl_singleton 0 hb.continuousOn
  have aM : Measurable a := slanted_radian_symbol_measurable σ b bM
  have cM : Measurable c := slanted_radian_symbol_measurable 0 b bM
  have deltaM : Measurable Δ := aM.sub cM
  have j1 := jet 1 (by decide)
  have ga : RadianAverageGrowth a := slanted_radian_symbol_growth σ b D D0
    (homogeneous_linear_bound b hb hom D D0 j1)
  have gc : RadianAverageGrowth c := slanted_radian_symbol_growth 0 b D D0
    (homogeneous_linear_bound b hb hom D D0 j1)
  have B0 : 0 ≤ B := mul_nonneg (mul_nonneg τ0 (norm_nonneg _)) D0
  have W0 (η : E) : 0 ≤ W η := mul_nonneg B0 (norm_nonneg _)
  have size (η : E) : ‖tau • (σ • η)‖ * D = W η := by
    simp only [W, B, norm_smul, Real.norm_of_nonneg τ0]
    ring
  have delta (η ξ : E) : Δ (η, ξ) = b (ξ + tau • (σ • η)) - b ξ := by
    simp only [Δ, a, c, slantedRadianSymbol, zero_smul, smul_zero, add_zero]
  have point (η ξ : E) : ‖Δ (η, ξ)‖ ≤ W η := by
    rw [delta, ← size]
    exact norm_symbol_shift_sub_le b hb hom D D0 j1 _ ξ
  have gd : RadianAverageGrowth Δ := by
    refine ⟨B, B0, fun η ξ => (point η _).trans ?_⟩
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) B0).trans
      (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (norm_nonneg _)))
  have exactR (g v : SchwartzMap E ℂ) :
      separatedRadianSlantRemainder σ b g v = radianFourierAverage Δ g v := by
    rw [radian_fourier_average_sub a c aM cM ga gc]
    funext x
    simp only [separatedRadianSlantRemainder, Pi.sub_apply, a]
    rw [← separated_radian_quantization_left b bM gc g v x]
    rfl
  have value (g v : SchwartzMap E ℂ) :
      MemLp (separatedRadianSlantRemainder σ b g v) p volume ∧
        eLpNorm (separatedRadianSlantRemainder σ b g v) p volume ≤
          ENNReal.ofReal ((tau * K) * ‖σ‖ * D * patchFourierMoment 1 g) * eLpNorm (v : E → ℂ) p volume := by
    let U := SchwartzMap.fourierTransformCLM ℂ g
    have int : Integrable (fun η => W η * ‖𝓕 (g : E → ℂ) η‖) := by
      simpa only [W, pow_one, mul_assoc] using (U.integrable_pow_mul volume 1).const_mul B
    have sec (η : E) :
        let w := radianAction (fun ξ => Δ (η, ξ)) v
        MemLp w p volume ∧ eLpNorm w p volume ≤ ENNReal.ofReal (W η) *
          (ENNReal.ofReal K * eLpNorm (v : E → ℂ) p volume) := by
      simp_rw [delta η]
      have h := shift b hb hom D D0 jet (tau • (σ • η)) v
      dsimp only at h
      rw [size, ENNReal.ofReal_mul K0, mul_assoc, ← mul_left_comm] at h
      exact h
    have Vfin := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (v.memLp p volume).eLpNorm_lt_top
      (a := ENNReal.ofReal K)
    have h := radian_fourier_average_L3_bound Δ deltaM gd g v W W0 point int _ Vfin sec
    rw [exactR]
    refine ⟨h.1, h.2.trans_eq ?_⟩
    have intEq : (∫ η, W η * ‖𝓕 (g : E → ℂ) η‖) = B * patchFourierMoment 1 g := by
      simp only [W, patchFourierMoment, pow_one, mul_assoc, integral_const_mul]
    have m0 : 0 ≤ B * patchFourierMoment 1 g :=
      mul_nonneg B0 (integral_nonneg fun _ => mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))
    rw [intEq, ← mul_assoc, ← ENNReal.ofReal_mul m0]
    congr 2
    dsimp only [B]
    ring
  refine ⟨(value f u).1, (value f u).2, ?_, ?_⟩
  · intro x
    dsimp only [R]
    rw [exactR]
    exact (radian_fourier_average_coordinate Δ deltaM gd f u 0 x).1
  · intro j d
    have eq : d = separatedRadianSlantRemainder σ b (energyPartial j f) u +
        separatedRadianSlantRemainder σ b f (energyPartial j u) := by
      funext x
      dsimp only [d, R, Pi.add_apply]
      simp_rw [exactR]
      exact (radian_fourier_average_coordinate Δ deltaM gd f u j x).2
    rw [eq]
    have A := value (energyPartial j f) u
    have B' := value f (energyPartial j u)
    refine ⟨A.1.add B'.1, (eLpNorm_add_le A.1.1 B'.1.1 (by norm_num [p])).trans ?_⟩
    exact (add_le_add A.2 B'.2).trans_eq (add_comm _ _)

end Burnett.A03
