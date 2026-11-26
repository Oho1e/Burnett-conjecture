import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotAdjoint

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.A06

open MeasureTheory Filter
open Burnett.A02.FrequencySplit (E Joint radianFourier radianFourier_scaled tau)
open scoped ComplexConjugate RealInnerProductSpace FourierTransform

private theorem tau_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

private def radianSchwartzSpectrum (u : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  let r := Units.mk0 (tau⁻¹) (inv_ne_zero tau_pos.ne')
  let scale : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (G := ℝˣ) r
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scale (SchwartzMap.fourierTransformCLM ℂ u)

private theorem radianSchwartzSpectrum_apply (u : SchwartzMap E ℂ) (p : E) :
    radianSchwartzSpectrum u p = radianFourier u p := by
  have hp : tau • (tau⁻¹ • p) = p := by rw [smul_smul, mul_inv_cancel₀ tau_pos.ne', one_smul]
  change (𝓕 (u : E → ℂ)) (tau⁻¹ • p) = radianFourier u p
  rw [← radianFourier_scaled, hp]

private theorem measurable_radianFourier {u : E → ℂ} (hu : Measurable u) :
    Measurable (radianFourier u) := by
  have hp : Measurable (fun p : E × E =>
      Complex.exp ((- (inner ℝ p.1 p.2 : ℝ) : ℂ) * Complex.I) * u p.1) := by
    refine Measurable.mul ?_ (hu.comp measurable_fst)
    fun_prop
  exact hp.stronglyMeasurable.integral_prod_left'.measurable

private theorem weightedSpectrum_integrable (u : SchwartzMap E ℂ) :
    Integrable (fun p : E => (1 + ‖p‖) * ‖radianFourier u p‖) := by
  let v := radianSchwartzSpectrum u
  have he : (fun p : E => (1 + ‖p‖) * ‖radianFourier u p‖) =
      fun p : E => ‖v p‖ + ‖p‖ * ‖v p‖ := by
    funext p
    rw [radianSchwartzSpectrum_apply, add_mul, one_mul]
  rw [he]
  exact v.integrable.norm.add (by simpa only [pow_one] using v.integrable_pow_mul volume 1)

private def weightedSpaceMass (u : SchwartzMap E ℂ) : ℝ :=
  ∫ x : E, ‖x‖ * ‖u x‖

private def weightedSpectrumMass (u : SchwartzMap E ℂ) : ℝ :=
  ∫ p : E, (1 + ‖p‖) * ‖radianFourier u p‖

private theorem weightedSpaceMass_nonneg (u : SchwartzMap E ℂ) : 0 ≤ weightedSpaceMass u :=
  integral_nonneg fun _ => by positivity

private theorem weightedSpectrumMass_nonneg (u : SchwartzMap E ℂ) :
    0 ≤ weightedSpectrumMass u :=
  integral_nonneg fun _ => by positivity

private theorem norm_radianFourier_lipschitz_schwartz
    {d : E → ℝ} {L : NNReal} (hd : LipschitzWith L d) (hd0 : d 0 = 0)
    (u : SchwartzMap E ℂ) (p : E) :
    ‖radianFourier (fun x => (d x : ℂ) * u x) p‖ ≤ (L : ℝ) * weightedSpaceMass u := by
  have hI : Integrable (fun x : E => (L : ℝ) * (‖x‖ * ‖u x‖)) :=
    ((by simpa only [pow_one] using u.integrable_pow_mul volume 1 :
      Integrable (fun x : E => ‖x‖ * ‖u x‖))).const_mul _
  let w := fun x : E =>
    Complex.exp ((- (inner ℝ x p : ℝ) : ℂ) * Complex.I) * ((d x : ℂ) * u x)
  have hw : ∀ x : E, ‖w x‖ ≤ (L : ℝ) * (‖x‖ * ‖u x‖) := by
    intro x
    have h := hd.dist_le_mul x 0
    have hbound : ‖d x‖ ≤ (L : ℝ) * ‖x‖ := by simpa [dist_eq_norm, hd0] using h
    change ‖Complex.exp ((- (inner ℝ x p : ℝ) : ℂ) * Complex.I) * ((d x : ℂ) * u x)‖ ≤ _
    rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul,
      norm_mul, Complex.norm_real, ← mul_assoc]
    gcongr
  have hIm : Integrable w := hI.mono' (by
    unfold w
    have hc : Continuous (fun x : E => (d x : ℂ)) := Complex.continuous_ofReal.comp hd.continuous
    exact (show Continuous (fun x : E =>
      Complex.exp ((- (inner ℝ x p : ℝ) : ℂ) * Complex.I) * ((d x : ℂ) * u x)) by
      fun_prop).aestronglyMeasurable) (Eventually.of_forall hw)
  change ‖∫ x, w x‖ ≤ _
  calc
    _ ≤ ∫ x, ‖w x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : E, (L : ℝ) * (‖x‖ * ‖u x‖) := integral_mono hIm.norm hI hw
    _ = _ := integral_const_mul _ _

private theorem measurable_radianHighPairWeight (b : Joint → ℂ) (hb : Measurable b)
    (f g h : E → ℂ) (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable (radianHighPairWeight b f g h) :=
  ((hb.mul ((measurable_radianFourier hf).comp measurable_fst)).mul
    ((measurable_radianFourier hg).comp measurable_snd)).mul
    (Complex.continuous_conj.measurable.comp
      ((measurable_radianFourier hh).comp (measurable_snd.add measurable_fst)))

private theorem bound_jointIntegral
    (W : Joint → ℂ) (hW : Measurable W) (f g : SchwartzMap E ℂ) (D : ℝ)
    (hbound : ∀ x : Joint, ‖W x‖ ≤
      D * (((1 + ‖x.1‖) * ‖radianFourier f x.1‖) *
        ((1 + ‖x.2‖) * ‖radianFourier g x.2‖))) :
    Integrable W ∧ ‖∫ x, W x‖ ≤ D * (weightedSpectrumMass f * weightedSpectrumMass g) := by
  let F := fun p : E => (1 + ‖p‖) * ‖radianFourier f p‖
  let G := fun p : E => (1 + ‖p‖) * ‖radianFourier g p‖
  let M := fun x : Joint => D * (F x.1 * G x.2)
  have hM : Integrable M := by
    rw [Measure.volume_eq_prod E E]
    exact ((weightedSpectrum_integrable f).mul_prod (weightedSpectrum_integrable g)).const_mul D
  have hi : Integrable W := hM.mono' hW.aestronglyMeasurable (Eventually.of_forall hbound)
  refine ⟨hi, (norm_integral_le_integral_norm _).trans ((integral_mono hi.norm hM hbound).trans_eq ?_)⟩
  change (∫ x : Joint, D * (F x.1 * G x.2)) =
    D * ((∫ p : E, F p) * (∫ p : E, G p))
  rw [Measure.volume_eq_prod E E, integral_const_mul, integral_prod_mul]

private theorem unit_jointWeights_le (p q : E) :
    1 + ‖p‖ + ‖q‖ ≤ (1 + ‖p‖) * (1 + ‖q‖) := by
  nlinarith [mul_nonneg (norm_nonneg p) (norm_nonneg q)]

private theorem shifted_jointWeights_le (p q : E) :
    1 + ‖p‖ + ‖-p + q‖ ≤ 2 * ((1 + ‖p‖) * (1 + ‖q‖)) := by
  have h : ‖-p + q‖ ≤ ‖p‖ + ‖q‖ := by simpa using norm_add_le (-p) q
  nlinarith [mul_nonneg (norm_nonneg p) (norm_nonneg q), norm_nonneg q]

/-- On each fixed triple of Schwartz tests, the two exact high-slot Fourier
terms for a normalized real Lipschitz coefficient are absolutely integrable.
Their commutator pairing is bounded with one factor each of the size
seminorm of the translation-invariant symbol and the Lipschitz seminorm. -/
theorem exists_radianHighCommutatorPair_test_bound (f g h : SchwartzMap E ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : Joint → ℂ), Measurable b → ∀ (B : ℝ), 0 ≤ B →
      (∀ x : Joint, ‖b x‖ ≤ B * (1 + ‖x.1‖ + ‖x.2‖)) →
      ∀ (d : E → ℝ) (L : NNReal), LipschitzWith L d → d 0 = 0 →
      Integrable (radianHighPairWeight b f (fun x => (d x : ℂ) * g x) h) ∧
      Integrable (radianHighPairWeight b f g (fun x => (d x : ℂ) * h x)) ∧
      ‖radianHighCommutatorPair b d f g h‖ ≤ C * B * (L : ℝ) := by
  let μ : Measure E := volume
  let κ := (tau ^ 8)⁻¹
  have κ0 : 0 ≤ κ := by dsimp [κ]; positivity
  let D1 := 2 * weightedSpaceMass g * (weightedSpectrumMass f * weightedSpectrumMass h)
  let D2 := weightedSpaceMass h * (weightedSpectrumMass f * weightedSpectrumMass g)
  have D10 : 0 ≤ D1 := by
    dsimp [D1]
    exact mul_nonneg (mul_nonneg (by norm_num) (weightedSpaceMass_nonneg g))
      (mul_nonneg (weightedSpectrumMass_nonneg f) (weightedSpectrumMass_nonneg h))
  have D20 : 0 ≤ D2 := by
    dsimp [D2]
    exact mul_nonneg (weightedSpaceMass_nonneg h)
      (mul_nonneg (weightedSpectrumMass_nonneg f) (weightedSpectrumMass_nonneg g))
  refine ⟨κ * (D1 + D2), mul_nonneg κ0 (add_nonneg D10 D20), ?_⟩
  intro b hb B B0 hbB d L hd hd0
  let W1 := radianHighPairWeight b f (fun x => (d x : ℂ) * g x) h
  let W2 := radianHighPairWeight b f g (fun x => (d x : ℂ) * h x)
  have md : Measurable (fun x => (d x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hd.continuous.measurable
  have m1 : Measurable W1 :=
    measurable_radianHighPairWeight b hb _ _ _ f.continuous.measurable
      (md.mul g.continuous.measurable) h.continuous.measurable
  have m2 : Measurable W2 :=
    measurable_radianHighPairWeight b hb _ _ _ f.continuous.measurable
      g.continuous.measurable (md.mul h.continuous.measurable)
  let T : Joint ≃ᵐ Joint := (MeasurableEquiv.shearAddRight E).symm
  have hT : MeasurePreserving T (volume : Measure Joint) volume := by
    rw [Measure.volume_eq_prod E E]
    exact measurePreserving_prod_neg_add μ μ
  obtain ⟨h1i, h1b⟩ := bound_jointIntegral (W1 ∘ T) (m1.comp hT.measurable) f h
    (2 * B * (L : ℝ) * weightedSpaceMass g) (by
      intro ⟨p, q⟩
      have hcancel : (-p + q) + p = q := by abel
      change ‖b (p, -p + q) * radianFourier f p *
        radianFourier (fun x => (d x : ℂ) * g x) (-p + q) *
        conj (radianFourier h ((-p + q) + p))‖ ≤ _
      rw [hcancel]
      simp only [norm_mul, Complex.norm_conj]
      calc
        _ ≤ (B * (2 * ((1 + ‖p‖) * (1 + ‖q‖)))) * ‖radianFourier f p‖ *
            ((L : ℝ) * weightedSpaceMass g) * ‖radianFourier h q‖ := by
          gcongr
          · exact (hbB (p, -p + q)).trans
              (mul_le_mul_of_nonneg_left (shifted_jointWeights_le p q) B0)
          · exact norm_radianFourier_lipschitz_schwartz hd hd0 g _
        _ = _ := by ring)
  obtain ⟨h2i, h2b⟩ := bound_jointIntegral W2 m2 f g
    (B * (L : ℝ) * weightedSpaceMass h) (by
      intro ⟨p, q⟩
      change ‖b (p, q) * radianFourier f p * radianFourier g q *
        conj (radianFourier (fun x => (d x : ℂ) * h x) (q + p))‖ ≤ _
      simp only [norm_mul, Complex.norm_conj]
      calc
        _ ≤ (B * ((1 + ‖p‖) * (1 + ‖q‖))) * ‖radianFourier f p‖ * ‖radianFourier g q‖ *
            ((L : ℝ) * weightedSpaceMass h) := by
          gcongr
          · exact (hbB (p, q)).trans (mul_le_mul_of_nonneg_left (unit_jointWeights_le p q) B0)
          · exact norm_radianFourier_lipschitz_schwartz hd hd0 h _
        _ = _ := by ring)
  have h1 : Integrable W1 := (hT.integrable_comp_emb T.measurableEmbedding).mp h1i
  have eq : (∫ x, W1 (T x)) = ∫ x, W1 x := hT.integral_comp' W1
  change ‖∫ x, W1 (T x)‖ ≤ _ at h1b
  rw [eq] at h1b
  refine ⟨h1, h2i, ?_⟩
  change ‖κ • (∫ x, W1 x) - κ • (∫ x, W2 x)‖ ≤ _
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg κ0]
  calc
    _ ≤ κ * (‖∫ x, W1 x‖ + ‖∫ x, W2 x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) κ0
    _ ≤ κ * ((2 * B * (L : ℝ) * weightedSpaceMass g) *
          (weightedSpectrumMass f * weightedSpectrumMass h) +
        (B * (L : ℝ) * weightedSpaceMass h) *
          (weightedSpectrumMass f * weightedSpectrumMass g)) :=
      mul_le_mul_of_nonneg_left (add_le_add h1b h2b) κ0
    _ = _ := by dsimp [D1, D2]; ring

end Burnett.A06
