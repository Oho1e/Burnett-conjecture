import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianCommutatorAssembly
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualOuter

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Finset Burnett.RicciSymbol
open scoped ContDiff ENNReal FourierTransform RealInnerProductSpace

private theorem radian_commutator_continuous (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (f g : SchwartzMap E ℂ) :
    Continuous (radianCommutator b f g) := by
  let B : E → ℝ := fun x => b (tau • x)
  have ht : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have hB : ContDiffOn ℝ ∞ B {x | x ≠ 0} :=
    hb.comp (contDiff_const.smul contDiff_id).contDiffOn (fun _ hx => smul_ne_zero ht.ne' hx)
  have hHom : ∀ t : ℝ, 0 < t → ∀ x, B (t • x) = t * B x := by
    intro t h x
    change b (tau • (t • x)) = t * b (tau • x)
    rw [smul_comm tau t x, hom t h]
  have action (v : SchwartzMap E ℂ) : Continuous (radianAction b v) := by
    have hi : Integrable (radianActionSpectrum b v) := orderOne_spectrum_integrable B hB hHom v
    rw [← radianActionSpectrum_inverse]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (continuous_fst.inner continuous_snd).neg hi
  unfold radianCommutator
  exact (action _).sub (f.continuous.mul (action g))

private theorem derivative_component_bound (p : ℝ) (j : Index) (f : SchwartzMap E ℂ) :
    eLpNorm (mikhlinDerivative j f : E → ℂ) (ENNReal.ofReal p) volume ≤
      eLpNorm (fderiv ℝ (f : E → ℂ)) (ENNReal.ofReal p) volume := by
  apply eLpNorm_mono
  intro x
  change ‖(-Complex.I) • (fderiv ℝ (f : E → ℂ) x (EuclideanSpace.single j 1))‖ ≤ _
  simpa using (fderiv ℝ (f : E → ℂ) x).le_opNorm (EuclideanSpace.single j 1)

private theorem test_pairing_bound {r q : ℝ} (hrq : r.HolderConjugate q) {u : E → ℂ}
    (hu : MemLp u (ENNReal.ofReal r) volume) (h : SchwartzMap E ℂ) :
    ‖∫ x, u x * h x‖ₑ ≤
      eLpNorm u (ENNReal.ofReal r) volume * eLpNorm (h : E → ℂ) (ENNReal.ofReal q) volume := by
  letI : ENNReal.HolderConjugate (ENNReal.ofReal r) (ENNReal.ofReal q) := hrq.ennrealOfReal
  calc
    _ ≤ ∫⁻ x, ‖u x * h x‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (u • (h : E → ℂ)) 1 volume := eLpNorm_one_eq_lintegral_enorm.symm
    _ ≤ _ := eLpNorm_smul_le_mul_eLpNorm h.continuous.aestronglyMeasurable hu.1

/-- The paper's physical first-order commutator obeys the finite-exponent
gradient estimate for Schwartz inputs in the original Fourier normalization. -/
theorem radian_commutator_Lp_bound (p s r : ℝ) (hp : 1 < p) (hs : 1 < s) (hr : 1 < r)
    (he : r⁻¹ = p⁻¹ + s⁻¹) (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f g : SchwartzMap E ℂ,
      MemLp (radianCommutator b f g) (ENNReal.ofReal r) volume ∧
      eLpNorm (radianCommutator b f g) (ENNReal.ofReal r) volume ≤ C *
        (eLpNorm (fderiv ℝ (f : E → ℂ)) (ENNReal.ofReal p) volume *
          eLpNorm (g : E → ℂ) (ENNReal.ofReal s) volume) := by
  classical
  choose KL hKL low using fun j => joint_bilinear_bound p s r hp hs hr he _
    (paperLowSymbol_regular b hb hom j).1 (paperLowSymbol_regular b hb hom j).2
  choose KP hKP product using fun j => joint_spectral_bilinear_outer_bound p s r hp hs hr he _
    (paperProductSymbol_regular j).1 (paperProductSymbol_regular j).2 _
    (angularComponent_contDiffOn b hb j) (angularComponent_scale hom j)
  choose KN hKN input using fun j => joint_spectral_bilinear_bound p s r hp hs hr he _
    (paperInputSymbol_regular j).1 (paperInputSymbol_regular j).2
  choose KA hKA angular using fun j => homogeneous_multiplier_Schwartz_bound _
    (angularComponent_contDiffOn b hb j) (angularComponent_scale hom j) s hs
  obtain ⟨KR, hKR, radial⟩ := mikhlin_radial_gradient_bound p hp
  let Lc := ∑ j, KL j
  let Pc := ∑ j, KP j * KR
  let Nc := ∑ j, KN j * KR * KA j
  have hL : Lc < ⊤ := ENNReal.sum_lt_top.mpr (fun j _ => hKL j)
  have hP : Pc < ⊤ := ENNReal.sum_lt_top.mpr (fun j _ => ENNReal.mul_lt_top (hKP j) hKR)
  have hN : Nc < ⊤ := ENNReal.sum_lt_top.mpr
    (fun j _ => ENNReal.mul_lt_top (ENNReal.mul_lt_top (hKN j) hKR) (hKA j))
  have hC : Lc + Pc + Nc < ⊤ := ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr ⟨hL, hP⟩, hN⟩
  refine ⟨Lc + Pc + Nc, hC, fun f g => ?_⟩
  let F := radianActionSpectrum (fun z => ‖z‖) f
  let gHat := SchwartzMap.fourierTransformCLM ℂ g
  let G : E → ℂ := gHat
  let V (j : Index) := radianActionSpectrum (angularComponent b j) g
  let Grad := eLpNorm (fderiv ℝ (f : E → ℂ)) (ENNReal.ofReal p) volume
  let NormG := eLpNorm (g : E → ℂ) (ENNReal.ofReal s) volume
  let Mass := Grad * NormG
  have gi : 𝓕⁻ G = (g : E → ℂ) := g.continuous.fourier_inversion g.integrable gHat.integrable
  have fr := radianActionSpectrum_radial_data f
  have hrF : eLpNorm (𝓕⁻ F) (ENNReal.ofReal p) volume ≤ KR * Grad := by
    change eLpNorm (𝓕⁻ (radianActionSpectrum (fun z => ‖z‖) f)) _ _ ≤ _
    rw [radianActionSpectrum_inverse]
    exact radial f
  have hV (j : Index) : eLpNorm (𝓕⁻ (V j)) (ENNReal.ofReal s) volume ≤ KA j * NormG := by
    change eLpNorm (𝓕⁻ (radianActionSpectrum (angularComponent b j) g)) _ _ ≤ _
    rw [radianActionSpectrum_inverse]
    exact angular j g
  let lowTerm (j : Index) := jointBilinear (paperLowSymbol b j) (mikhlinDerivative j f) g
  let productTerm (j : Index) := jointSpectralBilinear (paperAngularProduct b j) F G
  let inputTerm (j : Index) := jointSpectralBilinear (paperInputSymbol j) F (V j)
  have l (j : Index) : MemLp (lowTerm j) (ENNReal.ofReal r) volume ∧
      eLpNorm (lowTerm j) (ENNReal.ofReal r) volume ≤ KL j * Mass := by
    obtain ⟨mem, bd⟩ := low j (mikhlinDerivative j f) g
    exact ⟨mem, bd.trans (mul_le_mul_left' (mul_le_mul_right' (derivative_component_bound p j f) _) _)⟩
  have pr (j : Index) : MemLp (productTerm j) (ENNReal.ofReal r) volume ∧
      eLpNorm (productTerm j) (ENNReal.ofReal r) volume ≤ KP j * KR * Mass := by
    obtain ⟨mem, bd⟩ := product j F G fr.1 (gHat.smooth _).contDiffOn fr.2.1 gHat.integrable
      (fr.2.2 p hp) (gi.symm ▸ g.memLp (ENNReal.ofReal s) volume)
    rw [gi] at bd
    refine ⟨mem, bd.trans ?_⟩
    calc
      _ ≤ KP j * ((KR * Grad) * NormG) :=
        mul_le_mul_left' (mul_le_mul_right' hrF _) _
      _ = _ := by dsimp only [Mass]; ac_rfl
  have n (j : Index) : MemLp (inputTerm j) (ENNReal.ofReal r) volume ∧
      eLpNorm (inputTerm j) (ENNReal.ofReal r) volume ≤ KN j * KR * KA j * Mass := by
    have v := radianActionSpectrum_angular_data b hb hom j g
    obtain ⟨mem, bd⟩ := input j F (V j) fr.1 v.1 fr.2.1 v.2.1 (fr.2.2 p hp) (v.2.2 s hs)
    refine ⟨mem, bd.trans ?_⟩
    calc
      _ ≤ KN j * ((KR * Grad) * (KA j * NormG)) := mul_le_mul_left' (mul_le_mul' hrF (hV j)) _
      _ = _ := by dsimp only [Mass]; ac_rfl
  have hGrad : Grad < ⊤ := by
    simpa only [Grad, SchwartzMap.fderivCLM_apply] using
      ((SchwartzMap.fderivCLM ℝ f).memLp (ENNReal.ofReal p) volume).2
  have hMass := ENNReal.mul_lt_top hGrad (g.memLp (ENNReal.ofReal s) volume).2
  have hrq := Real.HolderConjugate.conjExponent hr
  apply CMBilinearDual.memLp_of_schwartz_pairing hrq (radian_commutator_continuous b hb hom f g)
    (ENNReal.mul_lt_top hC hMass).ne
  intro h
  let Q := eLpNorm (h : E → ℂ) (ENNReal.ofReal (Real.conjExponent r)) volume
  have sumPair (U : Index → E → ℂ) (K : Index → ℝ≥0∞)
      (bounds : ∀ j, MemLp (U j) (ENNReal.ofReal r) volume ∧
        eLpNorm (U j) (ENNReal.ofReal r) volume ≤ K j * Mass) :
      ‖∑ j, ∫ x, U j x * h x‖ₑ ≤ (∑ j, K j) * Mass * Q := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    exact (test_pairing_bound hrq (bounds j).1 h).trans (mul_le_mul_right' (bounds j).2 _)
  rw [radian_commutator_three_pairings b hb hom f g h]
  let IL := ∑ j, ∫ x, lowTerm j x * h x
  let IP := ∑ j, ∫ x, productTerm j x * h x
  let IN := ∑ j, ∫ x, inputTerm j x * h x
  change ‖IL + IP - IN‖ₑ ≤ _
  have triangle : ‖IL + IP - IN‖ₑ ≤ ‖IL + IP‖ₑ + ‖IN‖ₑ := by
    simpa only [sub_eq_add_neg, enorm_neg] using enorm_add_le (IL + IP) (-IN)
  refine (triangle.trans (add_le_add
    ((enorm_add_le IL IP).trans (add_le_add
      (sumPair lowTerm KL l) (sumPair productTerm (fun j => KP j * KR) pr)))
    (sumPair inputTerm (fun j => KN j * KR * KA j) n))).trans_eq ?_
  change Lc * Mass * Q + Pc * Mass * Q + Nc * Mass * Q = (Lc + Pc + Nc) * Mass * Q
  simp only [add_mul]

end Burnett.A02.FrequencySplit
