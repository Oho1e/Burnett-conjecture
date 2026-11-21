import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeMikhlinApplications
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeMikhlinOuter
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianCommutatorEstimate
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualBound
import Burnett.Analysis.CubicEnergy.CompleteEnergy.SymbolSeminormLow

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Finset Metric Burnett.RicciSymbol
open scoped ContDiff ENNReal FourierTransform

private theorem derivative_component_norm_bound (p : ℝ) (j : Index) (f : SchwartzMap E ℂ) :
    eLpNorm (mikhlinDerivative j f : E → ℂ) (ENNReal.ofReal p) volume ≤
      eLpNorm (fderiv ℝ (f : E → ℂ)) (ENNReal.ofReal p) volume := by
  apply eLpNorm_mono
  intro x
  change ‖(-Complex.I) • (fderiv ℝ (f : E → ℂ) x (EuclideanSpace.single j 1))‖ ≤ _
  simpa using (fderiv ℝ (f : E → ℂ) x).le_opNorm (EuclideanSpace.single j 1)

private theorem schwartz_pairing_norm_bound {r q : ℝ} (hrq : r.HolderConjugate q) {u : E → ℂ}
    (hu : MemLp u (ENNReal.ofReal r) volume) (h : SchwartzMap E ℂ) :
    ‖∫ x, u x * h x‖ₑ ≤
      eLpNorm u (ENNReal.ofReal r) volume * eLpNorm (h : E → ℂ) (ENNReal.ofReal q) volume := by
  letI : ENNReal.HolderConjugate (ENNReal.ofReal r) (ENNReal.ofReal q) := hrq.ennrealOfReal
  calc
    _ ≤ ∫⁻ x, ‖u x * h x‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (u • (h : E → ℂ)) 1 volume := eLpNorm_one_eq_lintegral_enorm.symm
    _ ≤ _ := eLpNorm_smul_le_mul_eLpNorm h.continuous.aestronglyMeasurable hu.1

/-- The actual first-order radian Fourier commutator has a linear bound in
the symbol's sphere jet. Order sixteen suffices: the low slot uses one
derivative of b before the joint jet of order fifteen, and the angular
factors use order six. -/
theorem radian_commutator_Lp_sphere_bound (p s r : ℝ) (hp : 1 < p) (hs : 1 < s) (hr : 1 < r)
    (he : r⁻¹ = p⁻¹ + s⁻¹) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ f g : SchwartzMap E ℂ,
        MemLp (radianCommutator b f g) (ENNReal.ofReal r) volume ∧
          eLpNorm (radianCommutator b f g) (ENNReal.ofReal r) volume ≤ C * ENNReal.ofReal D *
            (eLpNorm (fderiv ℝ (f : E → ℂ)) (ENNReal.ofReal p) volume *
              eLpNorm (g : E → ℂ) (ENNReal.ofReal s) volume) := by
  classical
  obtain ⟨KL,hKL,low⟩ := joint_bilinear_sphere_bound p s r hp hs hr he
  obtain ⟨AL,hAL,lowJet⟩ := low_symbol_sphere_jet 15
  obtain ⟨AP,hAP,angJet⟩ := angular_component_sphere_jet 6
  choose KP hKP product using fun j => joint_spectral_bilinear_outer_sphere_bound p s r hp hs hr he _
    (paperProductSymbol_regular j).1 (paperProductSymbol_regular j).2
  choose KN hKN input using fun j => joint_spectral_bilinear_bound p s r hp hs hr he _
    (paperInputSymbol_regular j).1 (paperInputSymbol_regular j).2
  obtain ⟨KA,hKA,angular⟩ := paper_cj_Schwartz_sphere_bound s hs
  obtain ⟨KR,hKR,radial⟩ := mikhlin_radial_gradient_bound p hp
  let Lcoef (_ : Index) := KL * ENNReal.ofReal AL
  let Pcoef (j : Index) := KP j * ENNReal.ofReal AP * KR
  let Ncoef (j : Index) := KN j * KR * KA
  let Lc := ∑ j, Lcoef j
  let Pc := ∑ j, Pcoef j
  let Nc := ∑ j, Ncoef j
  have hL : Lc < ⊤ := ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.mul_lt_top hKL ENNReal.ofReal_lt_top)
  have hP : Pc < ⊤ := ENNReal.sum_lt_top.mpr
    (fun j _ => ENNReal.mul_lt_top (ENNReal.mul_lt_top (hKP j) ENNReal.ofReal_lt_top) hKR)
  have hN : Nc < ⊤ := ENNReal.sum_lt_top.mpr
    (fun j _ => ENNReal.mul_lt_top (ENNReal.mul_lt_top (hKN j) hKR) hKA)
  have hC : Lc + Pc + Nc < ⊤ := ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr ⟨hL,hP⟩,hN⟩
  refine ⟨Lc+Pc+Nc,hC,?_⟩
  intro b hb hom D hD jet f g
  let S := ENNReal.ofReal D
  have jet₆ (i : ℕ) (hi : i ≤ 6) (ξ : E) (hξ : ξ ∈ sphere (0 : E) 1) :
      ‖iteratedFDeriv ℝ i b ξ‖ ≤ D := jet i (by omega) ξ hξ
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
  have hV (j : Index) : eLpNorm (𝓕⁻ (V j)) (ENNReal.ofReal s) volume ≤ KA * S * NormG := by
    change eLpNorm (𝓕⁻ (radianActionSpectrum (angularComponent b j) g)) _ _ ≤ _
    rw [radianActionSpectrum_inverse]
    exact angular b hb hom D hD jet₆ j g
  let lowTerm (j : Index) := jointBilinear (paperLowSymbol b j) (mikhlinDerivative j f) g
  let productTerm (j : Index) := jointSpectralBilinear (paperAngularProduct b j) F G
  let inputTerm (j : Index) := jointSpectralBilinear (paperInputSymbol j) F (V j)
  have l (j : Index) : MemLp (lowTerm j) (ENNReal.ofReal r) volume ∧
      eLpNorm (lowTerm j) (ENNReal.ofReal r) volume ≤ Lcoef j * S * Mass := by
    have reg := paperLowSymbol_regular b hb hom j
    obtain ⟨mem,bd⟩ := low (paperLowSymbol b j) reg.1 reg.2 (AL * D) (mul_nonneg hAL hD)
      (lowJet b hb hom D hD jet j) (mikhlinDerivative j f) g
    refine ⟨mem,bd.trans ?_⟩
    calc
      _ ≤ KL * ENNReal.ofReal (AL * D) * Mass :=
        mul_le_mul_left' (mul_le_mul_right' (derivative_component_norm_bound p j f) _) _
      _ = _ := by simp only [Lcoef,S,ENNReal.ofReal_mul hAL,mul_assoc]
  have pr (j : Index) : MemLp (productTerm j) (ENNReal.ofReal r) volume ∧
      eLpNorm (productTerm j) (ENNReal.ofReal r) volume ≤ Pcoef j * S * Mass := by
    obtain ⟨mem,bd⟩ := product j (angularComponent b j) (angularComponent_contDiffOn b hb j)
      (angularComponent_scale hom j) (AP * D) (mul_nonneg hAP hD) (angJet b hb D hD jet₆ j)
      F G fr.1 (gHat.smooth _).contDiffOn fr.2.1 gHat.integrable
      (fr.2.2 p hp) (gi.symm ▸ g.memLp (ENNReal.ofReal s) volume)
    rw [gi] at bd
    refine ⟨mem,bd.trans ?_⟩
    calc
      _ ≤ KP j * ENNReal.ofReal (AP * D) * ((KR * Grad) * NormG) :=
        mul_le_mul_left' (mul_le_mul_right' hrF _) _
      _ = _ := by
        rw [ENNReal.ofReal_mul hAP]
        dsimp only [Pcoef,S,Mass]
        ac_rfl
  have n (j : Index) : MemLp (inputTerm j) (ENNReal.ofReal r) volume ∧
      eLpNorm (inputTerm j) (ENNReal.ofReal r) volume ≤ Ncoef j * S * Mass := by
    have v := radianActionSpectrum_angular_data b hb hom j g
    obtain ⟨mem,bd⟩ := input j F (V j) fr.1 v.1 fr.2.1 v.2.1 (fr.2.2 p hp) (v.2.2 s hs)
    refine ⟨mem,bd.trans ?_⟩
    calc
      _ ≤ KN j * ((KR * Grad) * (KA * S * NormG)) := mul_le_mul_left' (mul_le_mul' hrF (hV j)) _
      _ = _ := by dsimp only [Ncoef,Mass]; ac_rfl
  have hGrad : Grad < ⊤ := by
    simpa only [Grad,SchwartzMap.fderivCLM_apply] using
      ((SchwartzMap.fderivCLM ℝ f).memLp (ENNReal.ofReal p) volume).2
  have hMass := ENNReal.mul_lt_top hGrad (g.memLp (ENNReal.ofReal s) volume).2
  obtain ⟨_,_,qualitative⟩ := radian_commutator_Lp_bound p s r hp hs hr he b hb hom
  have hu := (qualitative f g).1
  refine ⟨hu,?_⟩
  have hrq := Real.HolderConjugate.conjExponent hr
  apply CMBilinearDual.eLpNorm_le_of_schwartz_pairing hrq hu
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top) hMass).ne
  intro h
  let Q := eLpNorm (h : E → ℂ) (ENNReal.ofReal (Real.conjExponent r)) volume
  have sumPair (U : Index → E → ℂ) (K : Index → ℝ≥0∞)
      (bounds : ∀ j, MemLp (U j) (ENNReal.ofReal r) volume ∧
        eLpNorm (U j) (ENNReal.ofReal r) volume ≤ K j * S * Mass) :
      ‖∑ j, ∫ x, U j x * h x‖ₑ ≤ (∑ j, K j) * S * Mass * Q := by
    rw [Finset.sum_mul,Finset.sum_mul,Finset.sum_mul]
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    exact (schwartz_pairing_norm_bound hrq (bounds j).1 h).trans (mul_le_mul_right' (bounds j).2 _)
  rw [radian_commutator_three_pairings b hb hom f g h]
  let IL := ∑ j, ∫ x, lowTerm j x * h x
  let IP := ∑ j, ∫ x, productTerm j x * h x
  let IN := ∑ j, ∫ x, inputTerm j x * h x
  change ‖IL + IP - IN‖ₑ ≤ _
  have triangle : ‖IL + IP - IN‖ₑ ≤ ‖IL + IP‖ₑ + ‖IN‖ₑ := by
    simpa only [sub_eq_add_neg,enorm_neg] using enorm_add_le (IL + IP) (-IN)
  refine (triangle.trans (add_le_add
    ((enorm_add_le IL IP).trans (add_le_add (sumPair lowTerm Lcoef l) (sumPair productTerm Pcoef pr)))
    (sumPair inputTerm Ncoef n))).trans_eq ?_
  change Lc * S * Mass * Q + Pc * S * Mass * Q + Nc * S * Mass * Q = (Lc + Pc + Nc) * S * Mass * Q
  simp only [add_mul]

end Burnett.A02.FrequencySplit
