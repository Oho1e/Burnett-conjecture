import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearCancellation
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianCommutatorEstimate

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ContDiff ENNReal

/-- The L³ norm of the full Fréchet gradient of a component. -/
def energyGradientNorm (f : SchwartzMap E ℂ) : ℝ≥0∞ :=
  eLpNorm (fderiv ℝ (f : E → ℂ)) (ENNReal.ofReal 3) volume

private abbrev R : ℝ≥0∞ := ENNReal.ofReal (3 / 2)
private abbrev P : ℝ≥0∞ := ENNReal.ofReal 3

private theorem energyPartial_norm_le (j : Index) (f : SchwartzMap E ℂ) :
    eLpNorm (energyPartial j f : E → ℂ) P volume ≤ energyGradientNorm f := by
  apply eLpNorm_mono
  intro x
  change ‖(fderiv ℝ (f : E → ℂ) x) (EuclideanSpace.single j 1)‖ ≤ ‖fderiv ℝ (f : E → ℂ) x‖
  simpa using (fderiv ℝ (f : E → ℂ) x).le_opNorm (EuclideanSpace.single j 1)

private theorem cubic_test_holder {F G : E → ℂ} (hF : MemLp F R volume)
    (hG : MemLp G P volume) :
    ‖∫ x, F x * conj (G x)‖ₑ ≤ eLpNorm F R volume * eLpNorm G P volume := by
  have h : (3 / 2 : ℝ).HolderConjugate 3 := by constructor <;> norm_num
  letI : ENNReal.HolderConjugate R P := h.ennrealOfReal
  have hGc : AEStronglyMeasurable (fun x => conj (G x)) volume :=
    Complex.continuous_conj.comp_aestronglyMeasurable hG.1
  have normConj : eLpNorm (fun x => conj (G x)) P volume = eLpNorm G P volume :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => Complex.norm_conj (G x))
  calc
    _ ≤ ∫⁻ x, ‖F x * conj (G x)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (F • fun x => conj (G x)) 1 volume := eLpNorm_one_eq_lintegral_enorm.symm
    _ ≤ _ := by
      simpa only [normConj] using eLpNorm_smul_le_mul_eLpNorm (p := R) (q := P) (r := 1) hGc hF.1

private theorem cubic_product_holder {F G : E → ℂ} (hF : MemLp F P volume)
    (hG : MemLp G P volume) :
    MemLp (fun x => F x * G x) R volume ∧
      eLpNorm (fun x => F x * G x) R volume ≤ eLpNorm F P volume * eLpNorm G P volume := by
  have h : (3 : ℝ).HolderTriple 3 (3 / 2) := by constructor <;> norm_num
  letI : ENNReal.HolderTriple P P R := h.ennrealOfReal
  refine ⟨hG.mul' (r := R) hF, ?_⟩
  change eLpNorm (F • G) R volume ≤ _
  exact eLpNorm_smul_le_mul_eLpNorm (p := P) (q := P) (r := R) hG.1 hF.1

private theorem quasilinear_pairing_abs_bound {J : Type*} [Fintype J] (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (A : EnergyIndex J → SchwartzMap E ℂ) (u : J → SchwartzMap E ℂ)
    (hA : ∀ a d i j x, conj (A ((a,d),(i,j)) x) = A ((d,a),(j,i)) x) :
    ENNReal.ofReal |2 * (quasilinearPairing b A u).im| ≤
      ‖quasilinearCommutatorPairing b A u‖ₑ + 2 * ‖quasilinearCoefficientPairing b A u‖ₑ := by
  rw [quasilinear_imaginary_identity b hb hom A u hA, sub_eq_add_neg, ← neg_add, abs_neg]
  apply (ENNReal.ofReal_le_ofReal (abs_add_le ..)).trans
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  have him (z : ℂ) : ENNReal.ofReal |z.im| ≤ ‖z‖ₑ := by
    rw [← ofReal_norm_eq_enorm z]
    exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm z)
  norm_num
  exact add_le_add (him _) (mul_le_mul_left' (him _) _)

/-- Hölder's inequality and the actual commutator bound control the imaginary
part of the complete quasilinear energy by three first-derivative norms. -/
theorem quasilinear_imaginary_estimate (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {J : Type} [Fintype J]
    (A : EnergyIndex J → SchwartzMap E ℂ) (u : J → SchwartzMap E ℂ),
      (∀ a d i j x, conj (A ((a,d),(i,j)) x) = A ((d,a),(j,i)) x) →
      ENNReal.ofReal |2 * (quasilinearPairing b A u).im| ≤
        C * ∑ k : EnergyIndex J, energyGradientNorm (A k) *
          (energyGradientNorm (u k.2.2) * energyGradientNorm (u k.2.1)) := by
  obtain ⟨K, hK, comm⟩ := radian_commutator_Lp_bound 3 3 (3 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) b hb hom
  obtain ⟨M, hM, action⟩ := radian_degree_one_gradient_bound 3 (by norm_num) b hb hom
  refine ⟨K + 2 * M, ENNReal.add_lt_top.mpr ⟨hK, ENNReal.mul_lt_top (by norm_num) hM⟩, ?_⟩
  intro J _ A u hA
  let S (k : EnergyIndex J) := energyGradientNorm (A k) *
    (energyGradientNorm (u k.2.2) * energyGradientNorm (u k.2.1))
  have commBound : ‖quasilinearCommutatorPairing b A u‖ₑ ≤ K * ∑ k, S k := by
    unfold quasilinearCommutatorPairing
    apply (enorm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    let U := energyPartial k.1.2 (u k.2.2)
    let V := energyPartial k.1.1 (u k.2.1)
    have ck := comm (A k) U
    have hnU := energyPartial_norm_le k.1.2 (u k.2.2)
    have hnV := energyPartial_norm_le k.1.1 (u k.2.1)
    calc
      _ ≤ eLpNorm (radianCommutator b (A k) U) R volume * eLpNorm (V : E → ℂ) P volume :=
        cubic_test_holder ck.1 (V.memLp _ _)
      _ ≤ (K * (energyGradientNorm (A k) * energyGradientNorm (u k.2.2))) *
          energyGradientNorm (u k.2.1) :=
        mul_le_mul' (ck.2.trans (mul_le_mul_left' (mul_le_mul_left' hnU _) _)) hnV
      _ = K * S k := by dsimp only [S]; ring
  have coeffBound : ‖quasilinearCoefficientPairing b A u‖ₑ ≤ M * ∑ k, S k := by
    unfold quasilinearCoefficientPairing
    apply (enorm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    let F := energyPartial k.1.1 (A k)
    let U := energyPartial k.1.2 (u k.2.2)
    let G := radianAction b (u k.2.1)
    have hprod := cubic_product_holder (F.memLp _ _) (U.memLp _ _)
    have hnF := energyPartial_norm_le k.1.1 (A k)
    have hnU := energyPartial_norm_le k.1.2 (u k.2.2)
    have bk := action (u k.2.1)
    calc
      _ ≤ eLpNorm (fun x => F x * U x) R volume * eLpNorm G P volume :=
        cubic_test_holder hprod.1 bk.1
      _ ≤ (energyGradientNorm (A k) * energyGradientNorm (u k.2.2)) *
          (M * energyGradientNorm (u k.2.1)) :=
        mul_le_mul' (hprod.2.trans (mul_le_mul' hnF hnU)) bk.2
      _ = M * S k := by dsimp only [S]; ring
  refine (quasilinear_pairing_abs_bound b hb hom A u hA).trans ?_
  calc
    _ ≤ K * (∑ k, S k) + 2 * (M * ∑ k, S k) := add_le_add commBound (mul_le_mul_left' coeffBound _)
    _ = _ := by change _ = (K + 2 * M) * ∑ k, S k; ring

end Burnett.A02.FrequencySplit
