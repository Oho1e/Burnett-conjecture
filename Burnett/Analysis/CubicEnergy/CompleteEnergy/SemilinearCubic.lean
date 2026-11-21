import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianDegreeOne
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianOrderOnePairing

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Finset Burnett.RicciSymbol
open scoped ContDiff ENNReal ComplexConjugate

private def firstOrderMonomial {J : Type*}
    (q : Index → Index → J → J → J → ℝ) (u v : J → SchwartzMap E ℂ)
    (k : J) (i : (Index × J) × (Index × J)) (x : E) : ℂ :=
  (q i.1.1 i.2.1 i.1.2 i.2.2 k : ℂ) *
    energyPartial i.1.1 (u i.1.2) x * energyPartial i.2.1 (v i.2.2) x

/-- The fixed real coefficients extend complex bilinearly in the two
first-derivative inputs. Their final index is the output component. -/
def semilinearDerivativeTerm {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) (u v : J → SchwartzMap E ℂ) (k : J) (x : E) : ℂ :=
  ∑ i : (Index × J) × (Index × J), firstOrderMonomial q u v k i x

/-- Hermitian pairing, with the actual radian Fourier action in the test slot. -/
def semilinearHermitianPairing {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (u v w : J → SchwartzMap E ℂ) : ℂ :=
  ∑ k, ∫ x, semilinearDerivativeTerm q u v k x * conj (radianAction b (w k) x)

/-- The real semilinear contribution to the cubic energy on three fields. -/
def semilinearCubicForm {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (u v w : J → SchwartzMap E ℂ) : ℝ :=
  2 * (semilinearHermitianPairing q b u v w).im

def semilinearGradientNorm {J : Type*} [Fintype J] (u : J → SchwartzMap E ℂ) : ℝ≥0∞ :=
  ∑ k, eLpNorm (fderiv ℝ (u k : E → ℂ)) 3 volume

private theorem partial_norm_le_gradient (j : Index) (f : SchwartzMap E ℂ) :
    eLpNorm (energyPartial j f : E → ℂ) 3 volume ≤
      eLpNorm (fderiv ℝ (f : E → ℂ)) 3 volume := by
  apply eLpNorm_mono
  intro x
  change ‖fderiv ℝ (f : E → ℂ) x (EuclideanSpace.single j 1)‖ ≤ _
  simpa using (fderiv ℝ (f : E → ℂ) x).le_opNorm (EuclideanSpace.single j 1)

private theorem three_three_holder : ENNReal.HolderTriple 3 3 (ENNReal.ofReal (3/2)) := by
  have h : (3 : ℝ).HolderTriple 3 (3/2) := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using h.ennrealOfReal

private theorem three_halves_three_holder : ENNReal.HolderTriple (ENNReal.ofReal (3/2)) 3 1 := by
  have h : (3/2 : ℝ).HolderTriple 3 1 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using h.ennrealOfReal

private theorem triple_pairing_bound {P Q R S : ℝ≥0∞} [ENNReal.HolderTriple P Q S]
    [ENNReal.HolderTriple S R 1] (A B C : E → ℂ)
    (hA : MemLp A P volume) (hB : MemLp B Q volume) (hC : MemLp C R volume) :
    Integrable (fun x => A x * B x * conj (C x)) ∧
      ‖∫ x, A x * B x * conj (C x)‖ₑ ≤
        eLpNorm A P volume * eLpNorm B Q volume * eLpNorm C R volume := by
  let AB := fun x : E => A x * B x
  let Z := fun x : E => conj (C x)
  have same : ∀ᵐ x ∂(volume : Measure E), ‖C x‖ = ‖Z x‖ :=
    Filter.Eventually.of_forall fun x => (Complex.norm_conj (C x)).symm
  have hZ : MemLp Z R volume := hC.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hC.1) same
  have hAB : MemLp AB S volume := hB.mul' (r := S) hA
  have hABC : MemLp (fun x => AB x * Z x) 1 volume := hZ.mul' (r := 1) hAB
  refine ⟨memLp_one_iff_integrable.mp hABC,?_⟩
  have abBound : eLpNorm AB S volume ≤ eLpNorm A P volume * eLpNorm B Q volume :=
    eLpNorm_smul_le_mul_eLpNorm (φ := A) (f := B) (p := P) (q := Q) (r := S) hB.1 hA.1
  have zNorm : eLpNorm Z R volume = eLpNorm C R volume :=
    eLpNorm_congr_norm_ae (same.mono fun _ hx => hx.symm)
  calc
    _ ≤ ∫⁻ x, ‖A x * B x * conj (C x)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x => AB x * Z x) 1 volume := eLpNorm_one_eq_lintegral_enorm.symm
    _ ≤ eLpNorm AB S volume * eLpNorm Z R volume :=
      eLpNorm_smul_le_mul_eLpNorm (φ := AB) (f := Z) (p := S) (q := R) (r := 1) hZ.1 hAB.1
    _ ≤ _ := by
      rw [zNorm]
      exact mul_le_mul_right' abBound _

/-- Hölder controls the exact Hermitian pairing for every fixed
first-derivative bilinear coefficient array on a finite field space. -/
theorem semilinear_Hermitian_pairing_L3_bound {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t * b x) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ u v w : J → SchwartzMap E ℂ,
      (∀ k, Integrable (fun x => semilinearDerivativeTerm q u v k x *
        conj (radianAction b (w k) x))) ∧
      ‖semilinearHermitianPairing q b u v w‖ₑ ≤
        K * (semilinearGradientNorm u * semilinearGradientNorm v * semilinearGradientNorm w) := by
  classical
  let I := (Index × J) × (Index × J)
  obtain ⟨G,hG,action⟩ := radian_degree_one_gradient_bound 3 (by norm_num) b hb hom
  let W (k : J) (i : I) := ENNReal.ofReal |q i.1.1 i.2.1 i.1.2 i.2.2 k|
  let T := ∑ k, ∑ i, W k i
  have hT : T < ⊤ := ENNReal.sum_lt_top.mpr fun _ _ =>
    ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top
  refine ⟨T * G, ENNReal.mul_lt_top hT hG, ?_⟩
  intro u v w
  let Mass := semilinearGradientNorm u * semilinearGradientNorm v * semilinearGradientNorm w
  let product (k : J) (i : I) (x : E) :=
    firstOrderMonomial q u v k i x * conj (radianAction b (w k) x)
  have component (z : J → SchwartzMap E ℂ) (k : J) :
      eLpNorm (fderiv ℝ (z k : E → ℂ)) 3 volume ≤ semilinearGradientNorm z := by
    unfold semilinearGradientNorm
    exact single_le_sum (f := fun l : J => eLpNorm (fderiv ℝ (z l : E → ℂ)) 3 volume)
      (fun _ _ => zero_le _) (mem_univ k)
  have estimate (k : J) (i : I) : Integrable (product k i) ∧
      ‖∫ x, product k i x‖ₑ ≤ (W k i * G) * Mass := by
    let A := energyPartial i.1.1 (u i.1.2)
    let B := energyPartial i.2.1 (v i.2.2)
    let C := radianAction b (w k)
    have e3 : ENNReal.ofReal (3 : ℝ) = 3 := by norm_num
    have dC : MemLp C 3 volume ∧
        eLpNorm C 3 volume ≤ G * eLpNorm (fderiv ℝ (w k : E → ℂ)) 3 volume := by
      simpa only [C,e3] using action (w k)
    letI := three_three_holder
    letI := three_halves_three_holder
    have h := triple_pairing_bound (S := ENNReal.ofReal (3/2)) A B C
      (A.memLp 3 volume) (B.memLp 3 volume) dC.1
    let c := (q i.1.1 i.2.1 i.1.2 i.2.2 k : ℂ)
    have eq : product k i = fun x => c * (A x * B x * conj (C x)) := by
      funext x
      simp only [product,firstOrderMonomial,c,A,B,C,mul_assoc]
    have wc : ‖c‖ₑ = W k i := by
      rw [← ofReal_norm_eq_enorm]
      simp only [c, W, Complex.norm_real, Real.norm_eq_abs]
    have hA : eLpNorm (A : E → ℂ) 3 volume ≤ semilinearGradientNorm u :=
      (partial_norm_le_gradient i.1.1 (u i.1.2)).trans (component u i.1.2)
    have hB : eLpNorm (B : E → ℂ) 3 volume ≤ semilinearGradientNorm v :=
      (partial_norm_le_gradient i.2.1 (v i.2.2)).trans (component v i.2.2)
    have hC : eLpNorm C 3 volume ≤ G * semilinearGradientNorm w :=
      dC.2.trans (mul_le_mul_left' (component w k) _)
    rw [eq]
    refine ⟨h.1.const_mul c,?_⟩
    rw [integral_const_mul,enorm_mul,wc]
    calc
      _ ≤ W k i * (eLpNorm (A : E → ℂ) 3 volume * eLpNorm (B : E → ℂ) 3 volume * eLpNorm C 3 volume) :=
        mul_le_mul_left' h.2 _
      _ ≤ W k i * (semilinearGradientNorm u * semilinearGradientNorm v * (G * semilinearGradientNorm w)) :=
        mul_le_mul_left' (mul_le_mul' (mul_le_mul' hA hB) hC) _
      _ = _ := by unfold Mass; ac_rfl
  have expand (k : J) (x : E) : semilinearDerivativeTerm q u v k x * conj (radianAction b (w k) x) =
      ∑ i, product k i x := by
    unfold semilinearDerivativeTerm product
    rw [Finset.sum_mul]
  refine ⟨fun k => ?_,?_⟩
  · simp_rw [expand]
    exact integrable_finset_sum _ (fun i _ => (estimate k i).1)
  · unfold semilinearHermitianPairing
    simp_rw [expand]
    have sumIntegral (k : J) : (∫ x, ∑ i, product k i x) = ∑ i, ∫ x, product k i x :=
      integral_finset_sum _ (fun i _ => (estimate k i).1)
    simp_rw [sumIntegral]
    calc
      _ ≤ ∑ k, ∑ i, ‖∫ x, product k i x‖ₑ :=
        (enorm_sum_le _ _).trans (sum_le_sum fun _ _ => enorm_sum_le _ _)
      _ ≤ ∑ k, ∑ i, (W k i * G) * Mass :=
        sum_le_sum fun k _ => sum_le_sum fun i _ => (estimate k i).2
      _ = _ := by simp only [T, Mass, Finset.sum_mul]

/-- The paper's real semilinear cubic energy has the product of the three
gradient L³ norms as a bound on its three actual input fields. -/
theorem semilinear_cubic_L3_bound {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t * b x) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ u v w : J → SchwartzMap E ℂ,
      (∀ k, Integrable (fun x => semilinearDerivativeTerm q u v k x *
        conj (radianAction b (w k) x))) ∧
      ‖semilinearCubicForm q b u v w‖ₑ ≤
        K * (semilinearGradientNorm u * semilinearGradientNorm v * semilinearGradientNorm w) := by
  obtain ⟨K,hK,est⟩ := semilinear_Hermitian_pairing_L3_bound q b hb hom
  refine ⟨2*K, ENNReal.mul_lt_top (by norm_num) hK, ?_⟩
  intro u v w
  obtain ⟨integrable,bd⟩ := est u v w
  refine ⟨integrable,?_⟩
  let z := semilinearHermitianPairing q b u v w
  have hIm : ‖z.im‖ₑ ≤ ‖z‖ₑ := by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm z)
  change ‖(2 : ℝ) * z.im‖ₑ ≤ _
  rw [enorm_mul, show ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) by norm_num [← ofReal_norm_eq_enorm]]
  exact (mul_le_mul_left' (hIm.trans bd) _).trans_eq (mul_assoc ..).symm

end Burnett.A02.FrequencySplit
