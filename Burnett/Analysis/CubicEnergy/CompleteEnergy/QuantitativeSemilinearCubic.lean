import Burnett.Analysis.CubicEnergy.CompleteEnergy.SemilinearCubicAlgebra
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeRadianDegreeOne

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Finset Metric Burnett.RicciSymbol
open scoped BigOperators ComplexConjugate ContDiff ENNReal

private abbrev IntermediateExponent : ℝ≥0∞ := ENNReal.ofReal (3 / 2)
private abbrev DerivativeIndices (J : Type*) := (Index × J) × (Index × J)

private def coefficientMass {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) (k : J) : ℝ≥0∞ :=
  ∑ i : DerivativeIndices J, ‖(q i.1.1 i.2.1 i.1.2 i.2.2 k : ℂ)‖ₑ

private theorem component_gradient_le {J : Type*} [Fintype J] (u : J → SchwartzMap E ℂ) (k : J) :
    eLpNorm (fderiv ℝ (u k : E → ℂ)) 3 volume ≤ semilinearGradientNorm u := by
  unfold semilinearGradientNorm
  exact single_le_sum (f := fun l : J => eLpNorm (fderiv ℝ (u l : E → ℂ)) 3 volume)
    (fun _ _ => zero_le _) (mem_univ k)

private theorem component_derivative_le {J : Type*} [Fintype J] (u : J → SchwartzMap E ℂ) (p : Index × J) :
    eLpNorm (energyPartial p.1 (u p.2) : E → ℂ) 3 volume ≤ semilinearGradientNorm u := by
  refine (eLpNorm_mono (f := (energyPartial p.1 (u p.2) : E → ℂ))
    (g := fderiv ℝ (u p.2 : E → ℂ)) ?_).trans (component_gradient_le u p.2)
  intro x
  change ‖fderiv ℝ (u p.2 : E → ℂ) x (EuclideanSpace.single p.1 1)‖ ≤ _
  simpa using (fderiv ℝ (u p.2 : E → ℂ) x).le_opNorm (EuclideanSpace.single p.1 1)

private theorem three_three_holder : ENNReal.HolderTriple 3 3 IntermediateExponent := by
  have h : (3 : ℝ).HolderTriple 3 (3/2) := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using h.ennrealOfReal

private theorem three_halves_three_holder : ENNReal.HolderTriple IntermediateExponent 3 1 := by
  have h : (3/2 : ℝ).HolderTriple 3 1 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using h.ennrealOfReal

private theorem semilinear_derivative_bound {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) (u v : J → SchwartzMap E ℂ) (k : J) :
    MemLp (semilinearDerivativeTerm q u v k) IntermediateExponent volume ∧
      eLpNorm (semilinearDerivativeTerm q u v k) IntermediateExponent volume ≤
        coefficientMass q k * (semilinearGradientNorm u * semilinearGradientNorm v) := by
  letI := three_three_holder
  let W (i : DerivativeIndices J) : ℂ := q i.1.1 i.2.1 i.1.2 i.2.2 k
  let F (i : DerivativeIndices J) (x : E) := W i * energyPartial i.1.1 (u i.1.2) x * energyPartial i.2.1 (v i.2.2) x
  have each (i : DerivativeIndices J) : MemLp (F i) IntermediateExponent volume ∧
      eLpNorm (F i) IntermediateExponent volume ≤ ‖W i‖ₑ * (semilinearGradientNorm u * semilinearGradientNorm v) := by
    let a := energyPartial i.1.1 (u i.1.2)
    let b := energyPartial i.2.1 (v i.2.2)
    let g (x : E) := a x * b x
    have hA := a.memLp 3 volume
    have hB := b.memLp 3 volume
    have hg : MemLp g IntermediateExponent volume := hB.mul' hA
    have shape : F i = W i • g := by
      funext x
      simp only [F,a,b,g,Pi.smul_apply,smul_eq_mul,mul_assoc]
    rw [shape]
    refine ⟨hg.const_smul _, eLpNorm_const_smul_le.trans ?_⟩
    have hG : eLpNorm g IntermediateExponent volume ≤
        eLpNorm (a : E → ℂ) 3 volume * eLpNorm (b : E → ℂ) 3 volume :=
      eLpNorm_smul_le_mul_eLpNorm (φ := (a : E → ℂ)) (f := (b : E → ℂ))
        (p := 3) (q := 3) (r := IntermediateExponent) hB.1 hA.1
    exact mul_le_mul_left' (hG.trans (mul_le_mul' (component_derivative_le u i.1)
      (component_derivative_le v i.2))) _
  have eq : semilinearDerivativeTerm q u v k = ∑ i, F i := by
    funext x
    rw [Finset.sum_apply]
    rfl
  rw [eq]
  refine ⟨memLp_finset_sum' _ (fun i _ => (each i).1), ?_⟩
  calc
    _ ≤ ∑ i, eLpNorm (F i) IntermediateExponent volume :=
      eLpNorm_sum_le (fun i _ => (each i).1.1) (by norm_num)
    _ ≤ ∑ i, ‖W i‖ₑ * (semilinearGradientNorm u * semilinearGradientNorm v) :=
      sum_le_sum fun i _ => (each i).2
    _ = _ := by simp only [coefficientMass,W,Finset.sum_mul]

private theorem pairing_holder (f g : E → ℂ)
    (hf : MemLp f IntermediateExponent volume) (hg : MemLp g 3 volume) :
    Integrable (fun x => f x * conj (g x)) ∧
      ‖∫ x, f x * conj (g x)‖ₑ ≤ eLpNorm f IntermediateExponent volume * eLpNorm g 3 volume := by
  letI := three_halves_three_holder
  let Z := fun x : E => conj (g x)
  have same : ∀ᵐ x ∂(volume : Measure E), ‖g x‖ = ‖Z x‖ :=
    Filter.Eventually.of_forall fun x => (Complex.norm_conj (g x)).symm
  have hz : MemLp Z 3 volume := hg.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hg.1) same
  have fint : MemLp (fun x => f x * Z x) 1 volume := hz.mul' hf
  refine ⟨memLp_one_iff_integrable.mp fint, ?_⟩
  have znorm : eLpNorm Z 3 volume = eLpNorm g 3 volume :=
    eLpNorm_congr_norm_ae (same.mono fun _ hx => hx.symm)
  calc
    _ ≤ ∫⁻ x, ‖f x * Z x‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x => f x * Z x) 1 volume := eLpNorm_one_eq_lintegral_enorm.symm
    _ ≤ eLpNorm f IntermediateExponent volume * eLpNorm Z 3 volume :=
      eLpNorm_smul_le_mul_eLpNorm (φ := f) (f := Z) (p := IntermediateExponent) (q := 3) (r := 1) hz.1 hf.1
    _ = _ := by rw [znorm]

/-- The exact semilinear Hermitian pairing is uniformly controlled by six
ambient derivatives of the actual order-one multiplier on the unit sphere. -/
theorem semilinear_Hermitian_pairing_L3_sphere_bound {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ u v w : J → SchwartzMap E ℂ,
        (∀ k, Integrable (fun x => semilinearDerivativeTerm q u v k x *
          conj (radianAction b (w k) x))) ∧
        ‖semilinearHermitianPairing q b u v w‖ₑ ≤ K * ENNReal.ofReal D *
          (semilinearGradientNorm u * semilinearGradientNorm v * semilinearGradientNorm w) := by
  obtain ⟨L,hL,action⟩ := radian_degree_one_gradient_sphere_bound 3 (by norm_num)
  let A := ∑ k, coefficientMass q k
  have hA : A < ⊤ := ENNReal.sum_lt_top.mpr fun k _ =>
    ENNReal.sum_lt_top.mpr fun _ _ => enorm_lt_top
  refine ⟨A*L,ENNReal.mul_lt_top hA hL,?_⟩
  intro b hb hom D hD jet u v w
  let G := semilinearGradientNorm u * semilinearGradientNorm v * semilinearGradientNorm w
  let S := ENNReal.ofReal D
  have each (k : J) : Integrable (fun x => semilinearDerivativeTerm q u v k x * conj (radianAction b (w k) x)) ∧
      ‖∫ x, semilinearDerivativeTerm q u v k x * conj (radianAction b (w k) x)‖ₑ ≤
        (coefficientMass q k * L) * S * G := by
    let B := radianAction b (w k)
    have e3 : ENNReal.ofReal (3 : ℝ) = 3 := by norm_num
    have hbW : MemLp B 3 volume ∧
        eLpNorm B 3 volume ≤ L*S*eLpNorm (fderiv ℝ (w k : E → ℂ)) 3 volume := by
      simpa only [B,S,e3] using action b hb hom D hD jet (w k)
    have hB := hbW.2.trans (mul_le_mul_left' (component_gradient_le w k) _)
    obtain ⟨hQ,qbound⟩ := semilinear_derivative_bound q u v k
    obtain ⟨ih,hbnd⟩ := pairing_holder (semilinearDerivativeTerm q u v k) B hQ hbW.1
    refine ⟨ih,hbnd.trans ?_⟩
    calc
      _ ≤ (coefficientMass q k * (semilinearGradientNorm u * semilinearGradientNorm v)) *
        (L * S * semilinearGradientNorm w) := mul_le_mul' qbound hB
      _ = _ := by unfold G; ac_rfl
  refine ⟨fun k => (each k).1, ?_⟩
  unfold semilinearHermitianPairing
  calc
    _ ≤ ∑ k, ‖∫ x, semilinearDerivativeTerm q u v k x * conj (radianAction b (w k) x)‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ k, (coefficientMass q k * L) * S * G := sum_le_sum fun k _ => (each k).2
    _ = _ := by simp only [A,G,S,Finset.sum_mul]

/-- The same uniform coefficient bounds the exact real energy
after taking twice the imaginary part. -/
theorem semilinear_cubic_L3_sphere_bound {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ u v w : J → SchwartzMap E ℂ,
        ‖semilinearCubicForm q b u v w‖ₑ ≤ K * ENNReal.ofReal D *
          (semilinearGradientNorm u * semilinearGradientNorm v * semilinearGradientNorm w) := by
  obtain ⟨K,hK,est⟩ := semilinear_Hermitian_pairing_L3_sphere_bound q
  refine ⟨2*K,ENNReal.mul_lt_top (by norm_num) hK,?_⟩
  intro b hb hom D hD jet u v w
  have bd := (est b hb hom D hD jet u v w).2
  let z := semilinearHermitianPairing q b u v w
  have hIm : ‖z.im‖ₑ ≤ ‖z‖ₑ := by
    rw [← ofReal_norm_eq_enorm,← ofReal_norm_eq_enorm,Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm z)
  change ‖(2 : ℝ) * z.im‖ₑ ≤ _
  rw [enorm_mul,show ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) by norm_num [← ofReal_norm_eq_enorm]]
  simpa only [mul_assoc] using mul_le_mul_left' (hIm.trans bd) (2 : ℝ≥0∞)

/-- A bound uniform in the symbol for the previously constructed actual real
trilinear semilinear map. -/
theorem semilinear_cubic_multilinear_L3_sphere_bound {J : Type*} [Fintype J]
    (q : Index → Index → J → J → J → ℝ) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
      (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) (D : ℝ), 0 ≤ D →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ v : Fin 3 → J → SchwartzMap E ℂ,
        ‖semilinearCubicMultilinearMap q b hb hom v‖ₑ ≤
          K * ENNReal.ofReal D * ∏ i, semilinearGradientNorm (v i) := by
  obtain ⟨K,hK,est⟩ := semilinear_cubic_L3_sphere_bound q
  refine ⟨K,hK,?_⟩
  intro b hb hom D hD jet v
  rw [semilinear_cubic_multilinear_apply,Fin.prod_univ_three]
  exact est b hb hom D hD jet (v 0) (v 1) (v 2)

end Burnett.A02.FrequencySplit
