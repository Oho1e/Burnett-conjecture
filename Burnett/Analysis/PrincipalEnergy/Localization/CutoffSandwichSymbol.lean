import Burnett.Analysis.PrincipalEnergy.Commutator.CompactBaseCommutatorL2

set_option autoImplicit false
set_option maxHeartbeats 5200000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Microlocal.AngularCommutator (fourier_mul_inverse_eq_integral)
open scoped FourierTransform ComplexConjugate

/-- The left symbol of the actual two-sided Schwartz cutoff. -/
def cutoffSandwichSymbol (a : Space → Space → ℂ) (χ : SchwartzMap Space ℂ) (x ξ : Space) : ℂ :=
  χ x*(∫ η, (Real.fourierChar (inner ℝ η x)) • (a x (ξ+η)*𝓕 (χ : Space → ℂ) η))

private theorem fourier_scalarSchwartzProduct (χ f : SchwartzMap Space ℂ) (ζ : Space) :
    𝓕 (scalarSchwartzProduct χ f : Space → ℂ) ζ =
      ∫ ξ, 𝓕 (χ : Space → ℂ) (ζ-ξ)*𝓕 (f : Space → ℂ) ξ := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  have hInv : 𝓕⁻ (F : Space → ℂ)=(f : Space → ℂ) :=
    f.continuous.fourier_inversion f.integrable F.integrable
  have h := fourier_mul_inverse_eq_integral (χ : Space → ℂ) (F : Space → ℂ)
    χ.integrable F.integrable ζ
  rw [hInv] at h
  exact h

/-- The cutoff sandwich is the exact Fourier left action, with the original
Schwartz products and the same Fourier conversion in both slots. -/
theorem firstOrderAction_cutoffSandwichSymbol {a : Space → Space → ℂ} (ha : FrequencyOrderOne a)
    (χ f : SchwartzMap Space ℂ) (x : Space) :
    firstOrderAction (cutoffSandwichSymbol a χ) f x =
      χ x*firstOrderAction a (scalarSchwartzProduct χ f) x := by
  let V : Measure Space := volume
  let P (u : Space) : ℂ := ((Real.fourierChar (inner ℝ u x)) : ℂ)
  let U := SchwartzMap.fourierTransformCLM ℂ χ
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let A (ζ ξ : Space) : ℂ := P ζ*(a x ζ*(U (ζ-ξ)*F ξ))
  have hP (u : Space) : ‖P u‖=1 := Circle.norm_coe _
  have hPadd (u v : Space) : P (u+v)=P u*P v := by
    simp only [P,inner_add_left,Real.fourierChar.map_add_eq_mul,Circle.coe_mul]
  have hPM : Continuous P := by
    have hCIR : Continuous (fun z : Circle => (z:ℂ)) := continuous_subtype_val
    exact hCIR.comp (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const))
  have hAc : Continuous (uncurry A) :=
    (hPM.comp continuous_fst).mul (((ha.smooth x).continuous.comp continuous_fst).mul
      ((U.continuous.comp (continuous_fst.sub continuous_snd)).mul (F.continuous.comp continuous_snd)))
  let S (p : Space × Space) := (p.1+p.2,p.2)
  have hS : MeasurePreserving S (V.prod V) (V.prod V) := measurePreserving_add_prod V V
  obtain ⟨C,hC,hFreq⟩ := ha.order 0
  have hGrowth (ξ : Space) : ‖a x ξ‖≤C*(1+‖ξ‖) := by
    simpa only [pow_zero,mul_one,norm_iteratedFDeriv_zero] using hFreq x ξ
  have hL (z : SchwartzMap Space ℂ) : Integrable (fun u => (1+‖u‖)*‖z u‖) V := by
    have h := z.integrable.norm.add (z.integrable_pow_mul (volume : Measure Space) 1)
    simpa only [pow_one,add_mul,one_mul] using h
  have hB : Integrable ((uncurry A) ∘ S) (V.prod V) := by
    refine (((hL U).mul_prod (hL F)).const_mul C).mono'
      (hAc.comp ((continuous_fst.add continuous_snd).prodMk continuous_snd)).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    change ‖A (p.1+p.2) p.2‖≤C*(((1+‖p.1‖)*‖U p.1‖)*((1+‖p.2‖)*‖F p.2‖))
    have hSub : p.1+p.2-p.2=p.1 := by abel
    have hL := norm_add_le p.1 p.2
    have hW : 1+‖p.1+p.2‖≤(1+‖p.1‖)*(1+‖p.2‖) := by
      nlinarith only [hL,mul_nonneg (norm_nonneg p.1) (norm_nonneg p.2)]
    simp only [A,hSub,norm_mul,hP,one_mul]
    calc
      _ ≤ (C*((1+‖p.1‖)*(1+‖p.2‖)))*(‖U p.1‖*‖F p.2‖) := by
        exact mul_le_mul_of_nonneg_right ((hGrowth _).trans (mul_le_mul_of_nonneg_left hW hC))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  have hA : Integrable (uncurry A) (V.prod V) := (hS.integrable_comp hAc.aestronglyMeasurable).mp hB
  have hMove : (∫ p, A (p.1+p.2) p.2 ∂(V.prod V))=∫ p, A p.1 p.2 ∂(V.prod V) := by
    change (∫ p, uncurry A (S p) ∂(V.prod V))=_
    rw [← integral_map (f := uncurry A) hS.measurable.aemeasurable
      (by rw [hS.map_eq]; exact hAc.aestronglyMeasurable),hS.map_eq]
    rfl
  calc
    _ = χ x*(∫ ξ, ∫ η, A (η+ξ) ξ) := by
      have hPull : χ x*(∫ ξ, ∫ η, A (η+ξ) ξ)=(∫ ξ, χ x*(∫ η, A (η+ξ) ξ)) :=
        (integral_const_mul (χ x) (fun ξ => ∫ η, A (η+ξ) ξ)).symm
      rw [firstOrderAction,Real.fourierIntegralInv_eq,hPull]
      apply integral_congr_ae
      filter_upwards with ξ
      change P ξ*((χ x*(∫ η, P η*(a x (ξ+η)*U η)))*F ξ)=χ x*(∫ η, A (η+ξ) ξ)
      calc
        _ = (P ξ*χ x*F ξ)*(∫ η, P η*(a x (ξ+η)*U η)) := by ring
        _ = ∫ η, (P ξ*χ x*F ξ)*(P η*(a x (ξ+η)*U η)) := (integral_const_mul _ _).symm
        _ = _ := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with η
          dsimp only [A]
          rw [hPadd,add_sub_cancel_right,add_comm ξ η]
          ring
    _ = χ x*(∫ p, A (p.1+p.2) p.2 ∂(V.prod V)) := by
      exact congrArg (fun b : ℂ => χ x*b) (integral_prod_symm _ hB).symm
    _ = χ x*(∫ p, A p.1 p.2 ∂(V.prod V)) := by rw [hMove]
    _ = χ x*(∫ ζ, ∫ ξ, A ζ ξ) := by rw [integral_integral hA]
    _ = _ := by
      rw [firstOrderAction,Real.fourierIntegralInv_eq]
      congr 1
      apply integral_congr_ae
      filter_upwards with ζ
      rw [fourier_scalarSchwartzProduct]
      change (∫ ξ, A ζ ξ)=(P ζ)*(a x ζ*(∫ ξ, U (ζ-ξ)*F ξ))
      rw [← mul_assoc,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ξ
      dsimp only [A]
      ring

theorem cutoffSandwichSymbol_base_support {a : Space → Space → ℂ} (χ : SchwartzMap Space ℂ)
    (ξ : Space) : tsupport (fun x => cutoffSandwichSymbol a χ x ξ) ⊆ tsupport (χ : Space → ℂ) := by
  apply closure_mono
  intro x hx hχ
  apply hx
  change cutoffSandwichSymbol a χ x ξ=0
  rw [cutoffSandwichSymbol,hχ,zero_mul]

theorem cutoffSandwichSymbol_formalSymmetry {a : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (hSym : FirstOrderFormalSymmetry a) (χ : SchwartzMap Space ℂ)
    (hReal : ∀ x, conj (χ x)=χ x) : FirstOrderFormalSymmetry (cutoffSandwichSymbol a χ) := by
  intro u v
  simp_rw [firstOrderAction_cutoffSandwichSymbol ha]
  calc
    _ = ∫ x, conj (scalarSchwartzProduct χ u x)*firstOrderAction a (scalarSchwartzProduct χ v) x := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [scalarSchwartzProduct_apply,map_mul,hReal]
      ring
    _ = ∫ x, conj (firstOrderAction a (scalarSchwartzProduct χ u) x)*scalarSchwartzProduct χ v x :=
      hSym (scalarSchwartzProduct χ u) (scalarSchwartzProduct χ v)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [scalarSchwartzProduct_apply,map_mul,hReal]
      ring

end Burnett.Analysis.CarlesonEmbedding
