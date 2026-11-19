import Burnett.Analysis.Microlocal.AngularCommutator.FrequencyKernel
import Burnett.Analysis.Fourier.Projection
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The angular commutator on complex L²

The Fourier isometry and its inverse agree with the corresponding
integrals on integrable representatives. This identifies the actual
project multiplier commutator with the high-input kernel.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AngularCommutator

open MeasureTheory Burnett.Fourier
open scoped FourierTransform ContDiff ComplexConjugate ENNReal RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The actual project Fourier isometry agrees with the Fourier integral
on the intersection of L¹ and L². The proof uses real smooth tests and
does not require a simultaneous L¹/L² approximation theorem. -/
theorem fourierL2Equiv_eq_fourier_ae_of_integrable (f : V → ℂ)
    (h1 : Integrable f (volume : Measure V)) (h2 : MemLp f 2 (volume : Measure V)) :
    (fourierL2Equiv (h2.toLp f) : V → ℂ) =ᵐ[volume] 𝓕 f := by
  let T := fourierL2Equiv (V := V)
  have hc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner h1
  have hg := (Lp.memLp (T (h2.toLp f))).locallyIntegrable (by norm_num)
  apply ae_eq_of_integral_contDiff_smul_eq hg hc.locallyIntegrable
  intro q hqs hqc
  let ψ : SchwartzMap V ℂ := (hqc.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hqs)
  have hψ (x : V) : ψ x = (q x : ℂ) := rfl
  have hconjψ (x : V) : conj (ψ x) = ψ x := by rw [hψ, Complex.conj_ofReal]
  have hconjF (x : V) : conj (𝓕⁻ (ψ : V → ℂ) x) = 𝓕 (ψ : V → ℂ) x := by
    have h := fourier_conj_eq_conj_inverse (ψ : V → ℂ) x
    simp only [hconjψ] at h
    exact h.symm
  let p := ψ.toLp 2 (volume : Measure V)
  have hp := ψ.coeFn_toLp 2 (volume : Measure V)
  have htp := fourierL2Equiv_symm_schwartz_ae ψ
  have hfp := h2.coeFn_toLp
  have hH := T.inner_map_map (T.symm p) (h2.toLp f)
  rw [T.apply_symm_apply] at hH
  calc
    (∫ x, q x • (T (h2.toLp f) : V → ℂ) x) =
        inner ℂ p (T (h2.toLp f)) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hp] with x hx
      rw [RCLike.inner_apply', hx, hconjψ, hψ, Complex.real_smul]
    _ = inner ℂ (T.symm p) (h2.toLp f) := hH
    _ = ∫ x, f x * (𝓕 (ψ : V → ℂ)) x := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [htp, hfp] with x hx hy
      rw [RCLike.inner_apply, hx, hy, hconjF]
    _ = ∫ x, (𝓕 f) x * ψ x :=
      (fourier_integral_pairing f (ψ : V → ℂ) h1 ψ.integrable).symm
    _ = ∫ x, q x • (𝓕 f) x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hψ, Complex.real_smul, mul_comm]

end Burnett.Microlocal.AngularCommutator

namespace Burnett.Microlocal.AngularCommutator

open MeasureTheory Burnett.Fourier
open scoped FourierTransform ContDiff ComplexConjugate ENNReal RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The inverse of the actual project Fourier isometry agrees with the
inverse Fourier integral on the intersection of L¹ and L². -/
theorem fourierL2Equiv_symm_eq_inverse_ae_of_integrable (f : V → ℂ)
    (h1 : Integrable f (volume : Measure V)) (h2 : MemLp f 2 (volume : Measure V)) :
    (fourierL2Equiv.symm (h2.toLp f) : V → ℂ) =ᵐ[volume] 𝓕⁻ f := by
  let T := fourierL2Equiv (V := V)
  have hcf : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner h1
  have hc : Continuous (𝓕⁻ f) := by
    rw [show 𝓕⁻ f = (𝓕 f) ∘ (fun x : V => -x) from
      funext (Real.fourierIntegralInv_eq_fourierIntegral_neg f)]
    exact hcf.comp continuous_neg
  have hg := (Lp.memLp (T.symm (h2.toLp f))).locallyIntegrable (by norm_num)
  apply ae_eq_of_integral_contDiff_smul_eq hg hc.locallyIntegrable
  intro q hqs hqc
  let ψ : SchwartzMap V ℂ := (hqc.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hqs)
  have hψ (x : V) : ψ x = (q x : ℂ) := rfl
  have hconjψ (x : V) : conj (ψ x) = ψ x := by rw [hψ, Complex.conj_ofReal]
  have hconjF (x : V) : conj (𝓕 (ψ : V → ℂ) x) = 𝓕⁻ (ψ : V → ℂ) x := by
    have h := fourier_conj_eq_conj_inverse (ψ : V → ℂ) x
    simp only [hconjψ] at h
    rw [h, Complex.conj_conj]
  have hfC : Integrable (fun x => conj (f x)) (volume : Measure V) := by
    apply h1.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable h1.aestronglyMeasurable)
    filter_upwards with x
    rw [Complex.norm_conj]
  have hpair := congrArg conj
    (fourier_integral_pairing (fun x => conj (f x)) (ψ : V → ℂ) hfC ψ.integrable)
  have hconjf (x : V) : conj (𝓕 (fun x => conj (f x)) x) = 𝓕⁻ f x := by
    rw [fourier_conj_eq_conj_inverse f x, Complex.conj_conj]
  simp only [← integral_conj, map_mul, hconjf, hconjψ, Complex.conj_conj, hconjF] at hpair
  let p := ψ.toLp 2 (volume : Measure V)
  have hp := ψ.coeFn_toLp 2 (volume : Measure V)
  have htp := fourierL2Equiv_schwartz_ae ψ
  have hfp := h2.coeFn_toLp
  have hH := (T.inner_map_map p (T.symm (h2.toLp f))).symm
  rw [T.apply_symm_apply] at hH
  calc
    (∫ x, q x • (T.symm (h2.toLp f) : V → ℂ) x) =
        inner ℂ p (T.symm (h2.toLp f)) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hp] with x hx
      rw [RCLike.inner_apply', hx, hconjψ, hψ, Complex.real_smul]
    _ = inner ℂ (T p) (h2.toLp f) := hH
    _ = ∫ x, f x * (𝓕⁻ (ψ : V → ℂ)) x := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [htp, hfp] with x hx hy
      rw [RCLike.inner_apply, hx, hy, hconjF]
    _ = ∫ x, (𝓕⁻ f) x * ψ x := hpair.symm
    _ = ∫ x, q x • (𝓕⁻ f) x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hψ, Complex.real_smul, mul_comm]

end Burnett.Microlocal.AngularCommutator

namespace Burnett.Microlocal.AngularCommutator

open MeasureTheory Burnett.Fourier
open scoped FourierTransform ContDiff ComplexConjugate ENNReal RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The commutator between the actual project Fourier multiplier and actual
multiplication by the scalar cutoff in physical coordinates. -/
def cutoffCommutator (m χ : BoundedSymbol V) : ComplexL2 V →L[ℂ] ComplexL2 V :=
  (fourierMultiplier m).comp (symbolCLM χ) - (symbolCLM χ).comp (fourierMultiplier m)

private theorem fourierL2_cutoff_inverse_ae
    (χ : BoundedSymbol V) (hχ : Integrable (χ : V → ℂ) (volume : Measure V))
    (F : V → ℂ) (hF1 : Integrable F (volume : Measure V)) (hF2 : MemLp F 2 (volume : Measure V)) :
    (fourierL2Equiv (symbolL2 χ (fourierL2Equiv.symm (hF2.toLp F))) : V → ℂ)
      =ᵐ[volume] 𝓕 (fun x => χ x * (𝓕⁻ F) x) := by
  let u := fourierL2Equiv.symm (hF2.toLp F)
  let v := symbolL2 χ u
  have hU : (u : V → ℂ) =ᵐ[volume] 𝓕⁻ F :=
    fourierL2Equiv_symm_eq_inverse_ae_of_integrable F hF1 hF2
  have hv : (v : V → ℂ) =ᵐ[volume] (fun x => χ x * (𝓕⁻ F) x) := by
    filter_upwards [symbolL2_ae χ u, hU] with x hx hy
    rw [hx, hy]
  have h₂ := MemLp.ae_eq hv (Lp.memLp v)
  have h₁ : Integrable (fun x => χ x * (𝓕⁻ F) x) (volume : Measure V) := by
    have hnorm (x : V) : ‖(𝓕⁻ F) x‖ ≤ ∫ y, ‖F y‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (-innerₗ V) F x
    have h := hχ.bdd_mul ((Lp.aestronglyMeasurable u).congr hU) ⟨∫ y, ‖F y‖, hnorm⟩
    simpa only [mul_comm] using h
  have hev : v = h₂.toLp (fun x => χ x * (𝓕⁻ F) x) := by
    apply Lp.ext
    exact hv.trans h₂.coeFn_toLp.symm
  rw [show symbolL2 χ (fourierL2Equiv.symm (hF2.toLp F)) = v from rfl, hev]
  exact fourierL2Equiv_eq_fourier_ae_of_integrable _ h₁ h₂

/-- On an L¹∩L² input spectrum the actual production L² commutator has the
same explicit Fourier kernel, with equality of representatives almost everywhere. -/
theorem fourierL2_cutoffCommutator_eq_kernel_ae
    (m χ : BoundedSymbol V) (hsχ : ContDiff ℝ ∞ (χ : V → ℂ))
    (hcχ : HasCompactSupport (χ : V → ℂ)) (hm : Measurable (m : V → ℂ))
    (F : V → ℂ) (hF1 : Integrable F (volume : Measure V)) (hF2 : MemLp F 2 (volume : Measure V)) :
    (fourierL2Equiv (cutoffCommutator m χ (fourierL2Equiv.symm (hF2.toLp F))) : V → ℂ)
      =ᵐ[volume] (fun x => ∫ y, ((m x - m y) * (𝓕 (χ : V → ℂ)) (x - y)) * F y) := by
  let u := fourierL2Equiv.symm (hF2.toLp F)
  let v := symbolL2 m (hF2.toLp F)
  have hv : (v : V → ℂ) =ᵐ[volume] (fun x => m x * F x) := by
    filter_upwards [symbolL2_ae m (hF2.toLp F), hF2.coeFn_toLp] with x hx hy
    rw [hx, hy]
  have hMF₂ := MemLp.ae_eq hv (Lp.memLp v)
  have hMF₁ := hF1.bdd_mul m.measurable ⟨m.bound, m.norm_le⟩
  have hχ : Integrable (χ : V → ℂ) (volume : Measure V) := (hcχ.toSchwartzMap hsχ).integrable
  have hMu : fourierMultiplier m u = fourierL2Equiv.symm (hMF₂.toLp (fun x => m x * F x)) := by
    rw [fourierMultiplier_apply]
    change fourierL2Equiv.symm (symbolL2 m (fourierL2Equiv (fourierL2Equiv.symm (hF2.toLp F)))) = _
    rw [fourierL2Equiv.apply_symm_apply]
    apply congrArg fourierL2Equiv.symm
    apply Lp.ext
    exact hv.trans hMF₂.coeFn_toLp.symm
  change (fourierL2Equiv (fourierMultiplier m (symbolL2 χ u) -
    symbolL2 χ (fourierMultiplier m u)) : V → ℂ) =ᵐ[volume] _
  rw [map_sub, fourier_fourierMultiplier, hMu]
  let a := symbolL2 m (fourierL2Equiv (symbolL2 χ u))
  let b := fourierL2Equiv (symbolL2 χ (fourierL2Equiv.symm (hMF₂.toLp (fun x => m x * F x))))
  filter_upwards [Lp.coeFn_sub a b, symbolL2_ae m (fourierL2Equiv (symbolL2 χ u)),
      fourierL2_cutoff_inverse_ae χ hχ F hF1 hF2,
      fourierL2_cutoff_inverse_ae χ hχ (fun x => m x * F x) hMF₁ hMF₂]
    with x hd ha hf hh
  rw [hd]
  change a x - b x = _
  rw [ha, hf, hh]
  exact fourier_commutator_eq_kernel m χ F hm m.bound m.norm_le hsχ hcχ hF1 x

end Burnett.Microlocal.AngularCommutator
