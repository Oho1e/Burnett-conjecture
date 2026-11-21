import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletDyadicSquare
import Burnett.Analysis.PrincipalEnergy.Fourier.DyadicKernel

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier
open Burnett.Microlocal.AngularDyadicKernel
  (inverseFourier_dilation inverseFourier_mul_fourier_eq_convolution)
open Burnett.Microlocal.AngularCommutator
  (fourierL2Equiv_eq_fourier_ae_of_integrable fourierL2Equiv_symm_eq_inverse_ae_of_integrable)
open scoped FourierTransform BigOperators InnerProduct

def waveletSymbol (ψ : SchwartzMap Space ℂ) (s : ℝ) : BoundedSymbol Space where
  toFun := fun ξ => compactWaveletFrequency ψ (s • ξ)
  measurable := ((compactWaveletFrequency ψ).continuous.comp
    (continuous_const.smul continuous_id)).aestronglyMeasurable
  bound := SchwartzMap.seminorm ℝ 0 0 (compactWaveletFrequency ψ)
  bound_nonneg := apply_nonneg _ _
  norm_le := fun ξ => SchwartzMap.norm_le_seminorm ℝ (compactWaveletFrequency ψ) (s • ξ)

private theorem inverse_waveletSymbol (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) :
    𝓕⁻ (waveletSymbol ψ s : Space → ℂ) = compactWaveletKernel ψ s := by
  funext z
  change 𝓕⁻ (fun ξ => compactWaveletFrequency ψ (s • ξ)) z = _
  have hInv : 𝓕⁻ (compactWaveletFrequency ψ : Space → ℂ) = (ψ : Space → ℂ) :=
    ψ.continuous.fourier_inversion ψ.integrable (compactWaveletFrequency ψ).integrable
  simpa only [inv_inv, inv_pow, hInv, compactWaveletKernel] using
    (inverseFourier_dilation s⁻¹ (inv_pos.mpr hs) (compactWaveletFrequency ψ : Space → ℂ) z)

private theorem waveletSymbol_integrable (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) :
    Integrable (waveletSymbol ψ s : Space → ℂ) volume :=
  (compactWaveletFrequency ψ).integrable.comp_smul hs.ne'

private theorem waveletFourier_product_integrable (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    (f : Space → ℂ) (hf : Integrable f volume) :
    Integrable (fun ξ => waveletSymbol ψ s ξ * 𝓕 f ξ) volume := by
  have hFourier : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous (L := innerₗ Space)
      Real.continuous_fourierChar continuous_inner hf
  have hBdd : ∃ C : ℝ, ∀ ξ, ‖𝓕 f ξ‖ ≤ C :=
    ⟨∫ y, ‖f y‖, fun ξ => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _⟩
  simpa only [mul_comm] using (waveletSymbol_integrable ψ s hs).bdd_mul
    hFourier.aestronglyMeasurable hBdd

private theorem waveletAction_eq_inverse (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    (f : Space → ℂ) (hf : Integrable f volume) :
    𝓕⁻ (fun ξ => waveletSymbol ψ s ξ * 𝓕 f ξ) = compactWaveletAction ψ s f := by
  funext x
  rw [inverseFourier_mul_fourier_eq_convolution (waveletSymbol ψ s : Space → ℂ) f
    (waveletSymbol_integrable ψ s hs) hf, inverse_waveletSymbol ψ s hs]
  rfl

/-- Actual convolution outputs are continuous for every integrable input. -/
theorem compactWaveletAction_continuous (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    (f : Space → ℂ) (hf : Integrable f volume) : Continuous (compactWaveletAction ψ s f) := by
  rw [← waveletAction_eq_inverse ψ s hs f hf]
  refine VectorFourier.fourierIntegral_continuous (L := -innerₗ Space)
    Real.continuous_fourierChar ?_ (waveletFourier_product_integrable ψ s hs f hf)
  simpa only [LinearMap.neg_apply] using
    (continuous_inner : Continuous (fun z : Space × Space => inner ℝ z.1 z.2)).neg

/-- The Fourier L² wavelet multiplier represents the original physical
convolution, including for nonsmooth spatially localized inputs. -/
theorem waveletMultiplier_ae_eq_action (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    (f : Space → ℂ) (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    (fourierMultiplier (waveletSymbol ψ s) (hf₂.toLp f) : Space → ℂ) =ᵐ[volume]
      compactWaveletAction ψ s f := by
  let m := waveletSymbol ψ s
  let u := fourierL2Equiv (hf₂.toLp f)
  let F (ξ : Space) := m ξ * 𝓕 f ξ
  have hF₁ : Integrable F volume := waveletFourier_product_integrable ψ s hs f hf₁
  have hFourierAE : (u : Space → ℂ) =ᵐ[volume] 𝓕 f :=
    fourierL2Equiv_eq_fourier_ae_of_integrable f hf₁ hf₂
  have hF₂ : MemLp F 2 volume := MemLp.ae_eq
    (hFourierAE.mono fun ξ hξ => congrArg (fun z => m ξ * z) hξ) (symbol_product_memLp m u)
  have hL2 : symbolL2 m u = hF₂.toLp F := by
    apply Lp.ext
    filter_upwards [symbolL2_ae m u, MemLp.coeFn_toLp hF₂, hFourierAE] with ξ h₁ h₂ h₃
    rw [h₁,h₂]
    exact congrArg (fun z => m ξ * z) h₃
  rw [fourierMultiplier_apply, show waveletSymbol ψ s = m from rfl, hL2]
  have hInv := fourierL2Equiv_symm_eq_inverse_ae_of_integrable F hF₁ hF₂
  exact hInv.trans (EventuallyEq.of_eq (waveletAction_eq_inverse ψ s hs f hf₁))

private theorem norm_waveletMultiplier_sq (ψ : SchwartzMap Space ℂ) (s : ℝ)
    (u : ComplexL2 Space) :
    ‖fourierMultiplier (waveletSymbol ψ s) u‖^2 =
      ∫ ξ, ‖waveletSymbol ψ s ξ‖^2 * ‖fourierL2Equiv u ξ‖^2 := by
  rw [fourierMultiplier_apply, LinearIsometryEquiv.norm_map, l2_norm_sq_integral]
  refine integral_congr_ae ((symbolL2_ae (waveletSymbol ψ s) (fourierL2Equiv u)).mono ?_)
  intro ξ hξ
  change ‖symbolL2 (waveletSymbol ψ s) (fourierL2Equiv u) ξ‖^2 =
    ‖waveletSymbol ψ s ξ‖^2 * ‖fourierL2Equiv u ξ‖^2
  rw [hξ, norm_mul, mul_pow]

/-- The sum of the squared norms of the actual L² wavelet operators is
uniform in the starting scale and in arbitrary finite selections of scales. -/
theorem exists_waveletMultiplier_square_bound (ψ : SchwartzMap Space ℂ)
    (hMean : (∫ z, ψ z) = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (t : ℝ), 0<t → ∀ (J : Finset ℕ) (u : ComplexL2 Space),
      (∑ j ∈ J, ‖fourierMultiplier (waveletSymbol ψ (compactWaveletScale t j)) u‖^2) ≤
        D * ‖u‖^2 := by
  obtain ⟨D,hD,hBound⟩ := exists_compactWaveletFrequency_square_bound ψ hMean
  refine ⟨D,hD,fun t ht J u => ?_⟩
  let v := fourierL2Equiv u
  let m (j : ℕ) := waveletSymbol ψ (compactWaveletScale t j)
  have hTerm (j : ℕ) : Integrable (fun ξ => ‖m j ξ‖^2 * ‖v ξ‖^2) volume := by
    have h := (symbol_product_memLp (m j) v).integrable_norm_pow (p := 2) (by decide)
    simpa only [norm_mul,mul_pow] using h
  have hv : Integrable (fun ξ => ‖v ξ‖^2) volume := (Lp.memLp v).integrable_norm_pow (p := 2) (by decide)
  have hEq : D * ‖u‖^2 = ∫ ξ, D * ‖v ξ‖^2 := by
    rw [← LinearIsometryEquiv.norm_map (fourierL2Equiv (V := Space)) u, l2_norm_sq_integral,
      integral_const_mul]
  simp_rw [norm_waveletMultiplier_sq]
  rw [← integral_finset_sum J (fun j _ => hTerm j), hEq]
  apply integral_mono (integrable_finset_sum J (fun j _ => hTerm j)) (hv.const_mul D)
  intro ξ
  change (∑ j ∈ J, ‖m j ξ‖^2 * ‖v ξ‖^2) ≤ D * ‖v ξ‖^2
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hBound t ht J ξ) (sq_nonneg _)

/-- The physical wavelet convolutions have a uniform finite L² square sum.
The L¹ assumption permits a direct pointwise integral representation. -/
theorem exists_compactWaveletAction_square_bound (ψ : SchwartzMap Space ℂ)
    (hMean : (∫ z, ψ z) = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (t : ℝ), 0<t → ∀ (J : Finset ℕ) (f : Space → ℂ),
      Integrable f volume → MemLp f 2 volume →
        (∀ j, MemLp (compactWaveletAction ψ (compactWaveletScale t j) f) 2 volume) ∧
        (∑ j ∈ J, ∫ x, ‖compactWaveletAction ψ (compactWaveletScale t j) f x‖^2) ≤
          D * ∫ x, ‖f x‖^2 := by
  obtain ⟨D,hD,hBound⟩ := exists_waveletMultiplier_square_bound ψ hMean
  refine ⟨D,hD,fun t ht J f hf₁ hf₂ => ?_⟩
  have hAE (j : ℕ) := waveletMultiplier_ae_eq_action ψ (compactWaveletScale t j)
    (div_pos ht (pow_pos (by norm_num) _)) f hf₁ hf₂
  refine ⟨fun j => MemLp.ae_eq (hAE j) (Lp.memLp _),?_⟩
  have hEq (j : ℕ) : (∫ x, ‖compactWaveletAction ψ (compactWaveletScale t j) f x‖^2) =
    ‖fourierMultiplier (waveletSymbol ψ (compactWaveletScale t j)) (hf₂.toLp f)‖^2 := by
    rw [l2_norm_sq_integral]
    exact integral_congr_ae ((hAE j).symm.fun_comp (fun z : ℂ => ‖z‖^2))
  simp_rw [hEq]
  have hInput : (∫ x, ‖f x‖^2) = ‖hf₂.toLp f‖^2 := by
    rw [l2_norm_sq_integral]
    exact integral_congr_ae ((MemLp.coeFn_toLp hf₂).symm.fun_comp (fun z : ℂ => ‖z‖^2))
  rw [hInput]
  exact hBound t ht J (hf₂.toLp f)

end Burnett.Analysis.CarlesonEmbedding
