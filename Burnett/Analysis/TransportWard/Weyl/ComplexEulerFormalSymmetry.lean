import Burnett.Analysis.TransportWard.Weyl.LinearizedEulerSymmetry
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 3100000
set_option maxRecDepth 2300

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter Set MeasureTheory Burnett.Geometry ConnectionDifference
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.RicciSymbol Burnett.V02.EinsteinHilbert
open scoped ContDiff BigOperators ComplexConjugate Matrix.Norms.Elementwise

open private integrableOn_and_integral_coordinateDivergence_eq_zero from Burnett.Analysis.TransportWard.Weyl.EulerActionIntegral

local notation "E₀" => CoordinateSpace

private theorem integrableOn_linearizedDensityEulerRealPair
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g h k : E₀ → ι → ℝ) {U K : Set E₀}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U) (hk : ContDiffOn ℝ ∞ k U)
    (hn : ∀ y ∈ U, Matrix.det (assembleMetricComponents S (g y)) ≠ 0)
    (hk0 : ∀ y ∈ U \ K, k y = 0) :
    IntegrableOn (fun y => ∑ i, k y i * linearizedCoordinateDensityEuler S g h y i) U volume := by
  let V := linearizedEulerBoundaryVector S g h k
  let A (y : E₀) := ∑ i, k y i * linearizedCoordinateDensityEuler S g h y i
  have hz (y : E₀) (hy : y ∈ U \ K) (a : Index) : V y a = 0 := by
    simp only [V,linearizedEulerBoundaryVector,eulerVariationBoundaryVector,hk0 y hy,
      Pi.zero_apply,zero_mul,Finset.sum_const_zero,deriv_const]
  have hD := integrableOn_and_integral_coordinateDivergence_eq_zero hU hK hKU V
    (contDiffOn_linearizedEulerBoundaryVector S g h k hU hg hh hk hn) hz
  have hH : IntegrableOn (coordinateActionHessianDensity S g h k) K (volume : Measure E₀) :=
    ((contDiffOn_coordinateActionHessianDensity S g h k hU hg hh hk hn).continuousOn.mono
      hKU).integrableOn_compact hK
  have hEq : EqOn (fun y => coordinateActionHessianDensity S g h k y - coordinateDivergence V y) A K :=
    fun y hy => (linearizedCoordinateDensityEuler_pairing_eq_hessian_sub_divergence S g h k hU hg hh hk y
      (hKU hy) (hn y (hKU hy))).symm
  have hHD : IntegrableOn (fun y => coordinateActionHessianDensity S g h k y - coordinateDivergence V y)
      K volume := hH.sub hD.1
  have hA : IntegrableOn A K volume := hHD.congr_fun hEq hK.measurableSet
  exact hA.of_forall_diff_eq_zero hU.measurableSet (fun y hy => by
    simp only [A,hk0 y hy,Pi.zero_apply,zero_mul,Finset.sum_const_zero])

/-- The complex Euler action is the complexification of the actual real
linearized density on the same field coordinates. -/
def complexLinearizedCoordinateDensityEuler {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g : E₀ → ι → ℝ) (h : E₀ → ι → ℂ) (x : E₀) (i : ι) : ℂ :=
  ⟨linearizedCoordinateDensityEuler S g (fun y j => (h y j).re) x i,
    linearizedCoordinateDensityEuler S g (fun y j => (h y j).im) x i⟩

private theorem complexDensityEulerPairing_expand {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g : E₀ → ι → ℝ) (h k : E₀ → ι → ℂ) (x : E₀) :
    (∑ i, conj (k x i) * complexLinearizedCoordinateDensityEuler S g h x i) =
      (((∑ i, (k x i).re * linearizedCoordinateDensityEuler S g (fun y j => (h y j).re) x i) +
        ∑ i, (k x i).im * linearizedCoordinateDensityEuler S g (fun y j => (h y j).im) x i : ℝ) : ℂ) +
      Complex.I * (((∑ i, (k x i).re * linearizedCoordinateDensityEuler S g (fun y j => (h y j).im) x i) -
        ∑ i, (k x i).im * linearizedCoordinateDensityEuler S g (fun y j => (h y j).re) x i : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.re_sum,Complex.mul_re,Complex.conj_re,Complex.conj_im,
      complexLinearizedCoordinateDensityEuler,Complex.add_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero,
      neg_mul,sub_neg_eq_add,Finset.sum_add_distrib]
  · simp only [Complex.im_sum,Complex.mul_im,Complex.conj_re,Complex.conj_im,
      complexLinearizedCoordinateDensityEuler,Complex.add_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add,
      neg_mul,Finset.sum_add_distrib,Finset.sum_neg_distrib,sub_eq_add_neg]

/-- Complex formal symmetry of the full actual linearized Euler density
on the compact chart test domain used by the Weyl pair. -/
theorem integral_complexLinearizedCoordinateDensityEuler_hermitian
    {ι : Type*} [Fintype ι] (S : ι → Mat) (g : E₀ → ι → ℝ) (h k : E₀ → ι → ℂ)
    {U K : Set E₀} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U) (hk : ContDiffOn ℝ ∞ k U)
    (hn : ∀ y ∈ U, Matrix.det (assembleMetricComponents S (g y)) ≠ 0)
    (hh0 : ∀ y ∈ U \ K, h y = 0) (hk0 : ∀ y ∈ U \ K, k y = 0) :
    (∫ y in U, ∑ i, conj (k y i) * complexLinearizedCoordinateDensityEuler S g h y i) =
      conj (∫ y in U, ∑ i, conj (h y i) * complexLinearizedCoordinateDensityEuler S g k y i) := by
  let r (f : E₀ → ι → ℂ) (x : E₀) (i : ι) := (f x i).re
  let q (f : E₀ → ι → ℂ) (x : E₀) (i : ι) := (f x i).im
  have hr (f : E₀ → ι → ℂ) (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (r f) U :=
    contDiffOn_pi.mpr (fun i => Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hf i))
  have hq (f : E₀ → ι → ℂ) (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (q f) U :=
    contDiffOn_pi.mpr (fun i => Complex.imCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hf i))
  have hr0 (f : E₀ → ι → ℂ) (hf : ∀ y ∈ U \ K, f y = 0) : ∀ y ∈ U \ K, r f y = 0 := by
    intro y hy
    funext i
    simp only [r,hf y hy,Pi.zero_apply,Complex.zero_re]
  have hq0 (f : E₀ → ι → ℂ) (hf : ∀ y ∈ U \ K, f y = 0) : ∀ y ∈ U \ K, q f y = 0 := by
    intro y hy
    funext i
    simp only [q,hf y hy,Pi.zero_apply,Complex.zero_im]
  let A (f e : E₀ → ι → ℝ) (x : E₀) := ∑ i, e x i * linearizedCoordinateDensityEuler S g f x i
  let L (f e : E₀ → ι → ℝ) := ∫ x in U, A f e x
  have hInt (f e : E₀ → ι → ℝ) (hf : ContDiffOn ℝ ∞ f U) (he : ContDiffOn ℝ ∞ e U)
      (he0 : ∀ y ∈ U \ K, e y = 0) : Integrable (A f e) ((volume : Measure E₀).restrict U) :=
    integrableOn_linearizedDensityEulerRealPair S g f e hU hK hKU hg hf he hn he0
  have hLsym (f e : E₀ → ι → ℝ) (hf : ContDiffOn ℝ ∞ f U) (he : ContDiffOn ℝ ∞ e U)
      (hf0 : ∀ y ∈ U \ K, f y = 0) (he0 : ∀ y ∈ U \ K, e y = 0) : L f e = L e f :=
    integral_linearizedCoordinateDensityEuler_swap S g f e hU hK hKU hg hf he hn hf0 he0
  have hExp (f e : E₀ → ι → ℂ) (hF : ContDiffOn ℝ ∞ f U) (hE : ContDiffOn ℝ ∞ e U)
      (he0 : ∀ y ∈ U \ K, e y = 0) :
      (∫ y in U, ∑ i, conj (e y i) * complexLinearizedCoordinateDensityEuler S g f y i) =
      ((L (r f) (r e) + L (q f) (q e) : ℝ) : ℂ) +
        Complex.I * ((L (q f) (r e) - L (r f) (q e) : ℝ) : ℂ) := by
    have hRR := hInt (r f) (r e) (hr f hF) (hr e hE) (hr0 e he0)
    have hQQ := hInt (q f) (q e) (hq f hF) (hq e hE) (hq0 e he0)
    have hQR := hInt (q f) (r e) (hq f hF) (hr e hE) (hr0 e he0)
    have hRQ := hInt (r f) (q e) (hr f hF) (hq e hE) (hq0 e he0)
    let AR (y : E₀) := A (r f) (r e) y + A (q f) (q e) y
    let AI (y : E₀) := A (q f) (r e) y - A (r f) (q e) y
    have hIR : Integrable (fun y => (AR y : ℂ)) ((volume : Measure E₀).restrict U) :=
      (hRR.add hQQ).ofReal
    have hII : Integrable (fun y => (AI y : ℂ)) ((volume : Measure E₀).restrict U) :=
      (hQR.sub hRQ).ofReal
    have hRI : (∫ y in U, (AR y : ℂ)) = ((L (r f) (r e) + L (q f) (q e) : ℝ) : ℂ) := by
      calc
        (∫ y in U, (AR y : ℂ)) = Complex.ofReal (∫ y in U, AR y) :=
          integral_complex_ofReal (f := AR) (μ := (volume : Measure E₀).restrict U)
        _ = _ := congrArg Complex.ofReal (integral_add hRR hQQ)
    have hII' : (∫ y in U, (AI y : ℂ)) = ((L (q f) (r e) - L (r f) (q e) : ℝ) : ℂ) := by
      calc
        (∫ y in U, (AI y : ℂ)) = Complex.ofReal (∫ y in U, AI y) :=
          integral_complex_ofReal (f := AI) (μ := (volume : Measure E₀).restrict U)
        _ = _ := congrArg Complex.ofReal (integral_sub hQR hRQ)
    simp_rw [complexDensityEulerPairing_expand]
    change (∫ y in U, (AR y : ℂ) + Complex.I * (AI y : ℂ)) = _
    rw [integral_add hIR (hII.const_mul Complex.I),integral_const_mul,hRI,hII']
  rw [hExp h k hh hk hk0, hExp k h hk hh hh0]
  rw [hLsym (r k) (r h) (hr k hk) (hr h hh) (hr0 k hk0) (hr0 h hh0),
    hLsym (q k) (q h) (hq k hk) (hq h hh) (hq0 k hk0) (hq0 h hh0),
    hLsym (q k) (r h) (hq k hk) (hr h hh) (hq0 k hk0) (hr0 h hh0),
    hLsym (r k) (q h) (hr k hk) (hq h hh) (hr0 k hk0) (hq0 h hh0)]
  simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
  push_cast
  ring

end Burnett.V03.Palatini
