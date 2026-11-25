import Burnett.Analysis.CubicEnergy.AngularHarmonics.OriginalAngularExpansion
import Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 9000000

noncomputable section

namespace Burnett.A07

open Burnett.A06 Burnett.A02.FrequencySplit MeasureTheory Metric Set Filter
open scoped ContDiff ComplexConjugate

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _

/-- The symbol with the actual spherical multiplier still in the low frequency slot. -/
def angularModeSymbol (η χ : ℝ → ℝ) (F : Joint × RotationSpace → ℂ)
    (i : SphereHarmonicIndex) (x : Joint) : ℂ :=
  (sphereHarmonicMultiplierSymbol i.1 i.2 x.1 : ℂ) *
    regularizedLowCartesianSymbol η χ (jointSphereHarmonicCoefficientComplex F i) x

private theorem measurable_angularFactor (i : SphereHarmonicIndex) :
    Measurable (fun p : E => (sphereHarmonicMultiplierSymbol i.1 i.2 p : ℂ)) := by
  apply Complex.continuous_ofReal.measurable.comp
  change Measurable (spherePolynomialValue (sphereHarmonicPolynomialBasis i.1 i.2).val.val ∘
    roundSphereRadialNormalize)
  apply (spherePolynomialValue_contDiff _).continuous.measurable.comp
  exact measurable_norm.inv.smul measurable_id

private theorem ae_lowFrequency_ne_zero : ∀ᵐ x : Joint ∂volume, x.1 ≠ 0 := by
  rw [Measure.volume_eq_prod E E]
  have h : ∀ᵐ p : E ∂volume, p ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, setOf_eq_eq_singleton] using (measure_singleton (μ := volume) (0 : E))
  have hs : MeasurableSet {x : Joint | x.1 ≠ 0} :=
    (measurableSet_singleton (0 : E)).compl.preimage measurable_fst
  exact (Measure.ae_prod_iff_ae_ae hs).mpr (h.mono fun _ hp => Eventually.of_forall fun _ => hp)

private theorem angularModeSymbol_norm_le
    {η χ : ℝ → ℝ} {ρ M U V : ℝ} {F : Joint × RotationSpace → ℂ}
    (hρ : 0 ≤ ρ) (hcut : ∀ y ≥ ρ^2, χ y = 0)
    (hη : ∀ y ≥ 0, ‖η y‖ ≤ U) (hχ : ∀ y ≥ 0, ‖χ y‖ ≤ V)
    (hM : 0 ≤ M)
    (hcoef : ∀ i : SphereHarmonicIndex, ∀ z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1,
      ‖jointSphereHarmonicCoefficientComplex F i z‖ ≤ M / ((i.1 : ℝ) + 1)^12)
    (i : SphereHarmonicIndex) (x : Joint) (hx : x.1 ≠ 0) :
    ‖angularModeSymbol η χ F i x‖ ≤
      ((U*V*M*sphereEvaluationConstant) / ((i.1 : ℝ) + 1)^5) * (1 + ‖x.1‖ + ‖x.2‖) := by
  have hU : 0 ≤ U := (norm_nonneg _).trans (hη 0 le_rfl)
  have hV : 0 ≤ V := (norm_nonneg _).trans (hχ 0 le_rfl)
  have hC : 0 ≤ sphereEvaluationConstant := Real.sqrt_nonneg _
  let z := normalizedHighPair x
  let a := η ‖x.2‖ * ‖x.2‖ * χ (‖z.1‖^2)
  have hb : regularizedLowCartesianSymbol η χ (jointSphereHarmonicCoefficientComplex F i) x =
      a • jointSphereHarmonicCoefficientComplex F i z := by
    simp only [regularizedLowCartesianSymbol, lowCartesianSymbol, smul_smul, a, z, mul_assoc]
  by_cases ha : a = 0
  · simp only [angularModeSymbol, hb, ha, zero_smul, mul_zero, norm_zero]
    positivity
  have hq : x.2 ≠ 0 := by
    intro h
    apply ha
    simp [a, h]
  have hside : χ (‖z.1‖^2) ≠ 0 := by
    intro h
    apply ha
    simp [a, h]
  have hz : z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 := by
    refine ⟨mem_closedBall_zero_iff.mpr ?_, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hq)⟩
    by_contra! h
    exact hside (hcut _ (pow_le_pow_left₀ hρ h.le 2))
  let direction : RoundSphere3 := ⟨roundSphereRadialNormalize x.1,
    mem_sphere_zero_iff_norm.mpr (roundSphereRadialNormalize_norm hx)⟩
  have hmode : ‖(sphereHarmonicMultiplierSymbol i.1 i.2 x.1 : ℂ)‖ ≤
      sphereEvaluationConstant * ((i.1 : ℝ) + 1) := by
    rw [Complex.norm_real, sphereHarmonicMultiplierSymbol_eq i.1 i.2 hx]
    exact ((sphereHarmonicFamily i).norm_coe_le_norm direction).trans (norm_roundSphereHarmonic_le i)
  let d : ℝ := (i.1 : ℝ) + 1
  have hd : 1 ≤ d := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hquot : d / d^12 ≤ 1 / d^5 := by
    rw [div_le_div_iff₀ (by positivity : 0 < d^12) (by positivity : 0 < d^5),
      one_mul, ← pow_succ']
    exact pow_le_pow_right₀ hd (by norm_num)
  unfold angularModeSymbol
  rw [hb, norm_mul, norm_smul]
  simp only [a, norm_mul, norm_norm]
  calc
    _ ≤ (sphereEvaluationConstant*d) * (U*‖x.2‖*V * (M / d^12)) := by
      gcongr
      · exact hη _ (norm_nonneg _)
      · exact hχ _ (by positivity)
      · exact hcoef i z hz
    _ = (U*V*M*sphereEvaluationConstant) * (d/d^12) * ‖x.2‖ := by ring
    _ ≤ (U*V*M*sphereEvaluationConstant) * (1 / d^5) * (1 + ‖x.1‖ + ‖x.2‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hquot (by positivity))
        (by linarith [norm_nonneg x.1]) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The angular series can be integrated in the original radian Fourier pairing.
Each term still acts on the same original Schwartz low input through its exact symbol. -/
theorem originalRegularizedAngularPair_hasSum
    (η χ : ℝ → ℝ) {ρ M U V : ℝ} {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)}
    (hρ : 0 ≤ ρ) (hcut : ∀ y ≥ ρ^2, χ y = 0)
    (hη : ∀ y ≥ 0, ‖η y‖ ≤ U) (hχ : ∀ y ≥ 0, ‖χ y‖ ≤ V)
    (hF : ContinuousOn F W) (hW : (closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1) ×ˢ
      sphere (0 : RotationSpace) 1 ⊆ W) (hM : 0 ≤ M)
    (hcoef : ∀ i : SphereHarmonicIndex, ∀ z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1,
      ‖jointSphereHarmonicCoefficientComplex F i z‖ ≤ M / ((i.1 : ℝ) + 1)^12)
    (hmeas : ∀ i : SphereHarmonicIndex,
      Measurable (regularizedLowCartesianSymbol η χ (jointSphereHarmonicCoefficientComplex F i)))
    (f u w : SchwartzMap E ℂ) :
    HasSum (fun i => radianHighPair (angularModeSymbol η χ F i) f u w)
      (radianHighPair (originalRegularizedAngularSymbol η χ F) f u w) := by
  let A := U*V*M*sphereEvaluationConstant
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg ((norm_nonneg _).trans (hη 0 le_rfl))
    ((norm_nonneg _).trans (hχ 0 le_rfl))) hM) (Real.sqrt_nonneg _)
  let c (i : SphereHarmonicIndex) := A / ((i.1 : ℝ) + 1)^5
  let g₀ (x : Joint) := ((1 + ‖x.1‖ + ‖x.2‖ : ℝ) : ℂ)
  have h₀ : Measurable g₀ := Complex.continuous_ofReal.measurable.comp
    ((measurable_const.add (measurable_norm.comp measurable_fst)).add (measurable_norm.comp measurable_snd))
  have h₁ (p : Joint) : ‖g₀ p‖ = 1 + ‖p.1‖ + ‖p.2‖ :=
    Complex.norm_of_nonneg (by positivity)
  let G (p : Joint) := ‖radianHighPairWeight g₀ f u w p‖
  have hG : Integrable G := (integrable_radianHighPairWeight_of_orderOne g₀ h₀ 1 (by norm_num)
    (fun p => by rw [h₁, one_mul]) f u w).norm
  have hC : Summable c := (harmonic_series_estimate c hA (fun i =>
    (Real.norm_of_nonneg (show 0 ≤ c i from div_nonneg hA (by positivity))).le)).summable
  let weight (i : SphereHarmonicIndex) := radianHighPairWeight (angularModeSymbol η χ F i) f u w
  have hFourier (a : SchwartzMap E ℂ) : Measurable (radianFourier a) := by
    have hEq : radianFourier a = fun p => SchwartzMap.fourierTransformCLM ℂ a (tau⁻¹ • p) := by
      funext p
      have hτ : tau ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne'
      rw [SchwartzMap.fourierTransformCLM_apply, ← radianFourier_scaled, smul_smul,
        mul_inv_cancel₀ hτ, one_smul]
    rw [hEq]
    exact ((SchwartzMap.fourierTransformCLM ℂ a).continuous.comp
      (continuous_const.smul continuous_id)).measurable
  have hWeight (i : SphereHarmonicIndex) : AEStronglyMeasurable (weight i) := by
    have hs : Measurable (angularModeSymbol η χ F i) :=
      ((measurable_angularFactor i).comp measurable_fst).mul (hmeas i)
    exact (((hs.mul ((hFourier f).comp measurable_fst)).mul ((hFourier u).comp measurable_snd)).mul
      (Complex.continuous_conj.measurable.comp ((hFourier w).comp (measurable_snd.add measurable_fst)))).aestronglyMeasurable
  have hBound (i : SphereHarmonicIndex) : ∀ᵐ x ∂volume, ‖weight i x‖ ≤ c i * G x := by
    filter_upwards [ae_lowFrequency_ne_zero] with x hx
    simp only [weight, G, radianHighPairWeight, norm_mul]
    rw [h₁]
    have h := angularModeSymbol_norm_le hρ hcut hη hχ hM hcoef i x hx
    calc
      _ ≤ (c i * (1 + ‖x.1‖ + ‖x.2‖)) * ‖radianFourier f x.1‖ *
          ‖radianFourier u x.2‖ * ‖conj (radianFourier w (x.2 + x.1))‖ := by gcongr
      _ = _ := by ring
  have limits : ∀ᵐ x ∂volume, HasSum (fun i => weight i x)
      (radianHighPairWeight (originalRegularizedAngularSymbol η χ F) f u w x) := by
    filter_upwards [ae_lowFrequency_ne_zero] with x hx
    have point := originalRegularizedAngularSymbol_hasSum η χ hρ hcut hF hW hM hcoef x hx
    have result := point.mul_right (radianFourier f x.1 * radianFourier u x.2 * conj (radianFourier w (x.2 + x.1)))
    simpa only [weight, angularModeSymbol, radianHighPairWeight, mul_assoc] using result
  have hSum := hasSum_integral_of_dominated_convergence (fun i x => c i * G x) hWeight hBound
    (Eventually.of_forall fun x => hC.mul_right (G x))
    (by simpa only [tsum_mul_right] using hG.const_mul (∑' i, c i)) limits
  exact (((tau^8)⁻¹ • ContinuousLinearMap.id ℝ ℂ) : ℂ →L[ℝ] ℂ).hasSum hSum

private theorem exists_norm_bound_on_nonnegative_of_tail_const {f : ℝ → ℝ}
    (hf : Continuous f) (s c : ℝ) (htail : ∀ y ≥ s, f y = c) : ∃ K : ℝ, ∀ y ≥ 0, ‖f y‖ ≤ K := by
  obtain ⟨B,hB⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) s)).image hf.norm).bddAbove
  refine ⟨max B ‖c‖,fun y hy => ?_⟩
  by_cases h : s ≤ y
  · rw [htail y h]
    exact le_max_right _ _
  · exact (hB (mem_image_of_mem (fun q => ‖f q‖) ⟨hy,(lt_of_not_ge h).le⟩)).trans (le_max_left _ _)

/-- The smooth-profile hypotheses of the manuscript supply the measurable
mode symbols and all majorants for the original Fourier pairing. -/
theorem originalRegularizedAngularPair_hasSum_of_smoothProfile
    (η χ : ℝ → ℝ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ y ≤ r, η y = 0) (hone : ∀ y ≥ R, η y = 1)
    (hχ : ContDiff ℝ ∞ χ) (hcut : ∀ y ≥ ρ^2, χ y = 0)
    {F : Joint × RotationSpace → ℂ} {W : Set (Joint × RotationSpace)} (hW : IsOpen W)
    (hK : (closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1) ×ˢ sphere (0 : RotationSpace) 1 ⊆ W)
    (hF : ContDiffOn ℝ ∞ F W) {M : ℝ} (hM : 0 ≤ M)
    (hjet : ∀ n ≤ 27, ∀ z ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1, ∀ d : RoundSphere3,
      ‖iteratedFDeriv ℝ n F (z,(d : RotationSpace))‖ ≤ M)
    (f u w : SchwartzMap E ℂ) :
    HasSum (fun i => radianHighPair (angularModeSymbol η χ F i) f u w)
      (radianHighPair (originalRegularizedAngularSymbol η χ F) f u w) := by
  obtain ⟨C,hC,coeff⟩ := exists_smoothComplexAngularCoefficient_jet15 (E := Joint)
  obtain ⟨S,hS,hKS,jet⟩ := coeff hW ((isCompact_closedBall _ _).prod (isCompact_sphere _ _)) hK hF M hM hjet
  obtain ⟨U,hU⟩ := exists_norm_bound_on_nonnegative_of_tail_const hη.continuous R 1 hone
  obtain ⟨V,hV⟩ := exists_norm_bound_on_nonnegative_of_tail_const hχ.continuous (ρ^2) 0 hcut
  apply originalRegularizedAngularPair_hasSum η χ hρ hcut hU hV hF.continuousOn hK (mul_nonneg hC hM) _ _ f u w
  · intro i z hz
    have h := (jet i).2 0 (by norm_num) z hz
    rw [norm_iteratedFDeriv_zero] at h
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  · intro i
    let b : OrderOneSymbol ℂ := ⟨regularizedLowCartesianSymbol η χ (jointSphereHarmonicCoefficientComplex F i),
      regularizedLowCartesianSymbol_mem_orderOneSymbolSubmodule η χ _ hr hρ hR hη hzero hone hχ hcut hS hKS (jet i).1⟩
    exact b.measurable_symbol

end Burnett.A07
