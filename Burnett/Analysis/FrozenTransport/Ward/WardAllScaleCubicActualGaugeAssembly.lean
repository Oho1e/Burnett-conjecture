import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleCubicGaugeWeights

set_option autoImplicit false
set_option maxRecDepth 7800
set_option maxHeartbeats 19400000

noncomputable section

namespace Burnett.C02

open Set Filter Matrix MeasureTheory Burnett.RicciSymbol Burnett.V06 Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.V08 (originalGaugeSpectrum)
open scoped Matrix ComplexConjugate

open private wardAE_first_two_nonzero from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleCubicGaugeWeights

private theorem wardAE_triadDomain :
    ∀ᵐ x ∂(volume : Measure Joint), x ∈ wardTriadDomain := by
  have hThird := measurePreserving_radianCycle.quasiMeasurePreserving.ae
    (wardAE_first_two_nonzero.mono fun (_ : Joint) hx => hx.2)
  filter_upwards [wardAE_first_two_nonzero,hThird] with x hx hr
  exact ⟨hx.1,hx.2,hr⟩

private theorem wardCyclicBranchForm_of_weight_eq (ϑ : ℝ → ℝ) (κ : ℝ) (b : Fin 4) (G : Mat) (a : E → ℝ)
    (F H J : E → ComplexTensor2) (W : Joint → ℂ) (hInt : Integrable W)
    (heq : wardCyclicCubicBranchWeight ϑ κ b G a F H J =ᵐ[volume] fun x => (-Complex.I / 3) * W x) :
    Integrable (wardCyclicCubicBranchWeight ϑ κ b G a F H J) ∧
    wardCyclicCubicBranchForm ϑ κ b G a F H J = (-Complex.I / 3) * ((tau ^ 8)⁻¹ • ∫ x, W x) := by
  refine ⟨(hInt.const_mul _).congr heq.symm,?_⟩
  unfold wardCyclicCubicBranchForm
  rw [integral_congr_ae heq, integral_const_mul]
  simp only [Complex.real_smul]
  ring

/-- The original one- and two-gauge cubic energies equal their exact
ordered physical phase forms and the original low-gauge correction.
All phases are on the same physically projected fields. -/
theorem wardCyclicActualGaugeForms_eq_original (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ : ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm (inverseMatrix G) e| < ε →
      screenSecondDirection (inverseMatrix G) e ≠ 0 ∧
      IsUnit (screenMetricExtension (inverseMatrix G) (screenDirectionProjection (inverseMatrix G) e)).det)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a)
    (hReal : ∀ a b x, conj (z a b x) = z a b x) :
    let m := inverseMatrix G
    let w := metricDensity G
    let H := wardActualThinSpectrum m wi wo hm hη i o z
    let Q := originalGaugeSpectrum z
    let K := wardOrderedGaugeCorrectionNumerator ϑ κ G a wi wo hm hη i o z
    let M := wardLowGaugeMiddleTensorWeight ϑ κ m w a wi wo hm hη i o z
    let W (b : Fin 3 → Bool) (A : Joint → WardTensorTrilinear) := wardActualTensorWeight m b A wi wo hm hη i o z
    let L := W ![false,true,true] (wardFirstLowTrilinear ϑ κ (wardOneLowGaugeLieRawTrilinear m w a))
    let G₁ := W ![true,true,false] (wardFirstLowTrilinear ϑ κ (wardOneHighGaugeRawTrilinear m w a))
    let G₃ := W ![true,true,false] (wardComparableTrilinear ϑ κ (wardOneHighGaugeRawTrilinear m w a))
    let D₀ := W ![true,false,false] (wardFirstLowTrilinear ϑ κ (wardTwoGaugePhysicalRawTrilinear m w a))
    let D₁ := W ![false,true,false] (wardFirstLowTrilinear ϑ κ (wardTwoGaugeGaugeRawTrilinear m w a))
    let D₃ := W ![true,false,false] (wardComparableTrilinear ϑ κ (wardTwoGaugePhysicalRawTrilinear m w a))
    let I (F : Joint → ℂ) := (tau^8)⁻¹ • ∫ x, F x
    Integrable K → Integrable M → Integrable L → Integrable G₁ → Integrable G₃ →
    Integrable D₀ → Integrable D₁ → Integrable D₃ →
      (Integrable (wardCyclicCubicWeight G a Q H H) ∧ Integrable (wardCyclicCubicWeight G a H Q Q)) ∧
      wardCyclicCubicForm G a Q H H =
        I K + (-Complex.I / 3) * (I M + I L + 2 * I G₁ + I G₃) ∧
      wardCyclicCubicForm G a H Q Q = (-Complex.I / 3) * (I D₀ + 2 * I D₁ + I D₃) := by
  intro m w H Q K M W L G₁ G₃ D₀ D₁ D₃ I hK hM hL hG₁ hG₃ hD₀ hD₁ hD₃
  have hLow := wardCyclicActualLowGaugeForm_eq_original G hG hg f a ϑ κ wi wo hm hη i o ε hi hio hSmall
    hWindow z hz hReal hK hM hL
  have hHigh₁ : wardCyclicCubicBranchWeight ϑ κ 0 G a H H Q =ᵐ[volume] fun x => (-Complex.I / 3) * G₁ x := by
    filter_upwards [wardAE_triadDomain] with x hx
    obtain ⟨p,q⟩ := x
    have hv := (wardActualHighGauge_cut_tensor_eq_vertex G hG hg f a ϑ κ wi wo hm hη i o ε hi hio hSmall hWindow z hz p q hx).1
    have hW : G₁ (p,q) = _ := hv
    rw [hW]
    unfold wardCyclicCubicBranchWeight wardCyclicCubicWeight
    change (Burnett.Analysis.ProjectiveNullCaps.lowSlotWeight ϑ κ p q (-(p+q)) : ℂ) * (_ * _ * _) = _
    ring
  have hHigh₃ : wardCyclicCubicBranchWeight ϑ κ 3 G a H H Q =ᵐ[volume] fun x => (-Complex.I / 3) * G₃ x := by
    filter_upwards [wardAE_triadDomain] with x hx
    obtain ⟨p,q⟩ := x
    have hv := (wardActualHighGauge_cut_tensor_eq_vertex G hG hg f a ϑ κ wi wo hm hη i o ε hi hio hSmall hWindow z hz p q hx).2
    have hW : G₃ (p,q) = _ := hv
    rw [hW]
    unfold wardCyclicCubicBranchWeight wardCyclicCubicWeight
    change (Burnett.Analysis.ProjectiveNullCaps.comparableSlotWeight ϑ κ p q (-(p+q)) : ℂ) * (_ * _ * _) = _
    ring
  have hDouble₀ : wardCyclicCubicBranchWeight ϑ κ 0 G a H Q Q =ᵐ[volume] fun x => (-Complex.I / 3) * D₀ x := by
    filter_upwards [wardAE_triadDomain] with x hx
    obtain ⟨p,q⟩ := x
    have hv := (wardActualTwoGauge_physical_cut_tensor_eq_vertex G hG hg f a ϑ κ wi wo hm hη i o ε hi hio hSmall hWindow z hz p q hx).1
    have hW : D₀ (p,q) = _ := hv
    rw [hW]
    unfold wardCyclicCubicBranchWeight wardCyclicCubicWeight
    change (Burnett.Analysis.ProjectiveNullCaps.lowSlotWeight ϑ κ p q (-(p+q)) : ℂ) * (_ * _ * _) = _
    ring
  have hDouble₁ : wardCyclicCubicBranchWeight ϑ κ 0 G a Q H Q =ᵐ[volume] fun x => (-Complex.I / 3) * D₁ x := by
    filter_upwards [wardAE_triadDomain] with x hx
    obtain ⟨p,q⟩ := x
    have hv := wardActualTwoGauge_gauge_cut_tensor_eq_vertex G hG hg f a ϑ κ wi wo hm hη i o ε hi hio hSmall hWindow z hz p q hx
    have hW : D₁ (p,q) = _ := hv
    rw [hW]
    unfold wardCyclicCubicBranchWeight wardCyclicCubicWeight
    change (Burnett.Analysis.ProjectiveNullCaps.lowSlotWeight ϑ κ p q (-(p+q)) : ℂ) * (_ * _ * _) = _
    ring
  have hDouble₃ : wardCyclicCubicBranchWeight ϑ κ 3 G a H Q Q =ᵐ[volume] fun x => (-Complex.I / 3) * D₃ x := by
    filter_upwards [wardAE_triadDomain] with x hx
    obtain ⟨p,q⟩ := x
    have hv := (wardActualTwoGauge_physical_cut_tensor_eq_vertex G hG hg f a ϑ κ wi wo hm hη i o ε hi hio hSmall hWindow z hz p q hx).2
    have hW : D₃ (p,q) = _ := hv
    rw [hW]
    unfold wardCyclicCubicBranchWeight wardCyclicCubicWeight
    change (Burnett.Analysis.ProjectiveNullCaps.comparableSlotWeight ϑ κ p q (-(p+q)) : ℂ) * (_ * _ * _) = _
    ring
  have h1 := wardCyclicBranchForm_of_weight_eq ϑ κ 0 G a H H Q G₁ hG₁ hHigh₁
  have h3 := wardCyclicBranchForm_of_weight_eq ϑ κ 3 G a H H Q G₃ hG₃ hHigh₃
  have hD0 := wardCyclicBranchForm_of_weight_eq ϑ κ 0 G a H Q Q D₀ hD₀ hDouble₀
  have hD1 := wardCyclicBranchForm_of_weight_eq ϑ κ 0 G a Q H Q D₁ hD₁ hDouble₁
  have hD3 := wardCyclicBranchForm_of_weight_eq ϑ κ 3 G a H Q Q D₃ hD₃ hDouble₃
  have hOne := wardCyclicCubicForm_oneGauge_sectorSum ϑ κ G a H Q hLow.1 h1.1 h3.1
  have hTwo := wardCyclicCubicForm_twoGauge_sectorSum ϑ κ G a H Q hD0.1 hD1.1 hD3.1
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨hOne.1,hTwo.1⟩
  · rw [hOne.2, hLow.2, h1.2, h3.2]
    change I K + (-Complex.I / 3) * (I M + I L) + 2 * ((-Complex.I / 3) * I G₁) +
      (-Complex.I / 3) * I G₃ = _
    ring
  · rw [hTwo.2, hD0.2, hD1.2, hD3.2]
    change (-Complex.I / 3) * I D₀ + 2 * ((-Complex.I / 3) * I D₁) + (-Complex.I / 3) * I D₃ = _
    ring


/-- The exact three-gauge term contributes zero to the original cyclic
integral on the three copies of the same projected gauge complement. -/
theorem wardCyclicActualThreeGaugeForm_eq_zero (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (a : E → ℝ)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a) :
    let Q := originalGaugeSpectrum z
    Integrable (wardCyclicCubicWeight G a Q Q Q) ∧ wardCyclicCubicForm G a Q Q Q = 0 := by
  intro Q
  have hAE : wardCyclicCubicWeight G a Q Q Q =ᵐ[volume] (0 : Joint → ℂ) := by
    filter_upwards [wardAE_triadDomain] with x hx
    obtain ⟨p,q⟩ := x
    have h := wardActualThreeGaugeVertex_eq_zero G hG hg f z hz p q hx.1 hx.2.1 hx.2.2
    unfold wardCyclicCubicWeight
    change _ * _ * complexPrincipalVertex G (fun i => p i) (Q p)
      (fun i => q i) (Q q) (fun i => (-(p+q)) i) (Q (-(p+q))) = 0
    rw [h,mul_zero]
  have hZero : Integrable (0 : Joint → ℂ) := integrable_zero Joint ℂ volume
  refine ⟨hZero.congr hAE.symm, ?_⟩
  unfold wardCyclicCubicForm
  rw [integral_congr_ae hAE]
  simp


/-- The complete frozen cyclic energy on the actual thin-plus-gauge input
has the original three physical term, three times the exact correction,
and the explicit physical-phase remainder. -/
theorem wardCyclicActualFrozenGaugeDecomposition (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ : ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm (inverseMatrix G) e| < ε →
      screenSecondDirection (inverseMatrix G) e ≠ 0 ∧
      IsUnit (screenMetricExtension (inverseMatrix G) (screenDirectionProjection (inverseMatrix G) e)).det)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a)
    (hReal : ∀ a b x, conj (z a b x) = z a b x) :
    let m := inverseMatrix G
    let w := metricDensity G
    let H := wardActualThinSpectrum m wi wo hm hη i o z
    let Q := originalGaugeSpectrum z
    let K := wardOrderedGaugeCorrectionNumerator ϑ κ G a wi wo hm hη i o z
    let M := wardLowGaugeMiddleTensorWeight ϑ κ m w a wi wo hm hη i o z
    let W (b : Fin 3 → Bool) (A : Joint → WardTensorTrilinear) := wardActualTensorWeight m b A wi wo hm hη i o z
    let L := W ![false,true,true] (wardFirstLowTrilinear ϑ κ (wardOneLowGaugeLieRawTrilinear m w a))
    let G₁ := W ![true,true,false] (wardFirstLowTrilinear ϑ κ (wardOneHighGaugeRawTrilinear m w a))
    let G₃ := W ![true,true,false] (wardComparableTrilinear ϑ κ (wardOneHighGaugeRawTrilinear m w a))
    let D₀ := W ![true,false,false] (wardFirstLowTrilinear ϑ κ (wardTwoGaugePhysicalRawTrilinear m w a))
    let D₁ := W ![false,true,false] (wardFirstLowTrilinear ϑ κ (wardTwoGaugeGaugeRawTrilinear m w a))
    let D₃ := W ![true,false,false] (wardComparableTrilinear ϑ κ (wardTwoGaugePhysicalRawTrilinear m w a))
    let I (F : Joint → ℂ) := (tau^8)⁻¹ • ∫ x, F x
    Integrable (wardCyclicCubicWeight G a H H H) →
    Integrable K → Integrable M → Integrable L → Integrable G₁ → Integrable G₃ →
    Integrable D₀ → Integrable D₁ → Integrable D₃ →
    wardCyclicCubicForm G a (H+Q) (H+Q) (H+Q) =
      wardCyclicCubicForm G a H H H + 3 * I K +
        (-Complex.I) * (I M + I L + 2 * I G₁ + I G₃ + I D₀ + 2 * I D₁ + I D₃) := by
  intro m w H Q K M W L G₁ G₃ D₀ D₁ D₃ I hP hK hM hL hG₁ hG₃ hD₀ hD₁ hD₃
  have hMix := wardCyclicActualGaugeForms_eq_original G hG hg f a ϑ κ wi wo hm hη i o ε hi hio hSmall
    hWindow z hz hReal hK hM hL hG₁ hG₃ hD₀ hD₁ hD₃
  have hQQQ := wardCyclicActualThreeGaugeForm_eq_zero G hG hg f a z hz
  have hDet : Matrix.det G ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det G).mp hG)
  rw [wardCyclicCubicForm_expand G hDet a H Q hP hMix.1.1 hMix.1.2 hQQQ.1, hMix.2.1, hMix.2.2, hQQQ.2]
  change wardCyclicCubicForm G a H H H +
    3 * (I K + (-Complex.I / 3) * (I M + I L + 2 * I G₁ + I G₃)) +
    3 * ((-Complex.I / 3) * (I D₀ + 2 * I D₁ + I D₃)) + 0 = _
  ring

end Burnett.C02
