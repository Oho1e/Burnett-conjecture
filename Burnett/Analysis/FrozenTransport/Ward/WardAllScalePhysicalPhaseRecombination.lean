import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleUniformTensorPatch
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleCubicActualGaugeAssembly
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTensorVertexLink

set_option autoImplicit false
set_option maxRecDepth 7200
set_option maxHeartbeats 15300000

noncomputable section

namespace Burnett.C02

open Set Filter Matrix MeasureTheory Burnett.Fourier Burnett.RicciSymbol Burnett.V06 Burnett.A02.FrequencySplit Burnett.A05
open Burnett.Analysis.TransportWardSymbol
open Burnett.P01 (ComplexComponents ProjectionSchwartzMatrix)
open Burnett.V08 (originalGaugeSpectrum)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.C03 (ProjectedPatchLpBounds)
open scoped ComplexConjugate ContDiff Matrix Topology

open private wardActualTensorWeight_eq_originalSpectra from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTensorVertexLink
open private wardMiddleTensorTrilinear wardMiddleTensorTrilinear_apply from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleUniformTensorPatch

private theorem wardMiddleTensorWeight_eq_original (ϑ : ℝ → ℝ) (κ : ℝ) (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) :
    wardActualTensorWeight m ![false,true,true] (wardMiddleTensorTrilinear ϑ κ m w a)
      wi wo hm hη i o z = wardLowGaugeMiddleTensorWeight ϑ κ m w a wi wo hm hη i o z := by
  funext x
  let H := wardActualThinSpectrum m wi wo hm hη i o z
  let u : Fin 3 → ComplexComponents := ![originalGaugeSpectrum z x.1, H x.2, H (-(x.1+x.2))]
  have hSlots : (fun j : Fin 3 => if (![false,true,true] : Fin 3 → Bool) j then H (wardPhaseCovector x j)
      else originalGaugeSpectrum z (wardPhaseCovector x j)) = u := by
    funext j
    fin_cases j <;> rfl
  rw [wardActualTensorWeight_eq_originalSpectra, hSlots, wardMiddleTensorTrilinear_apply]
  rfl

/-- Both definitions use the original low-gauge transport-phase middle
coefficient with the same Fourier fields in the same three slots. -/
theorem wardMiddleTensorForm_eq_original (ϑ : ℝ → ℝ) (κ : ℝ) (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) :
    wardActualTensorForm m ![false,true,true] (wardMiddleTensorTrilinear ϑ κ m w a)
      wi wo hm hη i o z = wardLowGaugeMiddleTensorForm ϑ κ m w a wi wo hm hη i o z := by
  simp only [wardActualTensorForm, wardLowGaugeMiddleTensorForm, wardMiddleTensorWeight_eq_original]

/-- The original phase term multiplicities after the full polarized
expansion and the two equivalent low-slot contributions. -/
def wardPhysicalPhaseMultiplicity : Fin 7 → ℝ := ![1,1,2,1,2,1,1]

theorem wardPhysicalPhaseMultiplicity_nonneg (i : Fin 7) : 0 ≤ wardPhysicalPhaseMultiplicity i := by
  fin_cases i <;> norm_num [wardPhysicalPhaseMultiplicity]

theorem wardPhysicalPhaseMultiplicity_total : ∑ i, wardPhysicalPhaseMultiplicity i = 9 := by
  norm_num [wardPhysicalPhaseMultiplicity, Fin.sum_univ_succ]

/-- With exact multiplicities the recombined physical phase remainder
inherits the same full C02 patch bound, up to the finite factor nine. -/
theorem wardPhysicalPhaseWeightedSum_bound (F : ℕ → Fin 7 → ℂ) (M : ℝ)
    (h : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i, ‖F n i‖ ≤ M + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      ‖-Complex.I * ∑ i, (wardPhysicalPhaseMultiplicity i : ℂ) * F n i‖ ≤ 9 * M + ε := by
  intro ε hε
  filter_upwards [h (ε / 9) (div_pos hε (by norm_num))] with n hn
  have hI : ‖(-Complex.I : ℂ)‖ = 1 := by simp
  rw [norm_mul, hI, one_mul]
  calc
    _ ≤ ∑ i, ‖(wardPhysicalPhaseMultiplicity i : ℂ) * F n i‖ := norm_sum_le _ _
    _ ≤ ∑ i, wardPhysicalPhaseMultiplicity i * (M + ε / 9) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (wardPhysicalPhaseMultiplicity_nonneg i)]
      exact mul_le_mul_of_nonneg_left (hn i) (wardPhysicalPhaseMultiplicity_nonneg i)
    _ = _ := by
      rw [← Finset.sum_mul, wardPhysicalPhaseMultiplicity_total]
      ring


/-- The actual phase remainder in the symmetric cubic expansion uses
the seven ordered phase forms and their original sector multiplicities. -/
def wardPhysicalPhaseRemainder (ϑ : ℝ → ℝ) (κ : ℝ) (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) : ℂ :=
  -Complex.I * ∑ s : Fin 7, (wardPhysicalPhaseMultiplicity s : ℂ) *
    wardActualTensorForm m (wardPhysicalPhaseSlots s) (wardPhysicalPhaseTensorSymbol ϑ κ m w a s)
      wi wo hm hη i o z

/-- The first term in the weighted remainder is the original middle
transport-phase form. The other six preserve their exact cutoffs and slots. -/
theorem wardPhysicalPhaseRemainder_eq_original_forms
    (ϑ : ℝ → ℝ) (κ : ℝ) (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) :
    let F (b : Fin 3 → Bool) (A : Joint → WardTensorTrilinear) := wardActualTensorForm m b A wi wo hm hη i o z
    wardPhysicalPhaseRemainder ϑ κ m w a wi wo hm hη i o z =
      -Complex.I * (wardLowGaugeMiddleTensorForm ϑ κ m w a wi wo hm hη i o z +
        F ![false,true,true] (wardFirstLowTrilinear ϑ κ (wardOneLowGaugeLieRawTrilinear m w a)) +
        2 * F ![true,true,false] (wardFirstLowTrilinear ϑ κ (wardOneHighGaugeRawTrilinear m w a)) +
        F ![true,false,false] (wardFirstLowTrilinear ϑ κ (wardTwoGaugePhysicalRawTrilinear m w a)) +
        2 * F ![false,true,false] (wardFirstLowTrilinear ϑ κ (wardTwoGaugeGaugeRawTrilinear m w a)) +
        F ![true,true,false] (wardComparableTrilinear ϑ κ (wardOneHighGaugeRawTrilinear m w a)) +
        F ![true,false,false] (wardComparableTrilinear ϑ κ (wardTwoGaugePhysicalRawTrilinear m w a))) := by
  intro F
  unfold wardPhysicalPhaseRemainder
  simp only [wardPhysicalPhaseMultiplicity, wardPhysicalPhaseSlots, wardPhysicalPhaseTensorSymbol,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero,
    Complex.ofReal_one, Complex.ofReal_ofNat, one_mul, wardMiddleTensorForm_eq_original]
  dsimp only [F]
  ring

/-- The complete original frozen cyclic form contains the same phase
remainder that is controlled by the common C02 patch estimate. -/
theorem wardCyclicActualFrozenGaugeDecomposition_recombined
    (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
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
    Integrable (wardCyclicCubicWeight G a H H H) → Integrable K →
    (∀ s : Fin 7, Integrable (wardActualTensorWeight m (wardPhysicalPhaseSlots s)
      (wardPhysicalPhaseTensorSymbol ϑ κ m w a s) wi wo hm hη i o z)) →
    wardCyclicCubicForm G a (H+Q) (H+Q) (H+Q) =
      wardCyclicCubicForm G a H H H + 3 * ((tau^8)⁻¹ • (∫ x, K x)) +
        wardPhysicalPhaseRemainder ϑ κ m w a wi wo hm hη i o z := by
  intro m w H Q K hPure hK hSeven
  have hM : Integrable (wardLowGaugeMiddleTensorWeight ϑ κ m w a wi wo hm hη i o z) := by
    have h : Integrable (wardActualTensorWeight m ![false,true,true] (wardMiddleTensorTrilinear ϑ κ m w a)
        wi wo hm hη i o z) := hSeven 0
    rwa [wardMiddleTensorWeight_eq_original] at h
  have h := wardCyclicActualFrozenGaugeDecomposition G hG hg f a ϑ κ wi wo hm hη i o ε hi hio hSmall
    hWindow z hz hReal hPure hK hM (hSeven 1) (hSeven 2) (hSeven 5) (hSeven 3) (hSeven 4) (hSeven 6)
  rw [wardPhysicalPhaseRemainder_eq_original_forms]
  unfold wardLowGaugeMiddleTensorForm wardActualTensorForm
  refine h.trans ?_
  ring

end Burnett.C02
