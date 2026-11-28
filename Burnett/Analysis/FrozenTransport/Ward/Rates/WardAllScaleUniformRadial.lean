import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleLowQuantitative
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleComparableUniform
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableRadial
import Burnett.Analysis.FrozenTransport.Ward.WardLowTransferDerivatives
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleSignedPartition

set_option autoImplicit false
set_option maxRecDepth 7400
set_option maxHeartbeats 18200000

noncomputable section

namespace Burnett.C02

open Set MeasureTheory Burnett.A02.FrequencySplit Burnett.A05 Burnett.Analysis.CapFourier
open Burnett.A07 (coordinateDerivative)
open scoped ContDiff

open private wardLowCoordinateProfile_smooth wardLowRadialWeight_eq_coordinate_sum unit_mem_wardLowProfileDomain from Burnett.Analysis.FrozenTransport.Ward.WardLowTransferDerivatives
open private wardComparableCoordinateProfile wardComparableCoordinateProfile_smooth wardComparableCoordinateProfile_hom wardComparableRadialWeight_eq_coordinate_sum from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableRadial
open private wardComparableSymbol_bounded from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleSignedPartition

private theorem wardRadialForm_bound_of_coordinates (A : Joint → ℂ) (m : WardDerivativeAxes → Joint → ℂ)
    (C B : WardDerivativeAxes → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hm : ∀ i, Measurable (m i)) (hB : ∀ i x, ‖m i x‖ ≤ B i)
    (hEst : ∀ i (f g h : SchwartzMap E ℂ),
      ‖radianTrilinearForm (m i) f g h‖ ≤ C i * (triLpMass f g h 3 3 3).toReal)
    (f g h : SchwartzMap E ℂ)
    (hWeights : ∀ x, radianTrilinearWeight A f g h x =
      ∑ i : WardDerivativeAxes, radianTrilinearWeight (m i) (coordinateDerivative i.1 f)
        (coordinateDerivative i.2.1 g) (coordinateDerivative i.2.2 h) x) :
    Integrable (radianTrilinearWeight A f g h) ∧
    ‖radianTrilinearForm A f g h‖ ≤ (∑ i, C i) *
      (wardCoordinateGradientL3 f * wardCoordinateGradientL3 g * wardCoordinateGradientL3 h) := by
  let W i := radianTrilinearWeight (m i) (coordinateDerivative i.1 f)
    (coordinateDerivative i.2.1 g) (coordinateDerivative i.2.2 h)
  let T i := radianTrilinearForm (m i) (coordinateDerivative i.1 f)
    (coordinateDerivative i.2.1 g) (coordinateDerivative i.2.2 h)
  have hInt (i : WardDerivativeAxes) : Integrable (W i) :=
    integrable_radianTrilinearWeight_of_bounded (m i) (hm i).aestronglyMeasurable (B i) (hB i) _ _ _
  have hWeight : radianTrilinearWeight A f g h = fun x => ∑ i, W i x := funext hWeights
  refine ⟨hWeight.symm ▸ integrable_finset_sum Finset.univ (fun i _ => hInt i), ?_⟩
  have hForm : radianTrilinearForm A f g h = ∑ i, T i := by
    change (tau^8)⁻¹ • (∫ x, radianTrilinearWeight A f g h x) =
      ∑ i : WardDerivativeAxes, (tau^8)⁻¹ • (∫ x, W i x)
    rw [hWeight, ← Finset.smul_sum, ← integral_finset_sum Finset.univ (fun i _ => hInt i)]
  rw [hForm]
  have hTerm (u : SchwartzMap E ℂ) (j : Fin 4) :
      (eLpNorm (coordinateDerivative j u : E → ℂ) 3 volume).toReal ≤ wardCoordinateGradientL3 u := by
    unfold wardCoordinateGradientL3
    exact Finset.single_le_sum (f := fun i => (eLpNorm (coordinateDerivative i u : E → ℂ) 3 volume).toReal)
      (fun (_ : Fin 4) _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
  have hNonneg (u : SchwartzMap E ℂ) : 0 ≤ wardCoordinateGradientL3 u :=
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  calc
    _ ≤ ∑ i, ‖T i‖ := norm_sum_le _ _
    _ ≤ ∑ i, C i * (wardCoordinateGradientL3 f * wardCoordinateGradientL3 g * wardCoordinateGradientL3 h) := by
      apply Finset.sum_le_sum
      intro i _
      refine (hEst i _ _ _).trans (mul_le_mul_of_nonneg_left ?_ (hC i))
      simp only [triLpMass, ENNReal.toReal_mul, ENNReal.ofReal_ofNat]
      exact mul_le_mul (mul_le_mul (hTerm f i.1) (hTerm g i.2.1) ENNReal.toReal_nonneg (hNonneg f))
        (hTerm h i.2.2) ENNReal.toReal_nonneg (mul_nonneg (hNonneg f) (hNonneg g))
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The actual first-low radial form keeps the three ordinary gradients with
one uniform constant for the given compact smooth family. -/
theorem exists_wardLowRadialForm_compactFamilyBound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K V : Set X) (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (F : X × WardLowPoint → ℂ) (hF : ContDiffOn ℝ ∞ F (V ×ˢ wardLowProfileDomain))
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ K, ∀ f g h : SchwartzMap E ℂ,
      let A := wardLowRadialSymbol ϑ κ (fun x => F (c,x))
      Integrable (radianTrilinearWeight A f g h) ∧
      ‖radianTrilinearForm A f g h‖ ≤
        C * (wardCoordinateGradientL3 f * wardCoordinateGradientL3 g * wardCoordinateGradientL3 h) := by
  classical
  let G (i : WardDerivativeAxes) (p : X × WardLowPoint) := wardLowCoordinateProfile (fun x => F (p.1,x)) i p.2
  have hG (i : WardDerivativeAxes) : ContDiffOn ℝ ∞ (G i) (V ×ˢ wardLowProfileDomain) := by
    have hMap : MapsTo (fun p : X × WardLowPoint => p.2) (V ×ˢ wardLowProfileDomain) wardLowProfileDomain :=
      fun _ hx => hx.2
    have hc := (wardLowCoordinateProfile_smooth (fun _ => 1) contDiffOn_const i).comp contDiff_snd.contDiffOn
      hMap
    simpa only [G, Function.comp_apply, wardLowCoordinateProfile, one_mul] using hF.mul hc
  choose C hC hEst using fun i => exists_wardLowSlotForm_compactFamilyBound K V hK hV hKV (G i)
    wardLowProfileDomain (hG i) unit_mem_wardLowProfileDomain ϑ hϑ hCut κ hκ hSmall
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro c hc f g h
  let m i := wardLowSlotSymbol ϑ κ (fun x => G i (c,x))
  choose B hB using fun i => (hEst i c hc).2.1
  exact wardRadialForm_bound_of_coordinates _ m C B hC (fun i => (hEst i c hc).1)
    hB (fun i => (hEst i c hc).2.2) f g h
    (wardLowRadialWeight_eq_coordinate_sum ϑ κ (fun x => F (c,x)) f g h)

/-- The actual comparable form uses the same three gradients with
one uniform constant over the compact family of frozen centers. -/
theorem exists_wardComparableRadialForm_compactFamilyBound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K V : Set X) (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (F : X × Joint → ℂ) (hF : ContDiffOn ℝ ∞ F (V ×ˢ wardTriadDomain))
    (hHom : ∀ c ∈ K, ∀ t : ℝ, 0 < t → ∀ x ∈ wardTriadDomain, F (c,t • x) = F (c,x))
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ K, ∀ f g h : SchwartzMap E ℂ,
      let A := wardComparableRadialSymbol ϑ κ (fun x => F (c,x))
      Integrable (radianTrilinearWeight A f g h) ∧
      ‖radianTrilinearForm A f g h‖ ≤
        C * (wardCoordinateGradientL3 f * wardCoordinateGradientL3 g * wardCoordinateGradientL3 h) := by
  classical
  let G (i : WardDerivativeAxes) (p : X × Joint) := wardComparableCoordinateProfile (fun x => F (p.1,x)) i p.2
  have hG (i : WardDerivativeAxes) : ContDiffOn ℝ ∞ (G i) (V ×ˢ wardTriadDomain) := by
    have hMap : MapsTo (fun p : X × Joint => p.2) (V ×ˢ wardTriadDomain) wardTriadDomain :=
      fun _ hx => hx.2
    have hc := (wardComparableCoordinateProfile_smooth (fun _ => 1) contDiffOn_const i).comp contDiff_snd.contDiffOn
      hMap
    simpa only [G, Function.comp_apply, wardComparableCoordinateProfile, one_mul] using hF.mul hc
  have hGh (i : WardDerivativeAxes) (c : X) (hc : c ∈ K) :=
    wardComparableCoordinateProfile_hom (fun x => F (c,x)) (hHom c hc) i
  choose C hC hEst using fun i => exists_wardComparableForm_compactFamilyBound K V hK hV hKV (G i)
    (hG i) (hGh i) ϑ hϑ hCut hFlat κ hκ hSmall
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro c hc f g h
  let m i := wardComparableSymbol ϑ κ (fun x => G i (c,x))
  have hGs (i : WardDerivativeAxes) : ContDiffOn ℝ ∞ (fun x => G i (c,x)) wardTriadDomain :=
    (hG i).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => ⟨hKV hc,hx⟩)
  choose B _hB hBound using fun i => wardComparableSymbol_bounded ϑ hϑ hCut hFlat κ hκ hSmall
    (fun x => G i (c,x)) (hGs i) (hGh i c hc)
  have hm (i : WardDerivativeAxes) : Measurable (m i) :=
    measurable_radianFourBranchSymbol ϑ hϑ.continuous.measurable κ _
      ((hGs i).continuousOn.measurable_piecewise continuousOn_const wardTriadDomain_open.measurableSet) 3
  exact wardRadialForm_bound_of_coordinates _ m C B hC hm hBound
    (fun i => hEst i c hc) f g h
    (wardComparableRadialWeight_eq_coordinate_sum ϑ κ (fun x => F (c,x)) f g h)

end Burnett.C02
