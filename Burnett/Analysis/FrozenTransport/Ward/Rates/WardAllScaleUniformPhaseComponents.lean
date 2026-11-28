import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleUniformRadial
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualComparable
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableFactors
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualLowFields
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugePatch

set_option autoImplicit false
set_option maxRecDepth 7400
set_option maxHeartbeats 17000000

noncomputable section

namespace Burnett.C02

open Set MeasureTheory Burnett.A05 Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open Burnett.RicciSymbol (Tensor2)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.C03 (projectedGaugeComplement)
open scoped ContDiff

open private wardComparableCut_eq_sum_phases from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualComparable
open private wardComparableDenominator from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableFactors
open private wardGradientPhaseProduct_bound from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualLowFields
open private ward_coordinate_gradient_bound from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugePatch

/-- Transfer the exact physical phase to its original thin slot, using
specified bounds for the radial component forms. -/
theorem wardActualPhaseComponent_bound_of_radial {ι : Type*} [Fintype ι] (m : Tensor2)
    (A : Joint → ℂ) (B : ι → Joint → ℂ) (C : ι → ℝ) (hC : ∀ s, 0 ≤ C s)
    (j : ι → Fin 3) (physical : Fin 3 → Bool) (k : Fin 3 → OrderedPair) (hj : ∀ i, physical (j i) = true)
    (hEst : ∀ s (f g h : SchwartzMap E ℂ), Integrable (radianTrilinearWeight (B s) f g h) ∧
      ‖radianTrilinearForm (B s) f g h‖ ≤ C s *
        (wardCoordinateGradientL3 f * wardCoordinateGradientL3 g * wardCoordinateGradientL3 h))
    (hA : ∀ x, A x = ∑ s, B s x * (normalizedFrozenPhase m (wardPhaseCovector x (j s)) : ℂ)) :
    WardActualLowComponentBound m physical k A (64 * ∑ s, C s) := by
  classical
  intro wi wo hm η hη i o z V G P f
  let f' s := Function.update f (j s) (P (k (j s)))
  let W s := radianTrilinearWeight (B s) (f' s 0) (f' s 1) (f' s 2)
  let T s := radianTrilinearForm (B s) (f' s 0) (f' s 1) (f' s 2)
  have hg (s : ι) (ξ : E) : radianFourier (P (k (j s))) ξ =
      (normalizedFrozenPhase m ξ : ℂ) * radianFourier (f (j s)) ξ := by
    have he : f (j s) = V (k (j s)) := by simp [f, wardActualLowSlots, hj, V]
    rw [he]
    exact actualWardPhaseSchwartz_radianFourier m wi wo hm hη i o z (k (j s)) ξ
  have hInt (s : ι) : Integrable (W s) := (hEst s _ _ _).1
  have hW : radianTrilinearWeight (A) (f 0) (f 1) (f 2) = fun x => ∑ s, W s x := by
    funext x
    have he (s : ι) : W s x =
        radianTrilinearWeight (fun y => B s y * (normalizedFrozenPhase m (wardPhaseCovector y (j s)) : ℂ))
          (f 0) (f 1) (f 2) x :=
      congrFun (wardRadianWeight_phase_transfer (B s) (fun ξ => (normalizedFrozenPhase m ξ : ℂ)) f (P (k (j s))) (j s)
        (hg s)).symm x
    change A x * _ = _
    rw [hA x, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => (he s).symm
  refine ⟨hW.symm ▸ integrable_finset_sum Finset.univ (fun s _ => hInt s),?_⟩
  have hSum : radianTrilinearForm (A) (f 0) (f 1) (f 2) = ∑ s, T s := by
    change (tau^8)⁻¹ • (∫ x, radianTrilinearWeight (A) (f 0) (f 1) (f 2) x) =
      ∑ s : ι, (tau^8)⁻¹ • (∫ x, W s x)
    rw [hW, ← Finset.smul_sum, ← integral_finset_sum Finset.univ (fun s _ => hInt s)]
  rw [hSum]
  let a := euclideanFieldGradientL3 P
  let b := euclideanFieldGradientL3 G + euclideanFieldGradientL3 V
  have hn (u : OrderedPair → SchwartzMap E ℂ) : 0 ≤ euclideanFieldGradientL3 u := ENNReal.toReal_nonneg
  have hfn (s : Fin 3) : wardCoordinateGradientL3 (f s) ≤ 4 * b := by
    by_cases hs : physical s = true
    · have he : f s = V (k s) := by simp [f, wardActualLowSlots, hs, V]
      rw [he]
      exact (ward_coordinate_gradient_bound V (k s)).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hn G)) (by norm_num))
    · have he : f s = G (k s) := by simp [f, wardActualLowSlots, hs, G]
      rw [he]
      exact (ward_coordinate_gradient_bound G (k s)).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hn V)) (by norm_num))
  calc
    _ ≤ ∑ s, ‖T s‖ := norm_sum_le _ _
    _ ≤ ∑ s, C s * (64 * a * b^2) := by
      apply Finset.sum_le_sum
      intro s _
      exact (hEst s _ _ _).2.trans (mul_le_mul_of_nonneg_left (wardGradientPhaseProduct_bound f (P (k (j s)))
        (j s) a b (hn P) (add_nonneg (hn G) (hn V)) (ward_coordinate_gradient_bound P _) hfn) (hC s))
    _ = _ := by rw [← Finset.sum_mul]; unfold a b; ring

/-- One first-low phase-component constant is chosen over the whole
compact family, before the receiving center and actual inputs. -/
theorem exists_wardActualLowComponent_compactFamilyBound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ι : Type*} [Fintype ι]
    (K V : Set X) (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (hCut : ∀ t, 1 ≤ t → ϑ t = 0)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) (m : X → Tensor2)
    (A : X → Joint → ℂ) (F : ι → X × WardLowPoint → ℂ)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (V ×ˢ wardLowProfileDomain))
    (j : ι → Fin 3) (physical : Fin 3 → Bool) (k : Fin 3 → OrderedPair) (hj : ∀ i, physical (j i) = true)
    (hA : ∀ c ∈ K, ∀ x ∈ wardLowActive,
      A c x = ((‖x.1‖ * ‖x.2‖ * ‖-(x.1+x.2)‖ : ℝ) : ℂ) *
        ∑ i, F i (c,wardLowInput x) * (normalizedFrozenPhase (m c) (wardPhaseCovector x (j i)) : ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ K, WardActualLowComponentBound (m c) physical k (wardActualLowCut ϑ κ (A c)) C := by
  classical
  choose C hC hEst using fun i => exists_wardLowRadialForm_compactFamilyBound K V hK hV hKV (F i) (hF i)
    ϑ hϑ hCut κ hκ hSmall
  refine ⟨64 * ∑ s, C s, mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ => hC s), ?_⟩
  intro c hc
  exact wardActualPhaseComponent_bound_of_radial (m c) (wardActualLowCut ϑ κ (A c))
    (fun s => wardLowRadialSymbol ϑ κ (fun y => F s (c,y))) C hC j physical k hj
    (fun s => hEst s c hc)
    (wardActualLowCut_eq_sum_phases ϑ hCut κ hκ hSmall (m c) (A c) (fun s y => F s (c,y)) j (hA c hc))

/-- One comparable phase-component constant is chosen over the whole
compact family, before the receiving center and actual inputs. -/
theorem exists_wardActualComparableComponent_compactFamilyBound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ι : Type*} [Fintype ι]
    (K V : Set X) (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (hCut : ∀ t, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) (m : X → Tensor2)
    (A : X → Joint → ℂ) (F : ι → X × Joint → ℂ)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (V ×ˢ wardTriadDomain))
    (hHom : ∀ i c, c ∈ K → ∀ t : ℝ, 0 < t → ∀ x ∈ wardTriadDomain, F i (c,t • x) = F i (c,x))
    (j : ι → Fin 3) (physical : Fin 3 → Bool) (k : Fin 3 → OrderedPair) (hj : ∀ i, physical (j i) = true)
    (hA : ∀ c ∈ K, ∀ x ∈ wardTriadDomain, A c x = wardComparableDenominator x *
      ∑ s, F s (c,x) * (normalizedFrozenPhase (m c) (wardPhaseCovector x (j s)) : ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ K, WardActualLowComponentBound (m c) physical k (wardComparableSymbol ϑ κ (A c)) C := by
  classical
  choose C hC hEst using fun i => exists_wardComparableRadialForm_compactFamilyBound K V hK hV hKV (F i)
    (hF i) (hHom i) ϑ hϑ hCut hFlat κ hκ hSmall
  refine ⟨64 * ∑ s, C s, mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ => hC s), ?_⟩
  intro c hc
  exact wardActualPhaseComponent_bound_of_radial (m c) (wardComparableSymbol ϑ κ (A c))
    (fun s => wardComparableRadialSymbol ϑ κ (fun y => F s (c,y))) C hC j physical k hj
    (fun s => hEst s c hc)
    (wardComparableCut_eq_sum_phases ϑ κ (m c) (A c) (fun s y => F s (c,y)) j (hA c hc))

end Burnett.C02
