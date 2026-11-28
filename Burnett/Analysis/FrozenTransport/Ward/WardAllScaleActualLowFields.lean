import Burnett.Analysis.FrozenTransport.Ward.WardAllScalePhaseBranchSymbols
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugePatch

set_option autoImplicit false
set_option maxRecDepth 6500
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.C02

open Set MeasureTheory Burnett.A05 Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open Burnett.RicciSymbol (Tensor2)
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.C03 (projectedGaugeComplement)
open scoped ContDiff

open private ward_coordinate_gradient_bound from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugePatch

/-- Scalar Schwartz slots of the same original receiving-chart field. The
physical entries use the exact frozen thin screen and the other entries its
unchanged projected gauge complement. -/
def wardActualLowSlots (m : Tensor2) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix)
    (physical : Fin 3 → Bool) (k : Fin 3 → OrderedPair) (s : Fin 3) : SchwartzMap E ℂ :=
  if physical s then actualThinSchwartzField m wi wo hm hη i o z (k s)
  else projectedGaugeComplement z (k s).1 (k s).2

private theorem wardGradientPhaseProduct_bound (f : Fin 3 → SchwartzMap E ℂ) (p : SchwartzMap E ℂ)
    (j : Fin 3) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp : wardCoordinateGradientL3 p ≤ 4 * A) (hf : ∀ s, wardCoordinateGradientL3 (f s) ≤ 4 * B) :
    wardCoordinateGradientL3 (Function.update f j p 0) *
      wardCoordinateGradientL3 (Function.update f j p 1) *
        wardCoordinateGradientL3 (Function.update f j p 2) ≤ 64 * A * B^2 := by
  let t (s : Fin 3) := if s = j then 4 * A else 4 * B
  have hu (s : Fin 3) : wardCoordinateGradientL3 (Function.update f j p s) ≤ t s := by
    by_cases hs : s = j
    · subst s
      simpa only [t, Function.update_self, if_pos rfl] using hp
    · simpa only [t, Function.update_of_ne hs, if_neg hs] using hf s
  have hn (u : SchwartzMap E ℂ) : 0 ≤ wardCoordinateGradientL3 u := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have ht₀ (s : Fin 3) : 0 ≤ t s := by
    unfold t
    split <;> positivity
  refine (mul_le_mul (mul_le_mul (hu 0) (hu 1) (hn _) (ht₀ 0)) (hu 2) (hn _)
    (mul_nonneg (ht₀ 0) (ht₀ 1))).trans_eq ?_
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> decide
  rcases hj with rfl | rfl | rfl
  all_goals
    simp (disch := decide) [t]
    ring

/-- Actual scalar component estimate in the norms used by the C02 patch
argument, with the very same thin and gauge fields in every occurrence. -/
def WardActualLowComponentBound (m : Tensor2) (physical : Fin 3 → Bool) (k : Fin 3 → OrderedPair)
    (A : Joint → ℂ) (C : ℝ) : Prop :=
  ∀ (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) (η : ℝ) (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix),
    let V := actualThinSchwartzField m wi wo hm hη i o z
    let G (b : OrderedPair) := projectedGaugeComplement z b.1 b.2
    let P := actualWardPhaseSchwartz m wi wo hm hη i o z
    let f := wardActualLowSlots m wi wo hm hη i o z physical k
    Integrable (radianTrilinearWeight A (f 0) (f 1) (f 2)) ∧
    ‖radianTrilinearForm A (f 0) (f 1) (f 2)‖ ≤
      C * euclideanFieldGradientL3 P * (euclideanFieldGradientL3 G + euclideanFieldGradientL3 V)^2

theorem exists_wardActualLowComponent_bound {ι : Type*} [Fintype ι]
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (hCut : ∀ t, 1 ≤ t → ϑ t = 0)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) (m : Tensor2)
    (A : Joint → ℂ) (F : ι → WardLowPoint → ℂ) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) wardLowProfileDomain)
    (j : ι → Fin 3) (physical : Fin 3 → Bool) (k : Fin 3 → OrderedPair) (hj : ∀ i, physical (j i) = true)
    (hA : ∀ x ∈ wardLowActive,
      A x = ((‖x.1‖ * ‖x.2‖ * ‖-(x.1+x.2)‖ : ℝ) : ℂ) *
        ∑ i, F i (wardLowInput x) * (normalizedFrozenPhase m (wardPhaseCovector x (j i)) : ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ WardActualLowComponentBound m physical k (wardActualLowCut ϑ κ A) C := by
  classical
  obtain ⟨C, hC, hEst⟩ := exists_wardLowPhaseForm_bound ϑ hϑ hCut κ hκ hSmall m F hF j
  refine ⟨64 * ∑ i, C i, mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hC i), ?_⟩
  intro wi wo hm η hη i o z V G P f
  have hg (b : ι) (ξ : E) : radianFourier (P (k (j b))) ξ =
      (normalizedFrozenPhase m ξ : ℂ) * radianFourier (f (j b)) ξ := by
    have he : f (j b) = V (k (j b)) := by simp [f, wardActualLowSlots, hj, V]
    rw [he]
    exact actualWardPhaseSchwartz_radianFourier m wi wo hm hη i o z (k (j b)) ξ
  obtain ⟨hInt,hNorm⟩ := hEst (wardActualLowCut ϑ κ A) f (fun b => P (k (j b))) hg
    (wardActualLowCut_eq_sum_phases ϑ hCut κ hκ hSmall m A F j hA)
  refine ⟨hInt, hNorm.trans ?_⟩
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
    _ ≤ ∑ s, C s * (64 * a * b^2) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (wardGradientPhaseProduct_bound f (P (k (j s))) (j s) a b (hn P)
        (add_nonneg (hn G) (hn V)) (ward_coordinate_gradient_bound P _) hfn) (hC s)
    _ = _ := by rw [← Finset.sum_mul]; unfold a b; ring

end Burnett.C02
