import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleFarWardNumerator
import Burnett.Analysis.FrozenTransport.Ward.WardAllScalePurePhysicalDecomposition
import Burnett.Analysis.FrozenTransport.Ward.WardLowTransferDerivatives

set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 8200

noncomputable section

namespace Burnett.C02

open Matrix MeasureTheory Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol Burnett.Analysis.CapFourier
open Burnett.V08 (signedCyclicPhase)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix projectionFullSchwartz)
open Burnett.A07 (coordinateDerivative)
open Burnett.A05 (endpointDirection)

open private wardVertex_expand_column_sums from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleFarWardNumerator
open private directionDerivativeCoefficient sum_mul_three from Burnett.Analysis.FrozenTransport.Ward.WardLowTransferDerivatives

abbrev WardNearSlot := OrderedPair × Index
abbrev WardNearEntries := WardNearSlot × WardNearSlot × WardNearSlot

/-- The derivative of the same infrared-regularized receiving projection
which enters the actual thin physical spectrum. -/
def wardNearGradient (z : ProjectionSchwartzMatrix) (j : WardNearSlot) : SchwartzMap E ℂ :=
  coordinateDerivative j.2 (projectionFullSchwartz z j.1.1 j.1.2)

def wardNearGradientDirection (j : Index) (p : E) : ℂ :=
  directionDerivativeCoefficient (endpointDirection p) j

def wardNearScreenColumn (G : Mat) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G))
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (j : OrderedPair) (p : E) : ComplexTensor2 :=
  fun s t => (thinScreenAngular (inverseMatrix G) wi wo hm hη i o).complex p (s,t) j

def wardNearCyclicColumn (G : Mat) (a : E → ℝ) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (k j l : OrderedPair) (x : Joint) : ℂ :=
  let p := x.1
  let q := x.2
  let r := -(p+q)
  let T := wardNearScreenColumn G wi wo hm hη i o
  (signedCyclicPhase a p q : ℂ) * complexPrincipalVertex G
    (fun d => p d) (T k p) (fun d => q d) (T j q) (fun d => r d) (T l r)

/-- The actual full near weight on three ordinary coordinate derivatives.
At a zero slot the denominator makes the coefficient zero. All three
spectra of the actual physical term already vanish there. -/
def wardNearGradientSymbol (G : Mat) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ δ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (j : WardNearEntries) (x : Joint) : ℂ :=
  let r := -(x.1+x.2)
  (-Complex.I/3) * (wardPurePhysicalNearWeight ϑ κ δ x : ℂ) *
    (wardNearCyclicColumn G a wi wo hm hη i o j.1.1 j.2.1.1 j.2.2.1 x /
      ((‖x.1‖*‖x.2‖*‖r‖ : ℝ) : ℂ)) *
    (wardNearGradientDirection j.1.2 x.1 * wardNearGradientDirection j.2.1.2 x.2 *
      wardNearGradientDirection j.2.2.2 r)

private theorem wardNear_radialExpansion (B : ℂ) (f g h : SchwartzMap E ℂ) (x : Joint) :
    let r := -(x.1+x.2)
    B * (((‖x.1‖*‖x.2‖*‖r‖ : ℝ) : ℂ) *
      (radianFourier f x.1 * radianFourier g x.2 * radianFourier h r)) =
      ∑ t : WardDerivativeAxes, radianTrilinearWeight
        (fun y => B * (wardNearGradientDirection t.1 y.1 * wardNearGradientDirection t.2.1 y.2 *
          wardNearGradientDirection t.2.2 (-(y.1+y.2))))
        (coordinateDerivative t.1 f) (coordinateDerivative t.2.1 g) (coordinateDerivative t.2.2 h) x := by
  intro r
  have hRad (f : SchwartzMap E ℂ) (p : E) := ward_radialFourier_eq_sum_coordinateDerivative f p
  let P (t : Index) := wardNearGradientDirection t x.1 * radianFourier (coordinateDerivative t f) x.1
  let Q (t : Index) := wardNearGradientDirection t x.2 * radianFourier (coordinateDerivative t g) x.2
  let R (t : Index) := wardNearGradientDirection t r * radianFourier (coordinateDerivative t h) r
  calc
    _ = B * (((‖x.1‖ : ℂ) * radianFourier f x.1) * ((‖x.2‖ : ℂ) * radianFourier g x.2) *
        ((‖r‖ : ℂ) * radianFourier h r)) := by push_cast; ring
    _ = B * ((∑ t, P t) * (∑ t, Q t) * (∑ t, R t)) := by
      rw [hRad f x.1,hRad g x.2,hRad h r]
      simp only [P,Q,R,wardNearGradientDirection]
    _ = _ := by
      rw [sum_mul_three,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      simp only [radianTrilinearWeight,radianWeight,Complex.ofReal_one,one_mul,P,Q,R,r]
      ring

private theorem wardNear_entrySum (G : Mat) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ δ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) (k j l : OrderedPair) (x : Joint)
    (hp : x.1 ≠ 0) (hq : x.2 ≠ 0) (hr : -(x.1+x.2) ≠ 0) :
    let f := projectionFullSchwartz z k.1 k.2
    let g := projectionFullSchwartz z j.1 j.2
    let h := projectionFullSchwartz z l.1 l.2
    let B := (-Complex.I/3) * (wardPurePhysicalNearWeight ϑ κ δ x : ℂ) *
      wardNearCyclicColumn G a wi wo hm hη i o k j l x
    B * (radianFourier f x.1 * radianFourier g x.2 * radianFourier h (-(x.1+x.2))) =
      ∑ t : WardDerivativeAxes, radianTrilinearWeight
        (wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o ((k,t.1),(j,t.2.1),(l,t.2.2)))
        (wardNearGradient z (k,t.1)) (wardNearGradient z (j,t.2.1))
        (wardNearGradient z (l,t.2.2)) x := by
  intro f g h B
  let r := -(x.1+x.2)
  let N := ((‖x.1‖*‖x.2‖*‖r‖ : ℝ) : ℂ)
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (norm_ne_zero_iff.mpr hp) (norm_ne_zero_iff.mpr hq)) (norm_ne_zero_iff.mpr hr))
  have e := wardNear_radialExpansion (B/N) f g h x
  change (B/N) * (N * _) = _ at e
  rw [← mul_assoc,div_mul_cancel₀ _ hN] at e
  refine e.trans ?_
  apply Finset.sum_congr rfl
  intro t _
  simp only [radianTrilinearWeight,wardNearGradientSymbol,wardNearGradient,f,g,h,B,N,r]
  ring

private theorem wardNear_rearrange {J D : Type*} [Fintype J] [Fintype D]
    (w : J → J → J → D → D → D → ℂ) :
    (∑ l : J, ∑ j : J, ∑ k : J, ∑ t : D × D × D, w k j l t.1 t.2.1 t.2.2) =
      ∑ v : (J × D) × (J × D) × (J × D), w v.1.1 v.2.1.1 v.2.2.1 v.1.2 v.2.1.2 v.2.2.2 := by
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ j : J, ∑ l : J, ∑ k : J, ∑ s : D, ∑ t : D, ∑ d : D, w k j l s t d := Finset.sum_comm
    _ = ∑ j : J, ∑ k : J, ∑ l : J, ∑ s : D, ∑ t : D, ∑ d : D, w k j l s t d :=
      Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ k : J, ∑ j : J, ∑ l : J, ∑ s : D, ∑ t : D, ∑ d : D, w k j l s t d := Finset.sum_comm
    _ = ∑ k : J, ∑ j : J, ∑ s : D, ∑ l : J, ∑ t : D, ∑ d : D, w k j l s t d :=
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ k : J, ∑ s : D, ∑ j : J, ∑ l : J, ∑ t : D, ∑ d : D, w k j l s t d :=
      Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_comm

/-- The true near numerator is the finite sum of actual radian
trilinear weights on the projected coordinate gradients. -/
theorem wardActualNearWeight_eq_gradientSum (G : Mat) (hG : Matrix.det G ≠ 0)
    (a : E → ℝ) (ϑ : ℝ → ℝ) (κ δ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) (x : Joint) :
    let H := wardActualThinSpectrum (inverseMatrix G) wi wo hm hη i o z
    (wardPurePhysicalNearWeight ϑ κ δ x : ℂ) * wardCyclicCubicWeight G a H H H x =
      ∑ j : WardNearEntries, radianTrilinearWeight (wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o j)
        (wardNearGradient z j.1) (wardNearGradient z j.2.1) (wardNearGradient z j.2.2) x := by
  intro H
  let p := x.1
  let q := x.2
  let r := -(p+q)
  let u (k : OrderedPair) := projectionFullSchwartz z k.1 k.2
  let T := wardNearScreenColumn G wi wo hm hη i o
  have decompose (ξ : E) : H ξ = ∑ k : OrderedPair, radianFourier (u k) ξ • T k ξ := by
    funext b c
    refine (wardActualThinSpectrum_eq_sum _ _ _ hm hη i o z ξ (b,c)).trans ?_
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hV := wardVertex_expand_column_sums G hG (fun d => p d) (fun d => q d) (fun d => r d)
    (fun k => T k p) (fun k => T k q) (fun k => T k r)
    (fun k => radianFourier (u k) p) (fun k => radianFourier (u k) q) (fun k => radianFourier (u k) r)
  by_cases h₀ : p = 0 ∨ q = 0 ∨ r = 0
  · have hSpec (ξ : E) (hξ : ξ = 0) (k : OrderedPair) : radianFourier (u k) ξ = 0 := by
      subst ξ
      rw [Burnett.P01.projectionFullSchwartz_radianFourier]
      simp only [Burnett.P01.regularizedComplexGaugeProjection,norm_zero,
        Burnett.P01.gaugeProjectionInfrared_zero (by norm_num : (0:ℝ) ≤ 1),
        Complex.ofReal_zero,zero_smul,Matrix.zero_apply]
    have hSumZero (k j l : OrderedPair) :
        radianFourier (u l) r * (radianFourier (u j) q * (radianFourier (u k) p *
          complexPrincipalVertex G (fun d => p d) (T k p) (fun d => q d) (T j q) (fun d => r d) (T l r))) = 0 := by
      rcases h₀ with hp|hq|hr
      · simp only [hSpec _ hp, mul_zero,zero_mul]
      · simp only [hSpec _ hq, mul_zero,zero_mul]
      · simp only [hSpec _ hr,zero_mul]
    have hExpandZero : complexPrincipalVertex G (fun d => p d) (H p) (fun d => q d) (H q)
        (fun d => r d) (H r) = 0 := by
      rw [decompose p,decompose q,decompose r,hV]
      simp only [hSumZero,Finset.sum_const_zero]
    have hNormZero : ‖p‖*‖q‖*‖r‖ = 0 := by
      rcases h₀ with hp|hq|hr
      · simp only [hp,norm_zero,zero_mul]
      · simp only [hq,norm_zero,mul_zero,zero_mul]
      · simp only [hr,norm_zero,mul_zero]
    have hLost (j : WardNearEntries) : wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o j x = 0 := by
      simp only [wardNearGradientSymbol,← show p = x.1 from rfl,← show q = x.2 from rfl,
        ← show r = -(p+q) from rfl,hNormZero,Complex.ofReal_zero,div_zero,mul_zero,zero_mul]
    simp only [wardCyclicCubicWeight,← show p = x.1 from rfl,← show q = x.2 from rfl,
      ← show r = -(p+q) from rfl,hExpandZero,hLost,radianTrilinearWeight,zero_mul,mul_zero,Finset.sum_const_zero]
  · push_neg at h₀
    obtain ⟨hp,hq,hr⟩ := h₀
    let v (k j l : OrderedPair) := (-Complex.I/3) * (wardPurePhysicalNearWeight ϑ κ δ x : ℂ) *
      wardNearCyclicColumn G a wi wo hm hη i o k j l x *
      (radianFourier (u k) p * radianFourier (u j) q * radianFourier (u l) r)
    let w (k j l : OrderedPair) (s t d : Index) := radianTrilinearWeight
      (wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o ((k,s),(j,t),(l,d)))
      (wardNearGradient z (k,s)) (wardNearGradient z (j,t)) (wardNearGradient z (l,d)) x
    calc
      _ = ∑ l : OrderedPair, ∑ j : OrderedPair, ∑ k : OrderedPair, v k j l := by
        change _ * ((-Complex.I/3) * (signedCyclicPhase a p q : ℂ) * complexPrincipalVertex G
          (fun d => p d) (H p) (fun d => q d) (H q) (fun d => r d) (H r)) = _
        rw [decompose p,decompose q,decompose r,hV]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => ?_
        dsimp only [v,wardNearCyclicColumn,p,q,r]
        ring
      _ = ∑ l : OrderedPair, ∑ j : OrderedPair, ∑ k : OrderedPair, ∑ t : WardDerivativeAxes,
          w k j l t.1 t.2.1 t.2.2 := by
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => wardNear_entrySum G a ϑ κ δ wi wo hm hη i o z k j l x hp hq hr
      _ = _ := wardNear_rearrange w

end Burnett.C02
