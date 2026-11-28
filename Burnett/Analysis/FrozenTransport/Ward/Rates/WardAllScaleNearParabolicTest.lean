import Burnett.Analysis.FrozenTransport.V03SegmentTaylor
import Burnett.Analysis.AngularCaps.ParabolicProfileSmoothness
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency

set_option autoImplicit false
set_option maxRecDepth 6400
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.C02

open Set MeasureTheory Burnett.Analysis.ProjectiveNullCaps Burnett.V03
open Burnett.A02.FrequencySplit (E)
open scoped ContDiff Interval

private theorem wardDegreeOne_signed (a : E → ℝ)
    (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ) :
    ∀ t : ℝ, ∀ ξ, a (t • ξ) = t * a ξ := by
  intro t ξ
  rcases lt_trichotomy 0 t with h | h | h
  · exact hHom t h ξ
  · subst t
    simp only [zero_smul, zero_mul]
    have h := hOdd 0
    rw [neg_zero] at h
    linarith only [h]
  · have ht := hHom (-t) (neg_pos.mpr h) ξ
    rw [neg_smul, hOdd] at ht
    linarith only [ht]

private theorem wardRay_fderiv (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hHom : ∀ t : ℝ, ∀ ξ, a (t • ξ) = t * a ξ)
    (e : E) (he : e ≠ 0) (s : ℝ) (hs : s ≠ 0) :
    fderiv ℝ a (s • e) = fderiv ℝ a e := by
  have hOpen : IsOpen {ξ : E | ξ ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  have hE := (ha.contDiffAt (hOpen.mem_nhds he)).differentiableAt (by simp)
  have hS := (ha.contDiffAt (hOpen.mem_nhds (smul_ne_zero hs he))).differentiableAt (by simp)
  have hL : HasFDerivAt (fun ξ : E => s • ξ) (s • ContinuousLinearMap.id ℝ E) e :=
    (hasFDerivAt_id e).const_smul s
  have hComp := hS.hasFDerivAt.comp e hL
  have hEq : (fun ξ : E => a (s • ξ)) = (fun ξ => s • a ξ) := funext (hHom s)
  change HasFDerivAt (fun ξ : E => a (s • ξ))
    ((fderiv ℝ a (s • e)).comp (s • ContinuousLinearMap.id ℝ E)) e at hComp
  rw [hEq] at hComp
  have hD := hComp.unique (hE.hasFDerivAt.const_smul s)
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hD
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at hv
  exact mul_left_cancel₀ hs hv

private theorem wardRay_euler (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hHom : ∀ t : ℝ, ∀ ξ, a (t • ξ) = t * a ξ)
    (e : E) (he : e ≠ 0) :
    (fderiv ℝ a e) e = a e := by
  have hOpen : IsOpen {ξ : E | ξ ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  have hE : HasFDerivAt a (fderiv ℝ a e) ((1 : ℝ) • e) := by
    rw [one_smul]
    exact ((ha.contDiffAt (hOpen.mem_nhds he)).differentiableAt (by simp)).hasFDerivAt
  have hRay : HasDerivAt (fun t : ℝ => t • e) e 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const e
  have hComp : HasDerivAt (fun t : ℝ => a (t • e)) ((fderiv ℝ a e) e) 1 :=
    hE.comp_hasDerivAt 1 hRay
  rw [funext (fun t => hHom t e)] at hComp
  have hLin : HasDerivAt (fun t : ℝ => t * a e) (a e) 1 := by
    simpa only [id_eq,one_mul] using (hasDerivAt_id (1 : ℝ)).mul_const (a e)
  exact hComp.unique hLin

/-- The divided parabolic Taylor remainder on either signed axial cone.
It is expressed directly as an integral, including at zero width. -/
def wardParabolicTestRemainder (a : E → ℝ) (F : NullCoordinateMap) (δ : ℝ)
    (u : NullFrequencyCoordinates) : ℝ :=
  let e := F nullAxis
  let v := F (parabolicRemainder δ u)
  ∫ t in (0 : ℝ)..1, (1-t) * secondFDeriv a (u.1 • e + t • (δ • v)) v v

theorem wardParabolicTestRemainder_eq (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (F : NullFrequencyCoordinates ≃L[ℝ] E) (δ : ℝ) (u : NullFrequencyCoordinates) (hu : u.1 ≠ 0) :
    a (F (parabolicDilation δ u)) - (fderiv ℝ a (F nullAxis)) (F (parabolicDilation δ u)) =
      δ^2 * wardParabolicTestRemainder a F.toContinuousLinearMap δ u := by
  let e := F nullAxis
  let v := F (parabolicRemainder δ u)
  let g := u.1 • e
  let h := δ • v
  have hOpen : IsOpen {ξ : E | ξ ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  have hS := wardDegreeOne_signed a hOdd hHom
  have he : e ≠ 0 := by
    intro h0
    have hAxis := F.injective (h0.trans F.map_zero.symm)
    have hf := congrArg Prod.fst hAxis
    norm_num [nullAxis] at hf
  have hSeg (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) : fieldSegment g h t ≠ 0 := by
    dsimp only [fieldSegment, g, h, e, v]
    simp only [← F.map_smul, ← F.map_add]
    intro h0
    have hP := congrArg Prod.fst (F.injective (h0.trans F.map_zero.symm))
    have hv : u.1 = 0 := by simpa [nullAxis, parabolicRemainder] using hP
    exact hu hv
  have hT := linearTaylorRemainder_eq_integral a hOpen ha g h hSeg
  have hD : fderiv ℝ a g = fderiv ℝ a e := wardRay_fderiv a ha hS e he u.1 hu
  have hLin : (fderiv ℝ a e) g = a g := by
    dsimp only [g]
    simp only [map_smul, hS u.1 e, wardRay_euler a ha hS e he, smul_eq_mul]
  have hPar : F (parabolicDilation δ u) = g+h := by
    rw [parabolicDilation_split, F.map_add, F.map_smul, F.map_smul]
  rw [hPar]
  calc
    _ = linearTaylorRemainder a g h := by
      rw [linearTaylorRemainder, hD, map_add, hLin]
      ring
    _ = ∫ t in (0 : ℝ)..1, (1-t) • secondFDeriv a (fieldSegment g h t) h h := hT
    _ = _ := by
      unfold wardParabolicTestRemainder
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      change (1-t) • secondFDeriv a (g+t • h) h h = δ^2 * ((1-t) * secondFDeriv a (g+t • h) v v)
      simp only [h, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring

private theorem wardParabolicDilation_neg_add (δ : ℝ) (p q : NullFrequencyCoordinates) :
    parabolicDilation δ (-(p+q)) = -(parabolicDilation δ p + parabolicDilation δ q) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change δ^2 * -(p.2.1+q.2.1) = -(δ^2*p.2.1+δ^2*q.2.1)
      ring
    · change δ • -(p.2.2+q.2.2) = -(δ • p.2.2 + δ • q.2.2)
      rw [smul_neg,smul_add]

/-- For an actual parabolic-chart triad the same linear jet cancels
exactly from all three test placements, leaving the factor `δ²`. -/
theorem wardParabolicCyclicTest_eq (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (F : NullFrequencyCoordinates ≃L[ℝ] E) (δ : ℝ) (p q : NullFrequencyCoordinates)
    (hp : p.1 ≠ 0) (hq : q.1 ≠ 0) (hr : (-(p+q)).1 ≠ 0) :
    let r := -(p+q)
    let A (u : NullFrequencyCoordinates) := F (parabolicDilation δ u)
    let M := wardParabolicTestRemainder a F.toContinuousLinearMap δ
    a (A p) + a (A q) + a (A r) = δ^2 * (M p + M q + M r) := by
  intro r A M
  let L := fderiv ℝ a (F nullAxis)
  have hS : A p + A q + A r = 0 := by
    have he : A r = -(A p + A q) := by
      dsimp only [A, r]
      rw [wardParabolicDilation_neg_add, map_neg, map_add]
    rw [he, add_neg_cancel]
  have hL : L (A p) + L (A q) + L (A r) = 0 := by
    rw [← map_add, ← map_add, hS, map_zero]
  have h₀ : a (A p) - L (A p) = δ^2 * M p := wardParabolicTestRemainder_eq a ha hOdd hHom F δ p hp
  have h₁ : a (A q) - L (A q) = δ^2 * M q := wardParabolicTestRemainder_eq a ha hOdd hHom F δ q hq
  have h₂ : a (A r) - L (A r) = δ^2 * M r := wardParabolicTestRemainder_eq a ha hOdd hHom F δ r hr
  linear_combination h₀ + h₁ + h₂ + hL

end Burnett.C02
