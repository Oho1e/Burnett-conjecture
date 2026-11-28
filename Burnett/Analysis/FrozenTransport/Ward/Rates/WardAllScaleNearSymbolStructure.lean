import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearActualGradient
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearActualSupport
import Burnett.Analysis.AllScaleTransfer.RadianFourBranchProperties

set_option autoImplicit false
set_option maxRecDepth 8400
set_option maxHeartbeats 15000000

noncomputable section

namespace Burnett.C02

open Set MeasureTheory Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol Burnett.A05
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps hiding Index
open Burnett.V08 (signedCyclicPhase)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix

open private wardWedge_comm from Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearActualSupport
open private lowSlotWeight_smul from Burnett.Analysis.AllScaleTransfer.RadianFourBranchProperties

def wardNearCycleEntries (j : WardNearEntries) : WardNearEntries := (j.2.2,j.1,j.2.1)

theorem wardPurePhysicalNearWeight_cycle (ϑ : ℝ → ℝ) (κ δ : ℝ) (x : Joint) :
    wardPurePhysicalNearWeight ϑ κ δ (radianCycle x) = wardPurePhysicalNearWeight ϑ κ δ x := by
  let p := x.1
  let q := x.2
  let r := -(p+q)
  have hp : -(q+r) = p := by dsimp only [r]; abel
  change comparableSlotWeight ϑ κ q r (-(q+r)) +
    lowSlotWeight ϑ κ q r (-(q+r))*angularNearWeight ϑ δ q r (-(q+r)) +
    lowSlotWeight ϑ κ r (-(q+r)) q*angularNearWeight ϑ δ r (-(q+r)) q +
    lowSlotWeight ϑ κ (-(q+r)) q r*angularNearWeight ϑ δ (-(q+r)) q r =
      comparableSlotWeight ϑ κ p q r + lowSlotWeight ϑ κ p q r*angularNearWeight ϑ δ p q r +
        lowSlotWeight ϑ κ q r p*angularNearWeight ϑ δ q r p +
        lowSlotWeight ϑ κ r p q*angularNearWeight ϑ δ r p q
  rw [hp,← comparableSlotWeight_rotate ϑ κ p q r]
  ring

theorem wardNearGradientSymbol_cycle (G : Mat) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ δ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (j : WardNearEntries) (x : Joint) :
    wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o j (radianCycle x) =
      wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o (wardNearCycleEntries j) x := by
  let p := x.1
  let q := x.2
  let r := -(p+q)
  let T := wardNearScreenColumn G wi wo hm hη i o
  have hp : -(q+r) = p := by dsimp only [r]; abel
  have hα : signedCyclicPhase a q r = signedCyclicPhase a p q := by
    unfold signedCyclicPhase
    rw [hp]
    change a q+a r+a p = a p+a q+a r
    ring
  have hΓ : wardNearCyclicColumn G a wi wo hm hη i o j.1.1 j.2.1.1 j.2.2.1 (radianCycle x) =
      wardNearCyclicColumn G a wi wo hm hη i o j.2.2.1 j.1.1 j.2.1.1 x := by
    change (signedCyclicPhase a q r : ℂ) * complexPrincipalVertex G (fun d => q d) (T j.1.1 q)
      (fun d => r d) (T j.2.1.1 r) (fun d => (-(q+r)) d) (T j.2.2.1 (-(q+r))) =
        (signedCyclicPhase a p q : ℂ) * complexPrincipalVertex G (fun d => p d) (T j.2.2.1 p)
          (fun d => q d) (T j.1.1 q) (fun d => r d) (T j.2.1.1 r)
    rw [hp,hα,← complexPrincipalVertex_cyclic G (fun d => p d) (T j.2.2.1 p)]
  let L := (-Complex.I/3)*(wardPurePhysicalNearWeight ϑ κ δ x : ℂ)
  have hNear := wardPurePhysicalNearWeight_cycle ϑ κ δ x
  unfold wardNearGradientSymbol
  rw [hNear,hΓ]
  change L * (_ / ((‖q‖*‖r‖*‖-(q+r)‖ : ℝ) : ℂ)) *
    (wardNearGradientDirection j.1.2 q * wardNearGradientDirection j.2.1.2 r *
      wardNearGradientDirection j.2.2.2 (-(q+r))) =
    L * (_ / ((‖p‖*‖q‖*‖r‖ : ℝ) : ℂ)) *
      (wardNearGradientDirection j.2.2.2 p * wardNearGradientDirection j.1.2 q *
        wardNearGradientDirection j.2.1.2 r)
  rw [hp,show ‖q‖*‖r‖*‖p‖ = ‖p‖*‖q‖*‖r‖ by ring]
  dsimp only [wardNearCycleEntries]
  ring

private theorem wardScreenColumn_scale (G : Mat) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ}
    (hη : 0 < η) (i o : ℝ) (k : OrderedPair) (t : ℝ) (ht : 0 < t) (ξ : E) :
    wardNearScreenColumn G wi wo hm hη i o k (t • ξ) = wardNearScreenColumn G wi wo hm hη i o k ξ := by
  let S := thinScreenAngular (inverseMatrix G) wi wo hm hη i o
  funext a b
  change (S.matrix (t • ξ) (a,b) k : ℂ) = (S.matrix ξ (a,b) k : ℂ)
  rw [S.degree t ht]

private theorem wardPurePhysicalNearWeight_smul (ϑ : ℝ → ℝ) (κ δ t : ℝ) (ht : 0 < t) (x : Joint) :
    wardPurePhysicalNearWeight ϑ κ δ (t • x) = wardPurePhysicalNearWeight ϑ κ δ x := by
  have hAngular (p q r : E) :
      angularNearWeight ϑ δ (t • p) (t • q) (t • r) = angularNearWeight ϑ δ p q r := by
    have h (x y : E) : projectiveWedgeSq (t • x) (t • y) = projectiveWedgeSq x y := by
      rw [projectiveWedgeSq_smul_left t ht.ne',wardWedge_comm x,
        projectiveWedgeSq_smul_left t ht.ne',wardWedge_comm y x]
    simp only [angularNearWeight,h]
  have he : -(t • x.1+t • x.2) = t • (-(x.1+x.2)) := by rw [smul_neg,smul_add]
  simp only [wardPurePhysicalNearWeight,comparableSlotWeight,Prod.smul_fst,Prod.smul_snd,he,
    lowSlotWeight_smul ϑ κ t ht,hAngular]

theorem wardNearGradientSymbol_homogeneous (G : Mat) (hG : Matrix.det G ≠ 0)
    (a : E → ℝ) (ha : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t*a ξ)
    (ϑ : ℝ → ℝ) (κ δ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (j : WardNearEntries) (t : ℝ) (ht : 0 < t) (x : Joint) :
    wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o j (t • x) =
      wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o j x := by
  let p := x.1
  let q := x.2
  let r := -(p+q)
  let T := wardNearScreenColumn G wi wo hm hη i o
  have hr : -(t • p+t • q) = t • r := by rw [show r = -(p+q) from rfl,smul_neg,smul_add]
  have hDir (k : Index) (ξ : E) : wardNearGradientDirection k (t • ξ) = wardNearGradientDirection k ξ := by
    unfold wardNearGradientDirection
    rw [endpointDirection_pos_smul t ht]
  have hα : signedCyclicPhase a (t • p) (t • q) = t * signedCyclicPhase a p q := by
    simp only [signedCyclicPhase,hr,ha t ht,r]
    ring
  let B := wardNearCyclicColumn G a wi wo hm hη i o j.1.1 j.2.1.1 j.2.2.1 x
  have hNumerator : wardNearCyclicColumn G a wi wo hm hη i o j.1.1 j.2.1.1 j.2.2.1 (t • x) =
      ((t^3 : ℝ) : ℂ) * B := by
    change (signedCyclicPhase a (t • p) (t • q) : ℂ) * complexPrincipalVertex G
      (fun d => (t • p) d) (T j.1.1 (t • p)) (fun d => (t • q) d) (T j.2.1.1 (t • q))
      (fun d => (-(t • p+t • q)) d) (T j.2.2.1 (-(t • p+t • q))) = _
    rw [hr,hα]
    simp only [T,wardScreenColumn_scale G wi wo hm hη i o _ t ht]
    rw [complexPrincipalVertex_frequency_homogeneity G hG (fun d => p d) (fun d => q d) (fun d => r d)]
    simp only [B,wardNearCyclicColumn,p,q,r,Complex.ofReal_mul,Complex.ofReal_pow]
    ring
  let D := ‖p‖*‖q‖*‖r‖
  have hDenom : ‖t • p‖*‖t • q‖*‖t • r‖ = t^3*D := by
    simp only [norm_smul,Real.norm_of_nonneg ht.le,D]
    ring
  unfold wardNearGradientSymbol
  rw [wardPurePhysicalNearWeight_smul ϑ κ δ t ht,hNumerator]
  simp only [Prod.smul_fst,Prod.smul_snd,← show p = x.1 from rfl,← show q = x.2 from rfl,hr,hDir,hDenom]
  rw [Complex.ofReal_mul,mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr (pow_ne_zero 3 ht.ne'))]

/-- A nonzero exact differentiated near coefficient forces the original
near mask and all three physical thin-cone conditions. -/
theorem wardNearGradientSymbol_support (G : Mat) (hG : Matrix.det G ≠ 0)
    (a : E → ℝ) (ϑ : ℝ → ℝ) (κ δ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ}
    (hη : 0 < η) (i o : ℝ) (hi : 0 ≤ i) (hIO : i < o)
    (j : WardNearEntries) (x : Joint)
    (h : wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o j x ≠ 0) :
    let p := x.1
    let q := x.2
    let r := -(p+q)
    p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 ∧ wardPurePhysicalNearWeight ϑ κ δ x ≠ 0 ∧
      InRelativeCone (inverseMatrix G) (o*η) p ∧ InRelativeCone (inverseMatrix G) (o*η) q ∧
      InRelativeCone (inverseMatrix G) (o*η) r := by
  intro p q r
  let S := thinScreenAngular (inverseMatrix G) wi wo hm hη i o
  let T := wardNearScreenColumn G wi wo hm hη i o
  have hDenom : ‖p‖*‖q‖*‖r‖ ≠ 0 := by
    intro he
    apply h
    unfold wardNearGradientSymbol
    change _ * (_ / ((‖p‖*‖q‖*‖r‖ : ℝ) : ℂ)) * _ = 0
    simp only [he,Complex.ofReal_zero,div_zero,mul_zero,zero_mul]
  obtain ⟨⟨hp,hq⟩,hr⟩ := mul_ne_zero_iff.mp hDenom |>.imp_left mul_ne_zero_iff.mp
  have hn : wardPurePhysicalNearWeight ϑ κ δ x ≠ 0 := by
    intro he
    exact h (by simp only [wardNearGradientSymbol,he,Complex.ofReal_zero,mul_zero,zero_mul])
  have hCore : complexPrincipalVertex G (fun d => p d) (T j.1.1 p)
      (fun d => q d) (T j.2.1.1 q) (fun d => r d) (T j.2.2.1 r) ≠ 0 := by
    intro he
    apply h
    simp only [wardNearGradientSymbol,wardNearCyclicColumn,← show p = x.1 from rfl,
      ← show q = x.2 from rfl,← show r = -(p+q) from rfl,← show T = wardNearScreenColumn _ _ _ _ _ _ _ from rfl,
      he,mul_zero,zero_div,zero_mul]
  let χ := thinConeProfile (inverseMatrix G) η i o
  have hZero (k : OrderedPair) (ξ : E) (hz : χ ξ = 0) : T k ξ = 0 := by
    funext a b
    change (S.matrix ξ (a,b) k : ℂ) = 0
    change ((χ ξ * (wideScreenAngular wi wo (inverseMatrix G) hm).matrix ξ (a,b) k : ℝ) : ℂ) = 0
    rw [hz,zero_mul,Complex.ofReal_zero]
  have hχ₀ : χ p ≠ 0 := by
    intro hz
    apply hCore
    rw [hZero _ _ hz,show (0 : ComplexTensor2) = (0 : ℂ) • T j.1.1 p by simp,
      complexPrincipalVertex_smul_first_amplitude G hG,zero_mul]
  have hχ₁ : χ q ≠ 0 := by
    intro hz
    apply hCore
    rw [hZero _ _ hz,show (0 : ComplexTensor2) = (0 : ℂ) • T j.2.1.1 q by simp,
      complexPrincipalVertex_smul_second_amplitude G hG,zero_mul]
  have hχ₂ : χ r ≠ 0 := by
    intro hz
    apply hCore
    rw [hZero _ _ hz,show (0 : ComplexTensor2) = (0 : ℂ) • T j.2.2.1 r by simp,
      complexPrincipalVertex_smul_third_amplitude G hG,zero_mul]
  have hP := norm_ne_zero_iff.mp hp
  have hQ := norm_ne_zero_iff.mp hq
  have hR := norm_ne_zero_iff.mp hr
  exact ⟨hP,hQ,hR,hn,(thinConeProfile_nonzero_cone hη hi hIO hP hχ₀).le,
    (thinConeProfile_nonzero_cone hη hi hIO hQ hχ₁).le,(thinConeProfile_nonzero_cone hη hi hIO hR hχ₂).le⟩

end Burnett.C02
