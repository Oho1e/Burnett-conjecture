import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearFixedCapProfile

set_option autoImplicit false
set_option maxRecDepth 9300
set_option maxHeartbeats 16000000

noncomputable section

namespace Burnett.C02

open Set Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.CapFourier
open Burnett.A05 (endpointDirection_pos_smul)
open scoped ContDiff Matrix

private theorem wardNearGradientDirection_pos_smul (j : Fin 4) (t : ℝ) (ht : 0 < t) (p : E) :
    wardNearGradientDirection j (t • p) = wardNearGradientDirection j p := by
  unfold wardNearGradientDirection
  rw [endpointDirection_pos_smul t ht]

/-- Exact comparison between the jointly smooth profile and the original
localized near coefficient at nonzero width and genuine branch inputs.
The cap selector accounts for the cyclic relabeling of the base slot. -/
theorem wardParabolicNearProfile_eq_actual {N : ℕ} (V : Set E)
    (G : E → Mat) (c : E) (hG : Matrix.det (G c) ≠ 0)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0})
    (hOdd : ∀ ξ, a (c,-ξ) = -a (c,ξ))
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (c,t • ξ) = t * a (c,ξ))
    (b : ℝ) (M : WardParabolicTestPoint → ℝ) (hM : ContDiff ℝ ∞ M)
    (hExt : EqOn (wardJointParabolicTestRemainder a) M (wardParabolicTestDomain b))
    (ϑ : ℝ → ℝ) (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16)
    (tube δ thinIn thinOut capIn capOut : ℝ) (hδ : δ ≠ 0) (hη : 0 < tube*δ^2)
    (w : E) (F : NullCapChart (inverseMatrix (G c)) w) (t : Finset E)
    (W : E → E → Burnett.Microlocal.PhysicalDensity.OrderedPair →
      Burnett.Microlocal.PhysicalDensity.OrderedPair → ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix (G c)))
    (hWide : ∀ ξ, ∀ k j, W c ξ k j = (wideScreenAngular wi wo (inverseMatrix (G c)) hm).matrix ξ k j)
    (v : CapNeighborParameters N)
    (hEncoded : ∀ x : NullFrequencyCoordinates, x.1 ≠ 0 →
      capMultiplier t (inverseMatrix (G c)) δ (tube*δ^2) capIn capOut w (chartScaledFrequency F δ x) =
        parabolicBaseProfile F.toFrequency.toContinuousLinearMap tube δ capIn capOut v x)
    (u θ : NullFrequencyCoordinates) (ρ : ℝ) (hρ : 0 < ρ) (comparable : Bool)
    (hComp : comparable = true → ρ = 1) (s : Fin 3) (j : WardNearEntries) :
    let x : WardNearProfileInput N := (((c,F.toFrequency.toContinuousLinearMap,δ),v),u,θ,ρ)
    let A := (parabolicDilationEquiv hδ).trans F.toFrequency
    let p := A (ρ • u)
    let q := A θ
    let r := A (-(ρ • u+θ))
    let y : Joint := (p,q)
    let P := capMultiplier t (inverseMatrix (G c)) δ (tube*δ^2) capIn capOut w
    let L := if comparable then comparableSlotWeight ϑ κ p q r else lowSlotWeight ϑ κ p q r
    x ∈ wardParabolicNearProfileDomain N V tube b s →
    wardParabolicNearProfile G W M ϑ κ tube thinIn thinOut capIn capOut comparable s j x =
      (δ^2)⁻¹ • ((P (![p,q,r] s) : ℂ) * (L : ℂ) *
        wardNearGradientSymbol (G c) (fun ξ => a (c,ξ)) ϑ κ δ wi wo hm hη thinIn thinOut j y) := by
  intro x A p q r y P L hx
  let z := θ+ρ • u
  have hp : p = ρ • A u := A.map_smul ρ u
  have hr : r = -(A z) := by
    change A (-(ρ • u+θ)) = -(A (θ+ρ • u))
    rw [add_comm (ρ • u),map_neg]
  have hs : r = -(p+q) := by
    change A (-(ρ • u+θ)) = -(A (ρ • u)+A θ)
    rw [map_neg,map_add]
  have hSum : p+q+r = 0 := by rw [hs,add_neg_cancel]
  have hu := (hx.2.2 0).1
  have hθ := (hx.2.2 1).1
  have hz := (hx.2.2 2).1
  have au : A u ≠ 0 := fun e => hu (congrArg Prod.fst (A.injective (e.trans A.map_zero.symm)))
  have aq : q ≠ 0 := fun e => hθ (congrArg Prod.fst (A.injective (e.trans A.map_zero.symm)))
  have ar : r ≠ 0 := by
    rw [hr]
    exact neg_ne_zero.mpr (fun e => hz (congrArg Prod.fst (A.injective (e.trans A.map_zero.symm))))
  have ap : p ≠ 0 := by rw [hp]; exact smul_ne_zero hρ.ne' au
  have hCore := wardParabolicLowScreenedCore_eq_actual G a c hG ha hOdd hHom b M hM hExt w F
    W wi wo hm hWide tube δ thinIn thinOut hδ hη u θ ρ hρ hu hθ hz
    (hx.2.2 0).2 (hx.2.2 1).2 (hx.2.2 2).2 j.1.1 j.2.1.1 j.2.2.1
  let B := wardNearCyclicColumn (G c) (fun ξ => a (c,ξ)) wi wo hm hη thinIn thinOut
    j.1.1 j.2.1.1 j.2.2.1 y
  let D := ‖p‖*‖q‖*‖r‖
  have hVertex : wardParabolicLowScreenedCore G W M tube thinIn thinOut j.1.1 j.2.1.1 j.2.2.1
      (wardNearProfileCorePoint x) = B / ((δ^2*D : ℝ) : ℂ) := by
    symm
    simpa only [B,D,y,wardNearCyclicColumn,Burnett.V08.signedCyclicPhase,← hs] using hCore
  have hBase : parabolicBaseProfile F.toFrequency.toContinuousLinearMap tube δ capIn capOut v
      (wardNearProfileArguments x s) = P (![p,q,r] s) := by
    rw [← hEncoded _ (hx.2.2 s).1]
    change P (A (wardNearProfileArguments x s)) = P (![p,q,r] s)
    fin_cases s
    · change P (A u) = P p
      rw [hp]
      exact (capMultiplier_degreeZero t _ δ _ capIn capOut w ρ hρ.ne' (A u)).symm
    · rfl
    · change P (A z) = P r
      rw [hr]
      simpa only [neg_one_smul] using (capMultiplier_degreeZero t _ δ _ capIn capOut w
        (-1 : ℝ) (by norm_num) (A z)).symm
  have hMask : (if comparable then wardParabolicComparableNearBranchWeight ϑ F.toFrequency.toContinuousLinearMap
      δ κ u θ (-z) else wardParabolicLowNearBranchWeight ϑ F.toFrequency.toContinuousLinearMap
      δ κ ρ u θ z) = L*wardPurePhysicalNearWeight ϑ κ δ y := by
    cases comparable
    · have hSum' : ρ • A u+q+-(A z) = 0 := by rwa [← hp,← hr]
      have hp' : ρ • A u ≠ 0 := by rwa [← hp]
      have hr' : -(A z) ≠ 0 := by rwa [← hr]
      have e := wardParabolicLowNearBranchWeight_eq_actual ϑ hCut hκ hκsmall
        F.toFrequency.toContinuousLinearMap hδ ρ hρ.ne' u θ hSum' hp' aq hr'
      change _ = lowSlotWeight ϑ κ (ρ • A u) q (-(A z)) *
        wardPurePhysicalNearWeight ϑ κ δ (ρ • A u,q) at e
      rw [← hp,← hr] at e
      simpa only [L,Bool.false_eq_true,if_false,y] using e
    · have hρ' := hComp rfl
      have hp' : A u = p := by change A u = A (ρ • u); rw [hρ',one_smul]
      have hr' : A (-z) = r := by rw [map_neg,hr]
      have h := wardParabolicComparableNearBranchWeight_eq_actual ϑ F.toFrequency.toContinuousLinearMap
        δ κ hδ u θ (-z)
      change A u+q+A (-z) = 0 → _ = comparableSlotWeight ϑ κ (A u) q (A (-z)) *
        wardPurePhysicalNearWeight ϑ κ δ (A u,q) at h
      rw [hp',hr'] at h
      simpa only [L,if_true,y] using h hSum
  have hDir : wardNearGradientDirection j.1.2 (A u) = wardNearGradientDirection j.1.2 p := by
    rw [hp,wardNearGradientDirection_pos_smul _ ρ hρ]
  change (-Complex.I/3) * ((if comparable then wardParabolicComparableNearBranchWeight ϑ
      F.toFrequency.toContinuousLinearMap δ κ u θ (-z) else wardParabolicLowNearBranchWeight ϑ
      F.toFrequency.toContinuousLinearMap δ κ ρ u θ z : ℝ) : ℂ) *
    (parabolicBaseProfile F.toFrequency.toContinuousLinearMap tube δ capIn capOut v
      (wardNearProfileArguments x s) : ℂ) *
    wardParabolicLowScreenedCore G W M tube thinIn thinOut j.1.1 j.2.1.1 j.2.2.1 (wardNearProfileCorePoint x) *
    (wardNearGradientDirection j.1.2 (A u) * wardNearGradientDirection j.2.1.2 q *
      wardNearGradientDirection j.2.2.2 (-(A z))) = _
  rw [hMask,hBase,hVertex,hDir,← hr]
  change _ = (δ^2)⁻¹ • ((P (![p,q,r] s) : ℂ) * (L : ℂ) *
    ((-Complex.I/3) * (wardPurePhysicalNearWeight ϑ κ δ y : ℂ) *
    (B/((‖p‖*‖q‖*‖-(p+q)‖ : ℝ) : ℂ)) *
    (wardNearGradientDirection j.1.2 p * wardNearGradientDirection j.2.1.2 q *
      wardNearGradientDirection j.2.2.2 (-(p+q)))))
  rw [← hs]
  simp only [D,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv,div_eq_mul_inv,mul_inv_rev]
  ring

end Burnett.C02
