import Burnett.Analysis.TransportWard.Weyl.WindowedWeylLeftAction
import Burnett.Analysis.PrincipalEnergy.Localization.GlobalCoordinateActionBounds

/-! Convert the scaled joint jets in A03 to the actual A01 mixed jets,
retaining the correct frequency decay after a spatial differentiation. -/

set_option autoImplicit false
set_option maxHeartbeats 7500000
set_option maxRecDepth 4400

noncomputable section

namespace Burnett.V03

open Function MeasureTheory Metric Set Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic Burnett.Analysis.CarlesonEmbedding
open scoped ContDiff Topology BigOperators

local notation "P" => RadianParameter
local notation "W" => radianFrequencyWeight

/-- The usual order-one bounds evaluated on frequency-normalized joint directions. -/
structure ScaledJointOrderOne (a : E → E → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ (uncurry a)
  bound : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P,
    ‖radianScaledParameterJet (uncurry a) k p‖ ≤ C * W p.2

private theorem scaled_mixed_norm_le_joint (a : E → E → ℂ)
    (h : ContDiff ℝ ∞ (uncurry a)) (m n : ℕ) (x ξ : E) :
    W ξ ^ n * ‖iteratedFDeriv ℝ m (fun y => iteratedFDeriv ℝ n (a y) ξ) x‖ ≤
      ‖radianScaledParameterJet (uncurry a) (n+m) (x,ξ)‖ := by
  let s := W ξ
  let A (y ζ : E) := a (x+y) (ξ+s • ζ)
  have hA : ContDiff ℝ ∞ (uncurry A) := by
    change ContDiff ℝ ∞ (uncurry a ∘ (fun p : P => (x,ξ)+radianParameterScale s p))
    exact h.comp (contDiff_const.add (radianParameterScale s).contDiff)
  have freq (y : E) : iteratedFDeriv ℝ n (A y) 0 = s^n • iteratedFDeriv ℝ n (a (x+y)) ξ := by
    let L : E →L[ℝ] E := s • ContinuousLinearMap.id ℝ E
    have LC : A y = fun ζ => a (x+y) (ξ+L ζ) := rfl
    have smooth : ContDiff ℝ ∞ (a (x+y)) := h.comp (contDiff_const.prodMk contDiff_id)
    rw [LC,iteratedFDeriv_affine_actual _ smooth L ξ 0 n,map_zero,add_zero]
    ext v
    change iteratedFDeriv ℝ n (a (x+y)) ξ (fun j => s • v j) =
      s^n • iteratedFDeriv ℝ n (a (x+y)) ξ v
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      (iteratedFDeriv ℝ n (a (x+y)) ξ).toMultilinearMap.map_smul_univ (fun _ => s) v
  let Q (y : E) := iteratedFDeriv ℝ n (a y) ξ
  let L : (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) →L[ℝ]
      (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) :=
    ContinuousLinearMap.lsmul ℝ ℝ (s^n)
  have e : (fun y => iteratedFDeriv ℝ n (A y) 0) = L ∘ (fun y => Q (x+y)) := funext freq
  have hQ : ContDiff ℝ ∞ Q := (smooth_right_slice_iterated_fderiv a h n).comp
    (contDiff_id.prodMk contDiff_const)
  have hQ' : ContDiff ℝ ∞ (fun y => Q (x+y)) := hQ.comp (contDiff_const.add contDiff_id)
  have j := radian_mixed_jet_norm_le_joint A hA m n 0 0
  rw [e,L.iteratedFDeriv_comp_left hQ'.contDiffAt (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)),
    iteratedFDeriv_comp_add_left,add_zero] at j
  have e0 : L.compContinuousMultilinearMap (iteratedFDeriv ℝ m Q x) = s^n • iteratedFDeriv ℝ m Q x := by
    ext v
    rfl
  rw [e0,norm_smul,Real.norm_of_nonneg (pow_nonneg (radian_frequency_weight_pos ξ).le _)] at j
  exact j.trans_eq (congrArg norm (radian_parameter_jet_affine _ h (n+m) (x,ξ) s))

theorem ScaledJointOrderOne.firstBaseFrequency {a : E → E → ℂ} (h : ScaledJointOrderOne a) :
    FirstBaseFrequencyOrderOne a := by
  refine ⟨⟨fun x => h.smooth.comp (contDiff_const.prodMk contDiff_id), ?_⟩,
    fun n ξ => ((smooth_right_slice_iterated_fderiv a h.smooth n).comp
      (contDiff_id.prodMk contDiff_const)).differentiable (by simp), ?_⟩
  · intro n
    obtain ⟨C,C0,hC⟩ := h.bound (n+0)
    refine ⟨C,C0,fun x ξ => ?_⟩
    have hh := (scaled_mixed_norm_le_joint a h.smooth 0 n x ξ).trans (hC (x,ξ))
    simpa only [norm_iteratedFDeriv_zero, mul_comm, radianFrequencyWeight] using hh
  · intro n
    obtain ⟨C,C0,hC⟩ := h.bound (n+1)
    refine ⟨C,C0,fun x ξ => ?_⟩
    have hh := (scaled_mixed_norm_le_joint a h.smooth 1 n x ξ).trans (hC (x,ξ))
    rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] at hh
    simpa only [mul_comm, radianFrequencyWeight] using hh

theorem ScaledJointOrderOne.pureBase {a : E → E → ℂ} (h : ScaledJointOrderOne a) :
    ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ m (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖) := by
  intro m
  obtain ⟨C,C0,hC⟩ := h.bound (0+m)
  refine ⟨C,C0,fun x ξ => ?_⟩
  let I := (continuousMultilinearCurryFin0 ℝ E ℂ).symm
  let L := I.toLinearIsometry.toContinuousLinearMap
  have hEq : (fun y => iteratedFDeriv ℝ 0 (a y) ξ) = L ∘ (fun y => a y ξ) :=
    funext fun y => congrFun iteratedFDeriv_zero_eq_comp ξ
  have hEqJet := ContinuousLinearEquiv.iteratedFDeriv_comp_left (𝕜 := ℝ)
    (f := fun y => a y ξ) (x := x) (i := m) I.toContinuousLinearEquiv
  change iteratedFDeriv ℝ m (L ∘ (fun y => a y ξ)) x =
    L.compContinuousMultilinearMap (iteratedFDeriv ℝ m (fun y => a y ξ) x) at hEqJet
  have hR := (scaled_mixed_norm_le_joint a h.smooth m 0 x ξ).trans (hC (x,ξ))
  rw [hEq, hEqJet, pow_zero, one_mul] at hR
  rw [LinearIsometry.norm_compContinuousMultilinearMap I.toLinearIsometry] at hR
  exact hR

private theorem baseDirectionSymbol_eq_joint (a : E → E → ℂ) (hs : ContDiff ℝ ∞ (uncurry a))
    (e : E) (p : P) : baseDirectionSymbol a e p.1 p.2 = fderiv ℝ (uncurry a) p (e,0) := by
  let L := ContinuousLinearMap.inl ℝ E E
  have hLine : HasFDerivAt (fun y => (y,p.2)) L p.1 := by
    exact (L.hasFDerivAt.add_const (0,p.2)).congr_of_eventuallyEq
      (.of_forall fun y => by simp [L])
  have hd := ((hs.differentiable (by simp)) p).hasFDerivAt.comp p.1 hLine
  change fderiv ℝ (uncurry a ∘ fun y => (y,p.2)) p.1 e = _
  rw [hd.fderiv]
  rfl

/-- One base derivative uses one more scaled joint derivative and keeps
the same frequency order, since its direction has zero fiber component. -/
theorem ScaledJointOrderOne.baseDirection {a : E → E → ℂ} (h : ScaledJointOrderOne a) (e : E) :
    ScaledJointOrderOne (baseDirectionSymbol a e) := by
  refine ⟨baseDirectionSymbol_joint_smooth h.smooth e, fun n => ?_⟩
  obtain ⟨C,C0,hC⟩ := h.bound (n+1)
  let d : P := (e,0)
  refine ⟨‖d‖*C, mul_nonneg (norm_nonneg _) C0, fun p => ?_⟩
  let S := radianParameterScale (W p.2)
  let G (q : P) := uncurry a (p+S q)
  have hG : ContDiff ℝ ∞ G := h.smooth.comp (contDiff_const.add S.contDiff)
  have hD : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by simp)
  have hParam (q : P) : uncurry (baseDirectionSymbol a e) (p+S q) = fderiv ℝ G q d := by
    have ha := (h.smooth.differentiable (by simp) (p+S q)).hasFDerivAt.comp q
      (S.hasFDerivAt.const_add p)
    change _ = fderiv ℝ (uncurry a ∘ fun y => p+S y) q d
    have hd : S d = (e,0) := by simp [S,d]
    rw [ha.fderiv, ContinuousLinearMap.comp_apply, hd]
    exact baseDirectionSymbol_eq_joint a h.smooth e (p+S q)
  have he : (fun q : P => uncurry (baseDirectionSymbol a e) (p+S q)) =
      fun q => fderiv ℝ G q d := funext hParam
  have hScaled : iteratedFDeriv ℝ n (fun q : P => uncurry (baseDirectionSymbol a e) (p+S q)) 0 =
      radianScaledParameterJet (uncurry (baseDirectionSymbol a e)) n p :=
    radian_parameter_jet_affine _ (baseDirectionSymbol_joint_smooth h.smooth e) n p (W p.2)
  rw [← hScaled, he]
  calc
    _ ≤ ‖d‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ G) 0‖ :=
      norm_iteratedFDeriv_clm_apply_const hD.contDiffAt (by exact_mod_cast le_top)
    _ = ‖d‖ * ‖radianScaledParameterJet (uncurry a) (n+1) p‖ := by
      rw [norm_iteratedFDeriv_fderiv]
      exact congrArg (fun v => ‖d‖ * ‖v‖) (radian_parameter_jet_affine _ h.smooth (n+1) p (W p.2))
    _ ≤ ‖d‖ * (C * W p.2) := mul_le_mul_of_nonneg_left (hC p) (norm_nonneg _)
    _ = _ := by rw [mul_assoc]

end Burnett.V03
