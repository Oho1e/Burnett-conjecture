import Burnett.Analysis.TransportWard.Weyl.Amplitude.WeightedParameterJets

set_option autoImplicit false
set_option maxHeartbeats 6200000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal Topology

theorem iteratedFDeriv_affine_actual {X Y V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : Y → V)
    (h : ContDiff ℝ ∞ f) (L : X →L[ℝ] Y) (a : Y) (x : X) (n : ℕ) :
    iteratedFDeriv ℝ n (fun y => f (a+L y)) x =
      (iteratedFDeriv ℝ n f (a+L x)).compContinuousLinearMap (fun _ => L) := by
  let g (y : Y) := f (a+y)
  have c : ContDiff ℝ ∞ g := h.comp (contDiff_const.add contDiff_id)
  change iteratedFDeriv ℝ n (g ∘ L) x = _
  rw [L.iteratedFDeriv_comp_right c x (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]
  simp only [g,iteratedFDeriv_comp_add_left]

/-- Pointwise repeated currying preserves the norm of a joint iterated
Fréchet derivative. -/
theorem norm_iteratedFDeriv_of_iteratedFDeriv {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : X → V)
    (x : X) (m n : ℕ) :
    ‖iteratedFDeriv ℝ m (iteratedFDeriv ℝ n f) x‖ =
      ‖iteratedFDeriv ℝ (n+m) f x‖ := by
  induction m generalizing n with
  | zero => simp only [norm_iteratedFDeriv_zero,Nat.add_zero]
  | succ m ih =>
    let Vbig := ContinuousMultilinearMap ℝ (fun _ : Fin (n+1) => X) V
    let Vsmall := ContinuousMultilinearMap ℝ (fun _ : Fin n => X) V
    let C : Vbig ≃ₗᵢ[ℝ] (X →L[ℝ] Vsmall) :=
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => X) V
    let J : X → Vbig := iteratedFDeriv ℝ (n+1) f
    let L : Vbig →L[ℝ] (X →L[ℝ] Vsmall) := C.toLinearIsometry.toContinuousLinearMap
    have chain := ContinuousLinearEquiv.iteratedFDeriv_comp_left
      (𝕜 := ℝ) (E := X) (F := Vbig) (G := X →L[ℝ] Vsmall) (f := J) (x := x) (i := m)
      C.toContinuousLinearEquiv
    change iteratedFDeriv ℝ m (L ∘ J) x = L.compContinuousMultilinearMap (iteratedFDeriv ℝ m J x) at chain
    have curry : ‖iteratedFDeriv ℝ m (C ∘ J) x‖ = ‖iteratedFDeriv ℝ m J x‖ := by
      change ‖iteratedFDeriv ℝ m (L ∘ J) x‖ = _
      rw [chain]
      have nn := LinearIsometry.norm_compContinuousMultilinearMap
        (𝕜 := ℝ) (ι := Fin m) (E := fun _ : Fin m => X) (G := Vbig) (G' := X →L[ℝ] Vsmall)
        C.toLinearIsometry (iteratedFDeriv ℝ m J x)
      exact nn
    calc
      _ = ‖iteratedFDeriv ℝ m (fderiv ℝ (iteratedFDeriv ℝ n f)) x‖ :=
        norm_iteratedFDeriv_fderiv.symm
      _ = ‖iteratedFDeriv ℝ m (C ∘ iteratedFDeriv ℝ (n+1) f) x‖ := by rw [fderiv_iteratedFDeriv]
      _ = ‖iteratedFDeriv ℝ m (iteratedFDeriv ℝ (n+1) f) x‖ := curry
      _ = ‖iteratedFDeriv ℝ ((n+1)+m) f x‖ := ih (n+1)
      _ = _ := by rw [show (n+1)+m = n+(m+1) by omega]

private theorem norm_iteratedFDeriv_affine_contraction {X Y V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : Y → V) (h : ContDiff ℝ ∞ f)
    (L : X →L[ℝ] Y) (hL : ‖L‖ ≤ 1) (a : Y) (x : X) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f (a+L y)) x‖ ≤ ‖iteratedFDeriv ℝ n f (a+L x)‖ := by
  rw [iteratedFDeriv_affine_actual f h L a x n]
  have t := (iteratedFDeriv ℝ n f (a+L x)).norm_compContinuousLinearMap_le (fun _ : Fin n => L)
  rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at t
  exact t.trans (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL))

/-- The mixed jet used by the paper is a contraction of the joint jet
of the same symbol. -/
theorem radian_mixed_jet_norm_le_joint (a : E → E → ℂ)
    (h : ContDiff ℝ ∞ (Function.uncurry a)) (m n : ℕ) (x ξ : E) :
    ‖iteratedFDeriv ℝ m (fun y => iteratedFDeriv ℝ n (a y) ξ) x‖ ≤
      ‖iteratedFDeriv ℝ (n+m) (Function.uncurry a) (x,ξ)‖ := by
  let L := ContinuousLinearMap.inr ℝ E E
  let I := ContinuousLinearMap.inl ℝ E E
  let T := ContinuousMultilinearMap.compContinuousLinearMapL (G := ℂ) (fun _ : Fin n => L)
  let J := iteratedFDeriv ℝ n (Function.uncurry a)
  let A (y : E) := J ((0,ξ)+I y)
  have hJ : ContDiff ℝ ∞ J :=
    h.iteratedFDeriv_right (by exact_mod_cast (show (⊤ : ℕ∞) + (n : ℕ∞) ≤ ⊤ by simp))
  have hA : ContDiff ℝ ∞ A := hJ.comp (contDiff_const.add I.contDiff)
  have hc (v : E) : (v,0)+(L ξ) = (v,ξ) := by simp [L]
  have hi (v : E) : (0,ξ)+(I v) = (v,ξ) := by simp [I]
  have eq : (fun y => iteratedFDeriv ℝ n (a y) ξ) = T ∘ A := by
    funext y
    have et : (a y) = fun z => Function.uncurry a ((y,0)+L z) := by
      funext z
      simp [L]
    rw [et,iteratedFDeriv_affine_actual _ h L (y,0) ξ n,hc y]
    change _ = (iteratedFDeriv ℝ n (Function.uncurry a) ((0,ξ)+I y)).compContinuousLinearMap (fun _ => L)
    rw [hi y]
  have il : ‖I‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro y; simp [I])
  have ll : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro y; simp [L])
  have ht : ‖T‖ ≤ 1 := by
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le ℂ (fun _ : Fin n => L)).trans
    rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) ll
  rw [eq,T.iteratedFDeriv_comp_left hA.contDiffAt (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))]
  calc
    _ ≤ ‖T‖ * ‖iteratedFDeriv ℝ m A x‖ := T.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖iteratedFDeriv ℝ m A x‖ := mul_le_of_le_one_left (norm_nonneg _) ht
    _ ≤ ‖iteratedFDeriv ℝ m J ((0,ξ)+I x)‖ := norm_iteratedFDeriv_affine_contraction J hJ I il (0,ξ) x m
    _ = _ := by rw [hi x,norm_iteratedFDeriv_of_iteratedFDeriv]

/-- A uniform bound on the actual scaled joint jets implies the
ordinary order-zero mixed symbol seminorms consumed by the verified
left action. -/
theorem radian_order_zero_of_scaled_joint_jets (a : E → E → ℂ)
    (h : ContDiff ℝ ∞ (Function.uncurry a))
    (b : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p,
      ‖radianScaledParameterJet (Function.uncurry a) k p‖ ≤ C) :
    RadianOrderZeroSymbolSeminorms a := by
  refine ⟨compact_base_frequency_jets_of_joint_smooth a h,fun n m => ?_⟩
  obtain ⟨C,C0,hC⟩ := b (n+m)
  refine ⟨C,C0,fun x ξ => ?_⟩
  let s := radianFrequencyWeight ξ
  let A (y ζ : E) := a (x+y) (ξ+s • ζ)
  have hA : ContDiff ℝ ∞ (Function.uncurry A) := by
    change ContDiff ℝ ∞ (Function.uncurry a ∘ (fun p : RadianParameter => (x,ξ)+radianParameterScale s p))
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
  have eq : iteratedFDeriv ℝ (n+m) (Function.uncurry A) (0,0) =
      radianScaledParameterJet (Function.uncurry a) (n+m) (x,ξ) :=
    radian_parameter_jet_affine _ h (n+m) (x,ξ) s
  have bU : ‖iteratedFDeriv ℝ (n+m) (Function.uncurry A) (0,0)‖ ≤ C := by
    rw [eq]
    exact hC (x,ξ)
  exact j.trans bU

end Burnett.A03
