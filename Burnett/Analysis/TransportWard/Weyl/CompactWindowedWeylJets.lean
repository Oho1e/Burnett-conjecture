import Burnett.Analysis.TransportWard.Weyl.CompactHomogeneousFrequencyJets
import Burnett.Analysis.TransportWard.Weyl.Amplitude.ScaledMixedJetConversion
import Burnett.Analysis.TransportWard.Weyl.ScaledSymbolA01

set_option autoImplicit false
set_option maxHeartbeats 8500000
set_option maxRecDepth 4000

noncomputable section

namespace Burnett.V03

open Function Filter Set Burnett.Analysis Burnett.A03 Burnett.A02.FrequencySplit
open scoped BigOperators ContDiff Topology

private theorem nat_order_le_smooth (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)

private theorem norm_comp_uniform_contraction {U V W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ}
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin n => V) W) (L : U →L[ℝ] V)
    (hL : ‖L‖ ≤ 1) : ‖D.compContinuousLinearMap (fun _ => L)‖ ≤ ‖D‖ := by
  apply (D.norm_compContinuousLinearMap_le _).trans
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)

private theorem norm_mixed_joint {X Y V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : X × Y → V) (hf : ContDiff ℝ ∞ f) (m n : ℕ) (x : X) (y : Y) :
    ‖iteratedFDeriv ℝ m (fun a => iteratedFDeriv ℝ n (fun b => f (a, b)) y) x‖ ≤
      ‖iteratedFDeriv ℝ (n + m) f (x, y)‖ := by
  let L := ContinuousLinearMap.inr ℝ X Y
  let I := ContinuousLinearMap.inl ℝ X Y
  let T := ContinuousMultilinearMap.compContinuousLinearMapL (G := V) (fun _ : Fin n => L)
  let J := iteratedFDeriv ℝ n f
  let A (a : X) := J ((0, y) + I a)
  have hJ : ContDiff ℝ ∞ J :=
    hf.iteratedFDeriv_right (by exact_mod_cast (show (⊤ : ℕ∞) + (n : ℕ∞) ≤ ⊤ by simp))
  have hA : ContDiff ℝ ∞ A := hJ.comp (contDiff_const.add I.contDiff)
  have hL (a : X) : (a, 0) + L y = (a, y) := by simp [L]
  have hI (a : X) : (0, y) + I a = (a, y) := by simp [I]
  have hEq : (fun a => iteratedFDeriv ℝ n (fun b => f (a, b)) y) = T ∘ A := by
    funext a
    have he : (fun b => f (a, b)) = fun b => f ((a, 0) + L b) := by
      funext b
      simp [L]
    rw [he, iteratedFDeriv_affine_actual f hf L (a, 0) y n, hL a]
    change _ = (iteratedFDeriv ℝ n f ((0, y) + I a)).compContinuousLinearMap (fun _ => L)
    rw [hI a]
  have hIL : ‖I‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro a; simp [I])
  have hLL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro a; simp [L])
  have hTL : ‖T‖ ≤ 1 := by
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le V (fun _ : Fin n => L)).trans
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) hLL
  rw [hEq, T.iteratedFDeriv_comp_left hA.contDiffAt (nat_order_le_smooth m)]
  calc
    _ ≤ ‖T‖ * ‖iteratedFDeriv ℝ m A x‖ := T.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖iteratedFDeriv ℝ m A x‖ := mul_le_of_le_one_left (norm_nonneg _) hTL
    _ ≤ ‖iteratedFDeriv ℝ m J ((0, y) + I x)‖ := by
      rw [show A = fun a => J ((0, y) + I a) from rfl,
        iteratedFDeriv_affine_actual J hJ I (0, y) x m]
      exact norm_comp_uniform_contraction _ I hIL
    _ = _ := by rw [hI x, norm_iteratedFDeriv_of_iteratedFDeriv]

private theorem norm_input_scaledJet_le_joint (a : E → E → E → ℂ)
    (F : (E × E) × E → ℂ) (hF : ContDiff ℝ ∞ F)
    (ha : ∀ x y ξ, F ((x, y), ξ) = a x y ξ)
    (p : RadianParameter) (y : E) (m j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun z => radianScaledParameterJet (radianTwoPointParameter a z) m p) y‖ ≤
      ‖(iteratedFDeriv ℝ (m + j) F ((p.1, y), p.2)).compContinuousLinearMap
        (fun _ => frequencyDirectionScale (radianFrequencyWeight p.2))‖ := by
  let V := (E × E) × E
  let A := ContinuousLinearMap.fst ℝ E RadianParameter
  let B := ContinuousLinearMap.snd ℝ E RadianParameter
  let J : E × RadianParameter →L[ℝ] V :=
    (((ContinuousLinearMap.fst ℝ E E).comp B).prod A).prod ((ContinuousLinearMap.snd ℝ E E).comp B)
  let p₀ : V := ((p.1, y), p.2)
  let D : V →L[ℝ] V := frequencyDirectionScale (radianFrequencyWeight p.2)
  let G (q : E × RadianParameter) := F (p₀ + (D.comp J) q)
  have hJ : ‖J‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro v
    rw [one_mul, show J v = ((v.2.1, v.1), v.2.2) from rfl,
      norm_prod_le_iff, norm_prod_le_iff]
    exact ⟨⟨(norm_fst_le v.2).trans (norm_snd_le v), norm_fst_le v⟩,
      (norm_snd_le v.2).trans (norm_snd_le v)⟩
  have hG : ContDiff ℝ ∞ G := hF.comp (contDiff_const.add (D.comp J).contDiff)
  have hFibre (z : E) : ContDiff ℝ ∞ (radianTwoPointParameter a z) := by
    have hLift : ContDiff ℝ ∞ (fun q : RadianParameter => ((q.1, z), q.2)) :=
      (contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd
    have hEq : radianTwoPointParameter a z = F ∘ (fun q => ((q.1, z), q.2)) :=
      funext fun q => (ha q.1 z q.2).symm
    rw [hEq]
    exact hF.comp hLift
  let H (z : E) := radianScaledParameterJet (radianTwoPointParameter a z) m p
  have hShift : (fun z => iteratedFDeriv ℝ m (fun q => G (z, q)) 0) =
      fun z => H (y + z) := by
    funext z
    have hArg : (fun q => G (z, q)) =
        fun q => radianTwoPointParameter a (y + z) (p + radianParameterScale (radianFrequencyWeight p.2) q) := by
      funext q
      exact ha (p.1 + q.1) (y + z) (p.2 + radianFrequencyWeight p.2 • q.2)
    rw [hArg, radian_parameter_jet_affine _ (hFibre _) m p]
    rfl
  have h := norm_mixed_joint G hG j m (0 : E) (0 : RadianParameter)
  rw [hShift, iteratedFDeriv_comp_add_left, add_zero] at h
  apply h.trans
  change ‖iteratedFDeriv ℝ (m + j) G (0 : E × RadianParameter)‖ ≤ _
  rw [show G = (fun q => F (p₀ + (D.comp J) q)) from rfl,
    iteratedFDeriv_affine_actual F hF (D.comp J) p₀ 0 (m + j), map_zero, add_zero]
  have hCompose : (iteratedFDeriv ℝ (m + j) F p₀).compContinuousLinearMap (fun _ => D.comp J) =
      ((iteratedFDeriv ℝ (m + j) F p₀).compContinuousLinearMap (fun _ => D)).compContinuousLinearMap
        (fun _ => J) := by
    apply ContinuousMultilinearMap.ext
    intro _
    rfl
  rw [hCompose]
  exact norm_comp_uniform_contraction _ J hJ

/-- The genuine compact Weyl amplitude inherits the normalized estimates
of every order from joint smoothness and the actual degree-one tail. -/
theorem compactWindowedWeylAmplitude_scaled_orderOne (θ : E → ℝ) (β : E → E → ℂ)
    (hθ : ContDiff ℝ ∞ θ) (hβ : ContDiff ℝ ∞ (uncurry β)) (R : ℝ)
    (hSupport : ∀ x ∉ Metric.closedBall (0 : E) R, θ x = 0)
    (hHom : ∀ x ξ, 1 < ‖ξ‖ → ∀ t : ℝ, 1 ≤ t → β x (t • ξ) = t • β x ξ) :
    CompactRadianScaledOrderOne (windowedWeylAmplitude θ β) R R := by
  let a := windowedWeylAmplitude θ β
  let F (q : (E × E) × E) := a q.1.1 q.1.2 q.2
  let X := Metric.closedBall (0 : E) R
  let A (q : (E × E) × E) := ((1 / 2 : ℝ) • (q.1.1 + q.1.2), q.2)
  have hA : ContDiff ℝ ∞ A := (contDiff_const.smul
    ((contDiff_fst.comp contDiff_fst).add (contDiff_snd.comp contDiff_fst))).prodMk contDiff_snd
  have hθ₁ : ContDiff ℝ ∞ (fun q : (E × E) × E => (θ q.1.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hθ.comp (contDiff_fst.comp contDiff_fst))
  have hθ₂ : ContDiff ℝ ∞ (fun q : (E × E) × E => (θ q.1.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hθ.comp (contDiff_snd.comp contDiff_fst))
  have hF : ContDiff ℝ ∞ F := (hθ₁.mul hθ₂).mul (hβ.comp hA)
  have hSupp (q : E × E) (hq : q ∉ X ×ˢ X) (ξ : E) : F (q, ξ) = 0 := by
    by_cases hx : q.1 ∈ X
    · have hy : q.2 ∉ X := fun h => hq ⟨hx, h⟩
      simp [F, a, windowedWeylAmplitude, hSupport _ hy]
    · simp [F, a, windowedWeylAmplitude, hSupport _ hx]
  have hTail (q : E × E) (ξ : E) (hξ : 1 < ‖ξ‖) (t : ℝ) (ht : 1 ≤ t) :
      F (q, t • ξ) = t • F (q, ξ) := by
    simp only [F, a, windowedWeylAmplitude, hHom _ _ hξ t ht, mul_smul_comm]
  have hCompact : IsCompact X := isCompact_closedBall (0 : E) R
  have hAll (k : ℕ) := exists_scaled_joint_orderOne_of_compactBase_of_homogeneousTail
    F hF (hCompact.prod hCompact) hSupp hTail k
  have hScaled (m j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : RadianParameter, ∀ y : E,
      ‖iteratedFDeriv ℝ j (fun z => radianScaledParameterJet (radianTwoPointParameter a z) m p) y‖
        ≤ C * radianFrequencyWeight p.2 := by
    obtain ⟨C, hC, hb⟩ := hAll (m+j)
    exact ⟨C, hC, fun p y => (norm_input_scaledJet_le_joint a F hF (fun _ _ _ => rfl) p y m j).trans
      (hb ((p.1, y), p.2))⟩
  have hJoint : ContDiff ℝ ∞ (fun p : E × E × E => a p.1 p.2.1 p.2.2) :=
    hF.comp ((contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).prodMk (contDiff_snd.comp contDiff_snd))
  refine ⟨⟨hJoint, fun x y ξ hx => by simp [windowedWeylAmplitude, hSupport x hx],
    fun x y ξ hy => by simp [windowedWeylAmplitude, hSupport y hy], ?_⟩, hScaled⟩
  intro j
  obtain ⟨C, hC, hb⟩ := hScaled 0 j
  refine ⟨C, hC, fun x y ξ => ?_⟩
  let p : RadianParameter := (x, ξ)
  let J (z : E) := radianScaledParameterJet (radianTwoPointParameter a z) 0 p
  let v (i : Fin 0) : RadianParameter := Fin.elim0 i
  let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => RadianParameter) ℂ v
  have hEval : ‖ev‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro B
    calc
      ‖ev B‖ ≤ ‖B‖ * ∏ i, ‖v i‖ := B.le_opNorm v
      _ = 1 * ‖B‖ := by simp
  have hParameter : ContDiff ℝ ∞ (uncurry (radianTwoPointParameter a)) := by
    let args (q : E × RadianParameter) := ((q.2.1, q.1), q.2.2)
    have hArgs : ContDiff ℝ ∞ args :=
      ((contDiff_fst.comp contDiff_snd).prodMk contDiff_fst).prodMk (contDiff_snd.comp contDiff_snd)
    exact hF.comp hArgs
  let T := ContinuousMultilinearMap.compContinuousLinearMapL (G := ℂ)
    (fun _ : Fin 0 => radianParameterScale (radianFrequencyWeight p.2))
  have hJ : ContDiff ℝ ∞ J :=
    T.contDiff.comp ((smooth_right_slice_iterated_fderiv _ hParameter 0).comp
      (contDiff_id.prodMk contDiff_const))
  have hE : (fun z => a x z ξ) = ev ∘ J := by
    funext z
    change a x z ξ = iteratedFDeriv ℝ 0 (radianTwoPointParameter a z) p
      (fun i => radianParameterScale (radianFrequencyWeight p.2) (v i))
    rw [iteratedFDeriv_zero_apply]
    rfl
  rw [hE, ev.iteratedFDeriv_comp_left hJ.contDiffAt (nat_order_le_smooth j)]
  exact ((ev.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_of_le_one_left (norm_nonneg _) hEval)).trans (hb p y)

/-- The same regularized symbol, in the frequency convention of the
verified left action, satisfies the normalized A01 order-one bounds. -/
theorem scaledJointOrderOne_of_compactRadianSymbol (β : E → E → ℂ)
    (hβ : ContDiff ℝ ∞ (uncurry β)) {K : Set E} (hK : IsCompact K)
    (hSupp : ∀ x ∉ K, ∀ ξ, β x ξ = 0)
    (hHom : ∀ x ξ, 1 < ‖ξ‖ → ∀ t : ℝ, 1 ≤ t → β x (t • ξ) = t • β x ξ) :
    ScaledJointOrderOne (normalizedWeylSymbol β) := by
  let f := uncurry (normalizedWeylSymbol β)
  have hSmooth : ContDiff ℝ ∞ f :=
    hβ.comp (contDiff_fst.prodMk (contDiff_const.smul contDiff_snd))
  have hTau : 1 ≤ tau := by
    change 1 ≤ 2 * Real.pi
    linarith [Real.two_le_pi]
  have hTail (x ξ : E) (hξ : 1 < ‖ξ‖) (t : ℝ) (ht : 1 ≤ t) :
      f (x, t • ξ) = t • f (x, ξ) := by
    have hLarge : 1 < ‖tau • ξ‖ := by
      rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans hTau)]
      exact hξ.trans_le (le_mul_of_one_le_left (norm_nonneg _) hTau)
    change β x (tau • (t • ξ)) = t • β x (tau • ξ)
    rw [smul_comm tau t ξ]
    exact hHom _ _ hLarge t ht
  refine ⟨hSmooth, fun k => ?_⟩
  obtain ⟨C, hC, hb⟩ := exists_scaled_joint_orderOne_of_compactBase_of_homogeneousTail
    f hSmooth hK (fun x hx ξ => hSupp x hx (tau • ξ)) hTail k
  refine ⟨C, hC, fun p => ?_⟩
  have hScale : frequencyDirectionScale (radianFrequencyWeight p.2) =
      radianParameterScale (radianFrequencyWeight p.2) := by
    apply ContinuousLinearMap.ext
    intro _
    rfl
  simpa only [radianScaledParameterJet, ← hScale] using hb p

end Burnett.V03
