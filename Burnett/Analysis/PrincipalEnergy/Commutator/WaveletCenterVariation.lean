import Burnett.Analysis.PrincipalEnergy.Commutator.CenteredWaveletPackets
import Burnett.Analysis.PrincipalEnergy.Commutator.BumpScale
import Burnett.Analysis.PrincipalEnergy.Energy.CoordinateH1Energy

set_option autoImplicit false
set_option maxHeartbeats 4200000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier
open Burnett.Analysis.SymmetricEnergy (coordinateH1 coordinateDirection schwartz_ball_norm_le unitBallVolume)
open scoped Topology BigOperators NNReal ComplexConjugate

private theorem toLp_norm_of_translate (k v : SchwartzMap Space ℂ) (c : Space)
    (he : ∀ z, v z=k (z-c)) :
    ‖v.toLp 2 volume‖=‖k.toLp 2 volume‖ := by
  have hSq (f : SchwartzMap Space ℂ) : ‖f.toLp 2 volume‖^2=∫ z, ‖f z‖^2 := by
    rw [l2_norm_sq_integral]
    exact integral_congr_ae ((f.coeFn_toLp 2 volume).fun_comp fun z => ‖z‖^2)
  have hMove : MeasurePreserving (fun z : Space => z-c) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure Space) (-c)
  have hEq : ‖v.toLp 2 volume‖^2=‖k.toLp 2 volume‖^2 := by
    rw [hSq,hSq]
    simp_rw [he]
    rw [← integral_map (f := fun z : Space => ‖k z‖^2) hMove.measurable.aemeasurable
      (by rw [hMove.map_eq]; exact (k.continuous.norm.pow 2).aestronglyMeasurable),hMove.map_eq]
  exact le_antisymm ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hEq.le)
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hEq.ge)

private theorem continuous_toLp_compactTranslate (k : SchwartzMap Space ℂ)
    (v : Space → SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    (hSupp : tsupport (k : Space → ℂ) ⊆ Metric.closedBall 0 s)
    (he : ∀ c z, v c z=k (z-c)) :
    Continuous (fun c => (v c).toLp 2 volume) := by
  apply continuous_iff_continuousAt.2
  intro c
  apply tendsto_iff_norm_sub_tendsto_zero.2
  let D := SchwartzMap.seminorm ℝ 0 1 k
  have hD : 0≤D := apply_nonneg _ _
  let J : NNReal := ⟨D,hD⟩
  have hLip : LipschitzWith J (k : Space → ℂ) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ) k.differentiable
    intro z
    change ‖fderiv ℝ (k : Space → ℂ) z‖≤D
    have hEq : ‖fderiv ℝ (k : Space → ℂ) z‖=‖iteratedFDeriv ℝ 1 (k : Space → ℂ) z‖ := by
      simpa only [norm_iteratedFDeriv_zero] using
        (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := (k : Space → ℂ)) (x := z) (n := 0))
    rw [hEq]
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ k 1 z
  have hZero (z : Space) (hz : s<‖z‖) : k z=0 := by
    by_contra hk
    have hz' : z ∈ Metric.closedBall (0:Space) s := hSupp (subset_closure hk)
    exact (not_le_of_gt hz) (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz')
  let A := D*((s+1)^2*Real.sqrt unitBallVolume)
  have hBound : ∀ᶠ x : Space in 𝓝 c,
      ‖(v x).toLp 2 volume-(v c).toLp 2 volume‖≤A*‖x-c‖ := by
    filter_upwards [Metric.ball_mem_nhds c (zero_lt_one : (0:ℝ)<1)] with x hx
    have hd : ‖x-c‖<1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    have hS : tsupport (⇑(v x-v c)) ⊆ Metric.closedBall c (s+1) := by
      apply closure_minimal _ Metric.isClosed_closedBall
      intro z hz
      by_contra hNot
      have hOut : s+1<‖z-c‖ := not_le.mp (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hNot)
      have hTri := norm_add_le (z-x) (x-c)
      rw [show z-x+(x-c)=z-c by abel] at hTri
      have hFar : s<‖z-x‖ := by linarith
      exact hz (by rw [SchwartzMap.sub_apply,he,he,hZero _ hFar,hZero _ (by linarith : s<‖z-c‖),sub_self])
    have hV (z : Space) : ‖(v x-v c) z‖≤D*‖x-c‖ := by
      have h := hLip.dist_le_mul (z-x) (z-c)
      rw [dist_eq_norm,dist_eq_norm,show (z-x)-(z-c)=c-x by abel,norm_sub_rev c x] at h
      simpa only [SchwartzMap.sub_apply,he,J,NNReal.coe_mk] using h
    have hLp :=
      schwartz_ball_norm_le (v x-v c) c (s+1) (D*‖x-c‖) (by linarith) (by positivity) hS hV
    let B := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space)
    change ‖B (v x-v c)‖≤_ at hLp
    rw [map_sub] at hLp
    exact hLp.trans_eq (by dsimp only [A]; ring)
  have hLim : Tendsto (fun x : Space => A*‖x-c‖) (𝓝 c) (𝓝 0) := by
    have h : Continuous (fun x : Space => A*‖x-c‖) :=
      continuous_const.mul (continuous_id.sub continuous_const).norm
    have hT : Tendsto (fun x : Space => A*‖x-c‖) (𝓝 c) (𝓝 (A*‖c-c‖)) := h.continuousAt
    rwa [sub_self,norm_zero,mul_zero] at hT
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLim
    (Eventually.of_forall fun _ => norm_nonneg _) hBound

private theorem pderiv_compactTranslate (k v : SchwartzMap Space ℂ) (c e : Space)
    (he : ∀ z, v z=k (z-c)) (z : Space) :
    SchwartzMap.pderivCLM ℂ e v z=SchwartzMap.pderivCLM ℂ e k (z-c) := by
  change fderiv ℝ (v : Space → ℂ) z e=fderiv ℝ (k : Space → ℂ) (z-c) e
  rw [show (v : Space → ℂ)=fun z => k (z-c) from funext he]
  have h₀ : HasFDerivAt (fun x : Space => x-c) (ContinuousLinearMap.id ℝ Space) z :=
    (hasFDerivAt_id z).sub_const c
  have h₁ := k.differentiableAt.hasFDerivAt.comp z h₀
  change HasFDerivAt (fun x : Space => k (x-c))
    ((fderiv ℝ (k : Space → ℂ) (z-c)).comp (ContinuousLinearMap.id ℝ Space)) z at h₁
  rw [ContinuousLinearMap.comp_id] at h₁
  exact congrArg (fun L : Space →L[ℝ] ℂ => L e) h₁.fderiv

/-- In the physical first-order norm, a translated wavelet is continuous in
its center. Its first-order norm is independent of the center. -/
theorem centeredWavelet_coordinateH1_center
    (θ : SchwartzMap Space ℂ) (hθ : ∀ z, 1<‖z‖ → θ z=0) (s : ℝ) (hs : 0<s)
    (c : Space) :
    let w (x : Space) := centeredWavelet θ hθ s hs x
    Tendsto (fun x => coordinateH1 (w x-w c)) (𝓝 c) (𝓝 0) ∧
      coordinateH1 (w c)=coordinateH1 (w 0) := by
  intro w
  let k := w 0
  have he (x z : Space) : w x z=k (z-x) := by
    simp only [w,k,centeredWavelet_apply,sub_zero]
  let L := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space)
  let D (i : Fin 4) : SchwartzMap Space ℂ →L[ℂ] SchwartzMap Space ℂ :=
    SchwartzMap.pderivCLM ℂ (coordinateDirection i)
  have hSupport : tsupport (k : Space → ℂ) ⊆ Metric.closedBall 0 s := centeredWavelet_support θ hθ s hs 0
  have hSupportDer (i : Fin 4) : tsupport (D i k : Space → ℂ) ⊆ Metric.closedBall 0 s := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    have hn : fderiv ℝ (k : Space → ℂ) z≠0 := by
      intro h
      exact hz (show fderiv ℝ (k : Space → ℂ) z (coordinateDirection i)=0 by simp only [h,ContinuousLinearMap.zero_apply])
    exact hSupport (support_fderiv_subset ℝ hn)
  have heD (i : Fin 4) (x z : Space) : D i (w x) z=D i k (z-x) :=
    pderiv_compactTranslate k (w x) x (coordinateDirection i) (he x) z
  have hC := continuous_toLp_compactTranslate k w s hs hSupport he
  have hCD (i : Fin 4) := continuous_toLp_compactTranslate (D i k) (fun x => D i (w x)) s hs
    (hSupportDer i) (heD i)
  have hVal : Tendsto (fun x => ‖L (w x-w c)‖) (𝓝 c) (𝓝 0) := by
    simpa only [map_sub] using tendsto_iff_norm_sub_tendsto_zero.1 (hC.continuousAt (x := c))
  have hDer (i : Fin 4) : Tendsto (fun x => ‖L (D i (w x-w c))‖) (𝓝 c) (𝓝 0) := by
    simpa only [map_sub] using tendsto_iff_norm_sub_tendsto_zero.1 ((hCD i).continuousAt (x := c))
  have hSum : Tendsto (fun x => ∑ i : Fin 4, ‖L (D i (w x-w c))‖^2) (𝓝 c) (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin 4)) (fun i _ => (hDer i).pow 2)
    simpa only [zero_pow (by decide : (2:ℕ) ≠ 0),Finset.sum_const_zero] using h
  refine ⟨?_,?_⟩
  · have h := (((hVal).pow 2).add hSum).sqrt
    simpa only [coordinateH1,L,D,SchwartzMap.toLpCLM_apply,zero_pow (by decide : (2:ℕ) ≠ 0),
      add_zero,Real.sqrt_zero] using h
  · have hN := toLp_norm_of_translate k (w c) c (he c)
    have hND (i : Fin 4) := toLp_norm_of_translate (D i k) (D i (w c)) c (heD i c)
    have hDsum : (∑ i : Fin 4, ‖(D i (w c)).toLp 2 volume‖^2)=
        ∑ i : Fin 4, ‖(D i k).toLp 2 volume‖^2 :=
      Finset.sum_congr rfl fun i _ => congrArg (fun r : ℝ => r^2) (hND i)
    unfold coordinateH1
    rw [hN,hDsum]

/-- The center kernel is jointly continuous by a first-order bound on
the physical test pairing. This does not require its final zero-order bound. -/
theorem continuous_centeredWaveletPair_of_H1_bound
    (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
    (hLin : ∀ f u g : SchwartzMap Space ℂ, ∀ c : ℂ, R (f-c • u) g=R f g-c*R u g)
    (hSkew : ∀ f g, R g f= -conj (R f g))
    (D : ℝ) (hR : ∀ f g, ‖R f g‖≤D*coordinateH1 f*coordinateH1 g)
    (θ η : SchwartzMap Space ℂ)
    (hθ : ∀ z, 1<‖z‖ → θ z=0) (hη : ∀ z, 1<‖z‖ → η z=0)
    (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    Continuous (fun p : Space × Space =>
      R (centeredWavelet θ hθ t ht p.2) (centeredWavelet η hη s hs p.1)) := by
  let u := centeredWavelet θ hθ t ht
  let v := centeredWavelet η hη s hs
  let F (p : Space × Space) := R (u p.2) (v p.1)
  change Continuous F
  have hL (f f₀ g : SchwartzMap Space ℂ) : R f g-R f₀ g=R (f-f₀) g := by
    simpa only [one_smul,one_mul] using (hLin f f₀ g 1).symm
  have hG (f g g₀ : SchwartzMap Space ℂ) : R f g-R f g₀=R f (g-g₀) := by
    calc
      _ = -conj (R g f-R g₀ f) := by rw [hSkew g f,hSkew g₀ f,map_sub]; ring
      _ = _ := by rw [hL,hSkew (g-g₀) f]
  apply continuous_iff_continuousAt.mpr
  intro c
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hV (z : Space) : coordinateH1 (v z)=coordinateH1 (v 0) :=
    (centeredWavelet_coordinateH1_center η hη s hs z).2
  let B (p : Space × Space) :=
    (D*coordinateH1 (u p.2-u c.2))*coordinateH1 (v 0)+
      (D*coordinateH1 (u c.2))*coordinateH1 (v p.1-v c.1)
  have hDom (p : Space × Space) : ‖F p-F c‖≤B p := by
    have hE : F p-F c=R (u p.2-u c.2) (v p.1)+R (u c.2) (v p.1-v c.1) := by
      dsimp only [F]
      rw [← hL,← hG]
      ring
    rw [hE]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hR _ _))
    rw [← hV p.1]
    exact hR _ _
  have hUlim := (centeredWavelet_coordinateH1_center θ hθ t ht c.2).1.comp
    (continuous_snd.continuousAt (x := c))
  have hVlim := (centeredWavelet_coordinateH1_center η hη s hs c.1).1.comp
    (continuous_fst.continuousAt (x := c))
  have hB : Tendsto B (𝓝 c) (𝓝 0) := by
    have h := ((hUlim.const_mul D).mul_const (coordinateH1 (v 0))).add
      (hVlim.const_mul (D*coordinateH1 (u c.2)))
    simpa only [B,zero_mul,mul_zero,add_zero] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
    (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall hDom)

end Burnett.Analysis.CarlesonEmbedding
