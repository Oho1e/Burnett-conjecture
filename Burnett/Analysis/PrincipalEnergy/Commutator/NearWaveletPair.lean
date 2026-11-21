import Burnett.Analysis.PrincipalEnergy.Commutator.SeparatedWaveletTail
import Burnett.Analysis.PrincipalEnergy.Commutator.LocalWaveletPair
import Burnett.Analysis.PrincipalEnergy.Paraproduct.ExpandingAverageWindows
import Burnett.Analysis.PrincipalEnergy.Commutator.StandardOscillationCutoff

set_option autoImplicit false
set_option maxHeartbeats 4800000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped ComplexConjugate NNReal Topology

private theorem expandingTestSchwartz_hasCompactSupport (χ : SchwartzMap Space ℂ)
    (hχ : HasCompactSupport (χ : Space → ℂ)) (n : ℕ) :
    HasCompactSupport (expandingTestSchwartz χ hχ n : Space → ℂ) := by
  let q : ℝ := (n:ℝ)+1
  have hq : 0<q := by dsimp only [q]; positivity
  let e : Space ≃ₜ Space := Homeomorph.smulOfNeZero q⁻¹ (inv_ne_zero hq.ne')
  exact hχ.comp_homeomorph e

private theorem eventually_expandingTestSchwartz_one_on_ball (χ : SchwartzMap Space ℂ)
    (hχ : HasCompactSupport (χ : Space → ℂ)) (hχ₁ : ∀ z : Space, ‖z‖≤1 → χ z=1)
    (x : Space) (r : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ z : Space, ‖x-z‖≤r → expandingTestSchwartz χ hχ n z=1 := by
  obtain ⟨N,hN⟩ := exists_nat_ge (‖x‖+r)
  refine eventually_atTop.2 ⟨N,fun n hn z hz => ?_⟩
  have hNz : (N:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  have hZ : ‖z‖≤(n:ℝ)+1 := by
    have hTri := norm_add_le x (z-x)
    rw [show x+(z-x)=z by abel,norm_sub_rev z x] at hTri
    linarith
  rw [expandingTestSchwartz_apply,expandingInput]
  apply hχ₁
  have hQ : 0<(n:ℝ)+1 := by positivity
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hQ.le),← div_eq_inv_mul]
  exact (div_le_one hQ).mpr hZ

/-- One constant cancellation and the normalized-ball weak test give the
near bound for the actual wavelet pairing. The bound is uniform in the
centers, so it also applies when the support balls overlap. -/
theorem centeredWaveletPair_near_bound
    (θ η : SchwartzMap Space ℂ) (hθ : ∀ z, 1<‖z‖ → θ z=0) (hη : ∀ z, 1<‖z‖ → η z=0)
    (hη₀ : (∫ z, η z)=0) :
    ∃ M₁ M₂ : ℝ, 0≤M₁ ∧ 0≤M₂ ∧ ∀ {K : Space → Space → ℂ} {C W : ℝ}
      (_hK : CalderonZygmundKernelBounds K C) (_hW : 0≤W)
      (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
      (_hPair : ∀ (f g : SchwartzMap Space ℂ), HasCompactSupport (f : Space → ℂ) →
        ∀ d : ℝ, 0<d → (∀ x y : Space, f y≠0 → g x≠0 → d≤‖x-y‖) →
        R f g = ∫ p : Space × Space, conj (g p.1)*(K p.1 p.2*f p.2)
          ∂((volume : Measure Space).prod volume))
      (_hLin : ∀ f u g : SchwartzMap Space ℂ, ∀ c : ℂ, R (f-c • u) g=R f g-c*R u g)
      (_hSkew : ∀ f g, R g f= -conj (R f g))
      (_hWeak : ∀ (x : Space) (ρ : ℝ), 0<ρ → ∀ (f g : SchwartzMap Space ℂ),
        tsupport (f : Space → ℂ) ⊆ Metric.closedBall x ρ →
        tsupport (g : Space → ℂ) ⊆ Metric.closedBall x ρ →
        (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
        (∀ (j : Fin 4) z, ‖fderiv ℝ (⇑f) z (coordinateDirection j)‖≤ρ⁻¹) →
        (∀ (j : Fin 4) z, ‖fderiv ℝ (⇑g) z (coordinateDirection j)‖≤ρ⁻¹) →
        ‖R f g‖≤W*ρ^4)
      (_hCancel : ∀ (χ g : SchwartzMap Space ℂ) (hχ : HasCompactSupport (χ : Space → ℂ)),
        (∀ z : Space, ‖z‖≤1 → χ z=1) →
        Tendsto (fun n => R (expandingTestSchwartz χ hχ n) g) atTop (𝓝 0))
      (s t : ℝ) (hs : 0<s) (ht : 0<t), s≤t →
        ∀ x y : Space, ‖R (centeredWavelet θ hθ t ht y) (centeredWavelet η hη s hs x)‖≤
          (W*M₁+C*M₂)*Real.sqrt (s/t)*(t^4)⁻¹ := by
  obtain ⟨χ,D,hD,hχ,hχs,hχ₁,hχv,hχc,hχd⟩ := exists_standardOscillationCutoff
  obtain ⟨M₁,hM₁,hLocal⟩ :=
    localOscillationRamp_wavelet_weak_bound χ θ η hχ hχs hχv D hD hχd hθ hη
  let P := SchwartzMap.seminorm ℝ 0 1 θ
  let U := SchwartzMap.seminorm ℝ 0 0 θ
  let J := ∫ z : Space, inverseFifthTail 1 z
  let G := ∫ z : Space, ‖η z‖
  have hP : 0≤P := apply_nonneg _ _
  have hU : 0≤U := apply_nonneg _ _
  have hJ : 0≤J := integral_nonneg (inverseFifthTail_nonneg 1)
  have hG : 0≤G := integral_nonneg fun _ => norm_nonneg _
  let M₂ := (P/2+3*U)*J*G
  refine ⟨M₁,M₂,hM₁,by dsimp only [M₂]; positivity,?_⟩
  intro K C W hK hW R hPair hLin hSkew hWeak hCancel s t hs ht hst x y
  let f := centeredWavelet θ hθ t ht y
  let g := centeredWavelet η hη s hs x
  let u := localOscillationRamp f χ hχ x hs
  let F := expandingTestSchwartz χ hχ
  let v (n : ℕ) := f-u-f x • F n
  let q := Real.sqrt (s/t)
  let d := t*q
  have hq : 0<q := Real.sqrt_pos.2 (div_pos hs ht)
  have hd : 0<d := mul_pos ht hq
  have hqSq : q^2=s/t := Real.sq_sqrt (div_nonneg hs.le ht.le)
  have hqLe : q≤1 := (sq_le_sq₀ hq.le zero_le_one).mp
    (by rw [hqSq,one_pow]; exact (div_le_one ht).mpr hst)
  have hS : 0<2*s := by positivity
  let L : NNReal := ⟨(t^5)⁻¹*P,mul_nonneg (inv_nonneg.mpr (pow_nonneg ht.le _)) hP⟩
  have hLip : LipschitzWith L f := centeredWavelet_lipschitz θ hθ t ht y
  have hFV (z : Space) : ‖f z‖≤(t^4)⁻¹*U := centeredWavelet_norm_le θ hθ t ht y z
  have hFLip (z : Space) : ‖f z-f x‖≤(t^5)⁻¹*P*‖x-z‖ := by
    simpa only [dist_eq_norm,norm_sub_rev z x,L,NNReal.coe_mk] using hLip.dist_le_mul z x
  obtain ⟨hUs,_,_⟩ := localOscillationRamp_bounds f χ L hLip _ D hD hFV hχ hχs hχv hχd x hs
  have hCompF : HasCompactSupport (f : Space → ℂ) := centeredWavelet_hasCompactSupport θ hθ t ht y
  have hCompU : HasCompactSupport (u : Space → ℂ) :=
    (isCompact_closedBall x (4*s)).of_isClosed_subset isClosed_closure hUs
  have hCompV (n : ℕ) : HasCompactSupport (v n : Space → ℂ) := by
    have hFC : HasCompactSupport (F n : Space → ℂ) := expandingTestSchwartz_hasCompactSupport χ hχ n
    have hTerm : HasCompactSupport ((fun _ : Space => f x) • (F n : Space → ℂ)) := hFC.smul_left
    exact (hCompF.sub hCompU).sub hTerm
  have hgm : (∫ z, g z)=0 := (centeredWavelet_integral η hη s hs x).trans hη₀
  have hgS (z : Space) (hz : g z≠0) : ‖x-z‖≤s := by
    have hz' : z ∈ tsupport (g : Space → ℂ) := subset_closure hz
    have hBall : z ∈ Metric.closedBall x s := centeredWavelet_support η hη s hs x hz'
    rw [norm_sub_rev x z,← dist_eq_norm]
    exact Metric.mem_closedBall.mp hBall
  let A := (t^5)⁻¹*P*d
  let B := 3*((t^4)⁻¹*U)
  have hA : 0≤A := by dsimp only [A]; positivity
  have hB : 0≤B := by dsimp only [B]; positivity
  let E (z : Space) := A*inverseFifthTail (2*s) (x-z)+B*inverseFifthTail d (x-z)
  obtain ⟨hTailS,hIntS⟩ := inverseFifthTail_about_center hS x
  obtain ⟨hTailD,hIntD⟩ := inverseFifthTail_about_center hd x
  have hE : Integrable E := (hTailS.const_mul A).add (hTailD.const_mul B)
  have hE₀ (z : Space) : 0≤E z := add_nonneg
    (mul_nonneg hA (inverseFifthTail_nonneg _ _)) (mul_nonneg hB (inverseFifthTail_nonneg _ _))
  have hV (n : ℕ) (z : Space) :
      v n z=(1-χ ((2*s)⁻¹ • (z-x)))*(f z-f x)+f x*(1-F n z) := by
    simp only [v,u,SchwartzMap.sub_apply,SchwartzMap.smul_apply,smul_eq_mul,localOscillationRamp_apply]
    ring
  have hLocalOne (z : Space) (hz : ‖x-z‖≤2*s) : χ ((2*s)⁻¹ • (z-x))=1 := by
    apply hχ₁
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hS.le),norm_sub_rev z x,← div_eq_inv_mul]
    exact (div_le_one hS).mpr hz
  have hRemainder : ∀ᶠ n : ℕ in atTop, ‖R (v n) g‖≤C*M₂*q*(t^4)⁻¹ := by
    filter_upwards [eventually_expandingTestSchwartz_one_on_ball χ hχ hχ₁ x (max (2*s) d)] with n hn
    have hvSep (z : Space) (hz : v n z≠0) : 2*s≤‖x-z‖ := by
      by_contra h
      have hb := (lt_of_not_ge h).le
      exact hz (by rw [hV,hLocalOne z hb,hn z (hb.trans (le_max_left _ _)),sub_self,zero_mul,mul_zero,add_zero])
    have hNear (z : Space) (hz : ‖x-z‖≤d) : ‖v n z‖≤A := by
      rw [hV,hn z (hz.trans (le_max_right _ _)),sub_self,mul_zero,add_zero,norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hχc _)).trans
        ((hFLip z).trans (mul_le_mul_of_nonneg_left hz (by positivity)))
    have hFar (z : Space) : ‖v n z‖≤B := by
      have hCut : ‖1-F n z‖≤1 := hχc _
      rw [hV]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul,norm_mul]
      have hL : ‖1-χ ((2*s)⁻¹ • (z-x))‖*‖f z-f x‖≤2*((t^4)⁻¹*U) :=
        (mul_le_of_le_one_left (norm_nonneg _) (hχc _)).trans
          ((norm_sub_le _ _).trans (by linarith only [hFV z,hFV x]))
      have hR : ‖f x‖*‖1-F n z‖≤(t^4)⁻¹*U :=
        (mul_le_of_le_one_right (norm_nonneg _) hCut).trans (hFV x)
      dsimp only [B]
      linarith only [hL,hR]
    have hMaj (z : Space) : ‖v n z‖*inverseFifthTail (2*s) (x-z)≤E z := by
      by_cases hSz : 2*s≤‖x-z‖
      · by_cases hDz : ‖x-z‖≤d
        · exact (mul_le_mul_of_nonneg_right (hNear z hDz) (inverseFifthTail_nonneg _ _)).trans
            (le_add_of_nonneg_right (mul_nonneg hB (inverseFifthTail_nonneg _ _)))
        · have hEq : inverseFifthTail (2*s) (x-z)=inverseFifthTail d (x-z) := by
            simp only [inverseFifthTail,if_pos hSz,if_pos (lt_of_not_ge hDz).le]
          rw [hEq]
          exact (mul_le_mul_of_nonneg_right (hFar z) (inverseFifthTail_nonneg _ _)).trans
            (le_add_of_nonneg_left (mul_nonneg hA (inverseFifthTail_nonneg _ _)))
      · simpa only [inverseFifthTail,if_neg hSz,mul_zero] using hE₀ z
    have hTailBound := meanZero_separatedPair_tail_bound hK R hPair (v n) g (hCompV n) hgm x s hs
      hvSep hgS E hE hMaj
    have hgInt : (∫ z, ‖g z‖)=G := centeredWavelet_integral_norm η hη s hs x
    have hIntE : (∫ z, E z)=A*((2*s)⁻¹*J)+B*(d⁻¹*J) := by
      dsimp only [E]
      rw [integral_add (hTailS.const_mul A) (hTailD.const_mul B),integral_const_mul,integral_const_mul,hIntS,hIntD]
    have hsInv : s*(2*s)⁻¹=1/2 := by field_simp [hs.ne']
    have hdInv : s*d⁻¹=q := by
      apply (mul_inv_eq_iff_eq_mul₀ hd.ne').2
      calc
        _ = t*(s/t) := by field_simp [ht.ne']
        _ = q*d := by rw [← hqSq]; dsimp only [d]; ring
    have hScaleA : A=q*(t^4)⁻¹*P := by
      dsimp only [A,d]
      field_simp [ht.ne']
    calc
      _ ≤ C*s*(∫ z, ‖g z‖)*(∫ z, E z) := hTailBound
      _ = C*G*(A*(s*(2*s)⁻¹)*J+B*(s*d⁻¹)*J) := by rw [hgInt,hIntE]; ring
      _ = _ := by rw [hsInv,hdInv,hScaleA]; dsimp only [M₂,B]; ring
  have hLinValue (n : ℕ) : R (v n) g=R f g-R u g-f x*R (F n) g := by
    dsimp only [v]
    rw [hLin,show f-u=f-(1:ℂ) • u by simp,hLin,one_mul]
  have hLim : Tendsto (fun n => R (v n) g) atTop (𝓝 (R f g-R u g)) := by
    have h := (tendsto_const_nhds (x := R f g-R u g) (f := atTop)).sub
      ((tendsto_const_nhds (x := f x) (f := atTop)).mul (hCancel χ g hχ hχ₁))
    simp only [mul_zero,sub_zero] at h
    exact h.congr fun n => (hLinValue n).symm
  have hRatio : s*(t^5)⁻¹≤q*(t^4)⁻¹ := by
    rw [show s*(t^5)⁻¹=(s/t)*(t^4)⁻¹ by field_simp [ht.ne'],← hqSq]
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hqLe)]) (by positivity)
  have hLoc : ‖R u g‖≤W*M₁*(q*(t^4)⁻¹) :=
    (hLocal R hLin hSkew hWeak s t hs ht x y).trans (by
      rw [mul_assoc (W*M₁)]
      exact mul_le_mul_of_nonneg_left hRatio (by positivity))
  calc
    _ ≤ ‖R f g-R u g‖+‖R u g‖ := by
      calc
        ‖R f g‖ = ‖(R f g-R u g)+R u g‖ := congrArg norm (sub_add_cancel (R f g) (R u g)).symm
        _ ≤ _ := norm_add_le _ _
    _ ≤ C*M₂*q*(t^4)⁻¹+W*M₁*(q*(t^4)⁻¹) := add_le_add (le_of_tendsto hLim.norm hRemainder) hLoc
    _ = _ := by dsimp only [q]; ring

end Burnett.Analysis.CarlesonEmbedding
