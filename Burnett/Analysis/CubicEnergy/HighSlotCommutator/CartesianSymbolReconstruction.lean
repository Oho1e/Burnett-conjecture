import Burnett.Analysis.CubicEnergy.HighSlotCommutator.FullCartesianHighSlotBound
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.LowCartesianQuantitative
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false
set_option maxHeartbeats 5500000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open Filter Metric MeasureTheory Set
open scoped Topology ContDiff ENNReal NNReal

private def rebuildRamp (a b t : ℝ) : ℝ :=
  Real.smoothTransition ((t-a)/(b-a))

private theorem rebuildRamp_zero {a b t : ℝ} (hab : a<b) (ht : t≤a) :
    rebuildRamp a b t=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hab.le))

private theorem rebuildRamp_one {a b t : ℝ} (hab : a<b) (ht : b≤t) :
    rebuildRamp a b t=1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by simpa using sub_le_sub_right ht a))

private theorem rebuildRamp_smooth (a b : ℝ) : ContDiff ℝ ∞ (rebuildRamp a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (b-a))

private def rebuildRadius (ρ : ℝ) : ℝ := (ρ+1/2)/2

private def rebuildHighWindow (R : ℝ) : ℝ → ℝ := rebuildRamp R (R+1)

private def rebuildRatioWindow (ρ : ℝ) (t : ℝ) : ℝ :=
  1-rebuildRamp (ρ^2) (rebuildRadius ρ^2) t

private def rebuildLowWindow (ρ R : ℝ) (p : E) : ℝ :=
  1-rebuildRamp ((ρ*(R+1))^2) ((ρ*(R+1)+1)^2) (‖p‖^2)

private def shellProfile (R : ℝ) (B : Joint → ℂ) (z : Joint) : ℂ :=
  R⁻¹ • B (R • z)

private def rebuildHigh (ρ R : ℝ) (B : Joint → ℂ) : Joint → ℂ :=
  regularizedLowCartesianSymbol (rebuildHighWindow R) (rebuildRatioWindow ρ) (shellProfile R B)

private def rebuildLow (ρ R : ℝ) (B : Joint → ℂ) (x : Joint) : ℂ :=
  (1-rebuildHighWindow R ‖x.2‖) • (rebuildLowWindow ρ R x.1 • B x)

/-- Rebuild the high end from the same symbol on one fixed high-frequency
shell, and keep the low absolute frequencies through a fixed compact window. -/
def cartesianReconstruction (ρ R : ℝ) : (Joint → ℂ) →ₗ[ℝ] (Joint → ℂ) where
  toFun B x := rebuildHigh ρ R B x + rebuildLow ρ R B x
  map_add' B₁ B₂ := by
    funext x
    simp only [rebuildHigh,rebuildLow,regularizedLowCartesianSymbol,lowCartesianSymbol,
      shellProfile,Pi.add_apply,smul_add]
    abel
  map_smul' a B := by
    funext x
    simp only [rebuildHigh,rebuildLow,regularizedLowCartesianSymbol,lowCartesianSymbol,
      shellProfile,Pi.smul_apply,RingHom.id_apply,smul_add]
    congr 1 <;> simp only [smul_smul] <;> congr 1 <;> ring

private theorem highWindow_zero (R : ℝ) (t : ℝ) (ht : t≤R) :
    rebuildHighWindow R t=0 :=
  rebuildRamp_zero (by linarith) ht

private theorem highWindow_one (R : ℝ) (t : ℝ) (ht : R+1≤t) :
    rebuildHighWindow R t=1 :=
  rebuildRamp_one (by linarith) ht

private theorem ratioWindow_one {ρ t : ℝ} (hρ : 0≤ρ) (hρ' : ρ<1/2) (ht : t≤ρ^2) :
    rebuildRatioWindow ρ t=1 := by
  have hlt : ρ<rebuildRadius ρ := by unfold rebuildRadius; linarith
  have hsq : ρ^2<(rebuildRadius ρ)^2 := pow_lt_pow_left₀ hlt hρ (by norm_num)
  simp only [rebuildRatioWindow,rebuildRamp_zero hsq ht,sub_zero]

private theorem ratioWindow_zero {ρ : ℝ} (hρ : 0≤ρ) (hρ' : ρ<1/2) (t : ℝ)
    (ht : (rebuildRadius ρ)^2≤t) :
    rebuildRatioWindow ρ t=0 := by
  have hlt : ρ<rebuildRadius ρ := by unfold rebuildRadius; linarith
  have hsq : ρ^2<(rebuildRadius ρ)^2 := pow_lt_pow_left₀ hlt hρ (by norm_num)
  simp only [rebuildRatioWindow,rebuildRamp_one hsq ht,sub_self]

private theorem lowWindow_one {ρ R : ℝ} (hρ : 0≤ρ) (hR : 1≤R) {p : E}
    (hp : ‖p‖≤ρ*(R+1)) : rebuildLowWindow ρ R p=1 := by
  have a0 : 0≤ρ*(R+1) := by positivity
  have hsq : (ρ*(R+1))^2<(ρ*(R+1)+1)^2 := pow_lt_pow_left₀ (by linarith) a0 (by norm_num)
  simp only [rebuildLowWindow,rebuildRamp_zero hsq (pow_le_pow_left₀ (norm_nonneg _) hp _),sub_zero]

private theorem lowWindow_zero {ρ R : ℝ} (hρ : 0≤ρ) (hR : 1≤R) {p : E}
    (hp : ρ*(R+1)+1≤‖p‖) : rebuildLowWindow ρ R p=0 := by
  have a0 : 0≤ρ*(R+1) := by positivity
  have hsq : (ρ*(R+1))^2<(ρ*(R+1)+1)^2 := pow_lt_pow_left₀ (by linarith) a0 (by norm_num)
  simp only [rebuildLowWindow,rebuildRamp_one hsq (pow_le_pow_left₀ (by positivity) hp _),sub_self]

private theorem shellProfile_value {R : ℝ} (hR : 1≤R) (B : Joint → ℂ)
    (hom : ∀ z : Joint, R≤‖z.2‖ → ∀ (a : ℝ), 1≤a → B (a • z)=a • B z) {x : Joint}
    (hx : R≤‖x.2‖) : ‖x.2‖ • shellProfile R B (normalizedHighPair x) = B x := by
  let n := ‖x.2‖
  have Rpos : 0<R := lt_of_lt_of_le zero_lt_one hR
  have npos : 0<n := Rpos.trans_le hx
  let z := (R/n) • x
  have hz : ‖z.2‖=R := by
    change ‖(R/n) • x.2‖=R
    rw [norm_smul,Real.norm_of_nonneg (div_nonneg Rpos.le npos.le),div_mul_cancel₀ _ npos.ne']
  have hScale : (n/R) • z=x := by
    dsimp only [z]
    rw [smul_smul, show n/R*(R/n)=1 from by field_simp,one_smul]
  have nR : 1≤n/R := (one_le_div Rpos).mpr hx
  have eq : R • normalizedHighPair x = z := by
    change R • (n⁻¹ • x) = z
    rw [smul_smul,← div_eq_mul_inv]
  rw [shellProfile,eq,smul_smul,← div_eq_mul_inv,← hom z hz.ge (n/R) nR,hScale]

/-- The reconstruction fixes every actual symbol supported in the low cone
and homogeneous of degree one above the fixed high-frequency shell. -/
theorem cartesianReconstruction_apply_eq {ρ R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hR : 1≤R) (B : Joint → ℂ)
    (supp : ∀ x : Joint, ρ*‖x.2‖<‖x.1‖ → B x=0)
    (hom : ∀ z : Joint, R≤‖z.2‖ → ∀ (a : ℝ), 1≤a → B (a • z)=a • B z) :
    cartesianReconstruction ρ R B=B := by
  funext x
  let t := ‖x.2‖
  have high : rebuildHigh ρ R B x = rebuildHighWindow R t • B x := by
    by_cases hx : R≤t
    · have eq := shellProfile_value hR B hom hx
      have hq : 0<t := (lt_of_lt_of_le zero_lt_one hR).trans_le hx
      unfold rebuildHigh regularizedLowCartesianSymbol lowCartesianSymbol
      rw [smul_comm t,eq]
      congr 1
      by_cases hp : ‖x.1‖≤ρ*t
      · have hnorm : ‖(normalizedHighPair x).1‖≤ρ := by
          change ‖t⁻¹ • x.1‖≤ρ
          rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hq.le),mul_comm,← div_eq_mul_inv]
          exact (div_le_iff₀ hq).mpr hp
        rw [ratioWindow_one hρ hρ' (pow_le_pow_left₀ (norm_nonneg _) hnorm _),one_smul]
      · rw [supp x (lt_of_not_ge hp),smul_zero]
    · dsimp only [t] at hx ⊢
      simp only [rebuildHigh,regularizedLowCartesianSymbol,highWindow_zero R _ (le_of_not_ge hx),zero_smul]
  have low : rebuildLow ρ R B x = (1-rebuildHighWindow R t) • B x := by
    unfold rebuildLow
    by_cases hx : R+1≤t
    · dsimp only [t] at hx ⊢
      simp only [highWindow_one R _ hx,sub_self,zero_smul]
    · congr 1
      by_cases hp : ‖x.1‖≤ρ*t
      · rw [lowWindow_one hρ hR (hp.trans (mul_le_mul_of_nonneg_left (le_of_not_ge hx) hρ)),one_smul]
      · rw [supp x (lt_of_not_ge hp),smul_zero]
  change rebuildHigh ρ R B x + rebuildLow ρ R B x=B x
  rw [high,low,← add_smul,show rebuildHighWindow R t + (1-rebuildHighWindow R t)=1 from by ring,one_smul]

/-- The symbol used for each original angular mode already has the support
and homogeneity needed by the exact reconstruction. -/
theorem cartesianReconstruction_eq_regularizedLowCartesianSymbol {ρ R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hR : 1≤R) (η χ : ℝ → ℝ) (b : Joint → ℂ)
    (hηone : ∀ z≥R, η z=1) (hcut : ∀ z≥ρ^2, χ z=0) :
    cartesianReconstruction ρ R (regularizedLowCartesianSymbol η χ b) =
      regularizedLowCartesianSymbol η χ b := by
  apply cartesianReconstruction_apply_eq hρ hρ' hR
  · intro x hx
    simp only [regularizedLowCartesianSymbol,lowCartesianSymbol_eq_zero_outside χ b hρ hcut hx.le,smul_zero]
  · intro x hx a ha
    have ha0 : 0<a := zero_lt_one.trans_le ha
    have hax : R≤‖(a • x : Joint).2‖ := by
      change R≤‖a • x.2‖
      rw [norm_smul,Real.norm_of_nonneg ha0.le]
      exact hx.trans (le_mul_of_one_le_left (norm_nonneg _) ha)
    simp only [regularizedLowCartesianSymbol,hηone _ hx,hηone _ hax,one_smul,
      lowCartesianSymbol_smul χ b a ha0]

private theorem rebuildLow_regular {ρ R : ℝ} (hρ : 0≤ρ) (hR : 1≤R)
    (B : Joint → ℂ) (hB : ContDiff ℝ ∞ B) :
    HasCompactSupport (rebuildLow ρ R B) ∧ ContDiff ℝ ∞ (rebuildLow ρ R B) := by
  refine ⟨?_,?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0:E) (ρ*(R+1)+1)).prod (isCompact_closedBall (0:E) (R+1)))
    intro x hx
    change rebuildLow ρ R B x≠0 at hx
    have h₁ : ‖x.1‖≤ρ*(R+1)+1 := by
      by_contra! hn
      exact hx (by simp only [rebuildLow,lowWindow_zero hρ hR hn.le,zero_smul,smul_zero])
    have h₂ : ‖x.2‖≤R+1 := by
      by_contra! hn
      exact hx (by simp only [rebuildLow,highWindow_one R _ hn.le,sub_self,zero_smul])
    exact ⟨mem_closedBall_zero_iff.mpr h₁,mem_closedBall_zero_iff.mpr h₂⟩
  · have h : ContDiff ℝ ∞ (fun x : Joint => rebuildHighWindow R ‖x.2‖) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hx : x.2=0
      · have near : ∀ᶠ y : Joint in 𝓝 x, ‖y.2‖<R :=
          (isOpen_lt continuous_snd.norm continuous_const).mem_nhds (show ‖x.2‖<R from by
            rw [hx,norm_zero]
            exact zero_lt_one.trans_le hR)
        refine (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq ?_
        filter_upwards [near] with y hy
        exact highWindow_zero R _ hy.le
      · exact (rebuildRamp_smooth R (R+1)).contDiffAt.comp x
          ((contDiffAt_norm ℝ hx).comp x contDiffAt_snd)
    have hlow : ContDiff ℝ ∞ (fun x : Joint => rebuildLowWindow ρ R x.1) :=
      contDiff_const.sub ((rebuildRamp_smooth _ _).comp ((contDiff_norm_sq ℝ).comp contDiff_fst))
    exact (contDiff_const.sub h).smul (hlow.smul hB)

private theorem norm_one_sub_ramp_le (a b t : ℝ) : ‖1-rebuildRamp a b t‖≤1 := by
  unfold rebuildRamp
  rw [Real.norm_of_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one _))]
  exact sub_le_self _ (Real.smoothTransition.nonneg _)

private theorem rebuildLow_size (ρ R : ℝ) (B : Joint → ℂ) (x : Joint) :
    ‖rebuildLow ρ R B x‖≤‖B x‖ := by
  rw [rebuildLow,norm_smul,norm_smul]
  calc
    _ ≤ 1*(1*‖B x‖) := by
      gcongr
      · exact norm_one_sub_ramp_le _ _ _
      · exact norm_one_sub_ramp_le _ _ _
    _ = _ := by simp only [one_mul]

private theorem shellProfile_smooth (R : ℝ) {B : Joint → ℂ} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (shellProfile R B) :=
  (hB.comp (contDiff_const.smul contDiff_id)).const_smul _

private theorem rebuildHigh_control {ρ R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hR : 1≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ (B : Joint → ℂ), ContDiff ℝ ∞ B →
      ContDiff ℝ ∞ (rebuildHigh ρ R B) ∧
      ∀ A : ℝ, 0≤A → (∀ x : Joint, ‖B x‖≤A*(1+‖x.1‖+‖x.2‖)) →
        ∀ x : Joint, ‖rebuildHigh ρ R B x‖≤C*A*(1+‖x.1‖+‖x.2‖) := by
  let η := rebuildHighWindow R
  let χ := rebuildRatioWindow ρ
  let ρ₁ := rebuildRadius ρ
  have Rpos : 0<R := zero_lt_one.trans_le hR
  have hρ₁ : 0≤ρ₁ := by dsimp [ρ₁,rebuildRadius]; linarith
  have hη : ContDiff ℝ ∞ η := rebuildRamp_smooth R (R+1)
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.sub (rebuildRamp_smooth _ _)
  obtain ⟨C,hC,hQ⟩ := exists_regularizedLowCartesianSymbol_quantitative_orderOne_bound 0 η χ
    Rpos hρ₁ (show 1≤R+1 by linarith) (hη.of_le (by simp)) (highWindow_zero R)
    (highWindow_one R) (hχ.of_le (by simp)) (ratioWindow_zero hρ hρ')
  let G := R⁻¹*(1+R*ρ₁+R)
  have hG : 0≤G := by dsimp [G]; positivity
  refine ⟨C*G,mul_nonneg hC hG,?_⟩
  intro B hB
  have hP := shellProfile_smooth R hB
  have smooth : ContDiff ℝ ∞ (rebuildHigh ρ R B) :=
    regularizedLowCartesianSymbol_contDiff η χ (shellProfile R B) Rpos hρ₁ hη (highWindow_zero R)
      hχ (ratioWindow_zero hρ hρ') isOpen_univ (subset_univ _) hP.contDiffOn
  refine ⟨smooth,?_⟩
  intro A hA hSize x
  have hProfile (i : ℕ) (hi : i≤0) (z : Joint) (hz : z ∈ closedBall (0:E) ρ₁ ×ˢ sphere (0:E) 1) :
      ‖iteratedFDeriv ℝ i (shellProfile R B) z‖≤G*A := by
    have h₁ := mem_closedBall_zero_iff.mp hz.1
    have h₂ := mem_sphere_zero_iff_norm.mp hz.2
    rw [Nat.eq_zero_of_le_zero hi,norm_iteratedFDeriv_zero,shellProfile,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr Rpos.le)]
    have h := hSize (R • z)
    change ‖B (R • z)‖≤A*(1+‖R • z.1‖+‖R • z.2‖) at h
    rw [norm_smul,norm_smul,Real.norm_of_nonneg Rpos.le,h₂,mul_one] at h
    calc
      _ ≤ R⁻¹*(A*(1+R*‖z.1‖+R)) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr Rpos.le)
      _ ≤ R⁻¹*(A*(1+R*ρ₁+R)) := by gcongr
      _ = _ := by unfold G; ring
  have h := hQ isOpen_univ (subset_univ _) (shellProfile R B) (G*A) (mul_nonneg hG hA)
    (hP.of_le (by simp)).contDiffOn hProfile x
  simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one,← mul_assoc] using h

/-- The linear symbol reconstruction is measurable and controlled in the
zeroth physical size weight, uniformly over the input symbol. -/
theorem exists_cartesianReconstruction_size {ρ R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hR : 1≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ (B : Joint → ℂ), ContDiff ℝ ∞ B →
      Measurable (cartesianReconstruction ρ R B) ∧
      ∀ A : ℝ, 0≤A → (∀ x : Joint, ‖B x‖≤A*(1+‖x.1‖+‖x.2‖)) →
        ∀ x : Joint, ‖cartesianReconstruction ρ R B x‖≤C*A*(1+‖x.1‖+‖x.2‖) := by
  obtain ⟨C,hC,hQ⟩ := rebuildHigh_control hρ hρ' hR
  refine ⟨C+1,by positivity,?_⟩
  intro B hB
  obtain ⟨hH,high⟩ := hQ B hB
  obtain ⟨_,hL⟩ := rebuildLow_regular hρ hR B hB
  refine ⟨(hH.add hL).continuous.measurable,?_⟩
  intro A hA hSize x
  change ‖rebuildHigh ρ R B x+rebuildLow ρ R B x‖≤_
  calc
    _ ≤ ‖rebuildHigh ρ R B x‖+‖rebuildLow ρ R B x‖ := norm_add_le _ _
    _ ≤ C*A*(1+‖x.1‖+‖x.2‖)+A*(1+‖x.1‖+‖x.2‖) :=
      add_le_add (high A hA hSize x) ((rebuildLow_size ρ R B x).trans (hSize x))
    _ = _ := by ring

/-- For each smooth symbol, the reconstructed multiplier satisfies the
original mixed-exponent estimate for all coefficients and Schwartz tests. -/
theorem exists_cartesianReconstruction_highSlot_bound_paper (inputL2 : Bool) {ρ R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hR : 1≤R)
    (B : Joint → ℂ) (hB : ContDiff ℝ ∞ B) (A : ℝ) (hA : 0≤A)
    (hSize : ∀ x : Joint, ‖B x‖≤A*(1+‖x.1‖+‖x.2‖)) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (cartesianReconstruction ρ R B) (fun x => (D x).re) f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  let η := rebuildHighWindow R
  let χ := rebuildRatioWindow ρ
  let ρ₁ := rebuildRadius ρ
  have Rpos : 0<R := zero_lt_one.trans_le hR
  have hρ₁ : 0≤ρ₁ := by dsimp [ρ₁,rebuildRadius]; linarith
  have hρ₁' : ρ₁≤1/2 := by dsimp [ρ₁,rebuildRadius]; linarith
  have hη : ContDiff ℝ ∞ η := rebuildRamp_smooth R (R+1)
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.sub (rebuildRamp_smooth _ _)
  obtain ⟨C,hC,hQ⟩ := rebuildHigh_control hρ hρ' hR
  obtain ⟨hH,hHSize⟩ := hQ B hB
  obtain ⟨hLc,hL⟩ := rebuildLow_regular hρ hR B hB
  obtain ⟨MH,hMH,high⟩ := exists_regularizedLowCartesian_highSlotSchwartz_bound_paper inputL2 η χ (shellProfile R B)
    hρ₁ hρ₁' Rpos (by linarith : 0<R+1) hη (highWindow_zero R) (highWindow_one R) hχ
    (ratioWindow_zero hρ hρ') isOpen_univ (subset_univ _) (shellProfile_smooth R hB).contDiffOn
  obtain ⟨ML,hML,low⟩ := exists_compactRadianHighCommutatorPair_bound (rebuildLow ρ R B) hLc hL
  refine ⟨MH+ML,ENNReal.add_lt_top.mpr ⟨hMH,hML⟩,?_⟩
  intro D L hD f g h
  change ‖radianHighCommutatorPair (fun x => rebuildHigh ρ R B x+rebuildLow ρ R B x)
    (fun x => (D x).re) f g h‖ₑ≤_
  rw [radianHighCommutatorPair_add_schwartz_symbols _ _ (C*A) A hH.continuous.measurable
    hL.continuous.measurable (mul_nonneg hC hA) hA (hHSize A hA hSize)
    (fun x => (rebuildLow_size ρ R B x).trans (hSize x)) D f g h]
  calc
    _ ≤ ‖radianHighCommutatorPair (rebuildHigh ρ R B) (fun x => (D x).re) f g h‖ₑ +
      ‖radianHighCommutatorPair (rebuildLow ρ R B) (fun x => (D x).re) f g h‖ₑ := enorm_add_le _ _
    _ ≤ (L : ℝ≥0∞)*MH*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) +
        (L : ℝ≥0∞)*ML*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := add_le_add (high D L hD f g h) (by
          cases inputL2
          · exact (low D L hD f g h).1
          · exact (low D L hD f g h).2)
    _ = _ := by rw [← add_mul,← mul_add]

theorem exists_cartesianReconstruction_highSlot_bound {ρ R : ℝ}
    (hρ : 0≤ρ) (hρ' : ρ<1/2) (hR : 1≤R)
    (B : Joint → ℂ) (hB : ContDiff ℝ ∞ B) (A : ℝ) (hA : 0≤A)
    (hSize : ∀ x : Joint, ‖B x‖≤A*(1+‖x.1‖+‖x.2‖)) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ f g h : SchwartzMap E ℂ,
      ‖radianHighCommutatorPair (cartesianReconstruction ρ R B) (fun x => (D x).re) f g h‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 4 2 :=
  exists_cartesianReconstruction_highSlot_bound_paper false hρ hρ' hR B hB A hA hSize

end Burnett.A06
