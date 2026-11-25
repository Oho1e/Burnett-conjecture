import Burnett.Analysis.AllScaleTransfer.ActualUnscaledAtlasFiniteShiftRemainder
import Burnett.Analysis.AllScaleTransfer.ActualUnscaledCorrection
import Burnett.Analysis.AllScaleTransfer.ActualUnscaledAtlasTail
import Burnett.Analysis.AllScaleTransfer.AtlasSphereEndpoint
import Burnett.Analysis.AllScaleTransfer.RadianFirstLowSupport

set_option autoImplicit false
set_option maxHeartbeats 8500000

noncomputable section

namespace Burnett.A05

open Set Metric MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis CapFourier
open scoped ContDiff ENNReal

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

/-- One unscaled low slot in the manuscript. The common angular trace and
the exact positive-ratio charts determine every piece of the same
original Fourier form. No choice of dyadic truncation enters its bound. -/
theorem exists_unscaled_radian_firstLow_bound {ι : Type*} [Fintype ι]
    (V : ι → Set FrequencyPair) (U : ι → Set LowRatio.Angles)
    (angular : ι → FrequencyPair → LowRatio.Angles)
    (hV : ∀ i, IsOpen (V i)) (hU : ∀ i, IsOpen (U i))
    (hCover : radialJetAnnulus (1/2) 2 ×ˢ radialJetAnnulus (1/2) 2 ⊆ ⋃ i, V i)
    (hAnn : ∀ i, V i ⊆ radialJetAnnulus (1/4) 3 ×ˢ radialJetAnnulus (1/4) 3)
    (hAngular : ∀ i, ContDiffOn ℝ ∞ (angular i) (V i)) (hMap : ∀ i, MapsTo (angular i) (V i) (U i))
    (l u b : ℝ) (hl : 0 < l) (hu : 0 < u) (hu1 : u < 1) (hub : u < b)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hRange : ∀ t ≥ 0, ‖χ t‖ ≤ 1)
    (hOne : ∀ t, 0 ≤ t → t ≤ l → χ t = 1) (hZero : ∀ t, u ≤ t → χ t = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M : ι → LowRatio.Point → ℂ) (M₀ : Joint → ℂ) (D : ℝ), 0 ≤ D →
      (∀ i, ContDiffOn ℝ 100 (M i) (U i ×ˢ Ico (0 : ℝ) b)) →
      (∀ i n, n ≤ 100 → ∀ z ∈ U i ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n (M i) (U i ×ˢ Ico (0 : ℝ) b) z‖ ≤ D) →
      (∀ i pq, pq ∈ V i →
        M₀ (endpointDirection pq.1, endpointDirection pq.2) = M i (angular i pq, 0)) →
      ∀ (m : Joint → ℂ) (B : ℝ), 0 ≤ B → Measurable m → (∀ p, ‖m p‖ ≤ B) →
      (∀ t : ℝ, 0 < t → ∀ p : Joint, m (t • p) = m p) →
      (∀ p : Joint, p.2 ≠ 0 → m p ≠ 0 → ‖p.1‖ / ‖p.2‖ ≤ u) →
      (∀ i pq, pq ∈ V i → ∀ t : ℝ, 0 < t →
        let ρ := t * (‖pq.1‖ / ‖pq.2‖)
        ρ ∈ Ioo (0 : ℝ) b → m (t • pq.1, pq.2) = M i (angular i pq, ρ)) →
      ∀ f g h : SchwartzMap E ℂ, ‖radianTrilinearForm m f g h‖ ≤ C * D * (triLpMass f g h 3 3 3).toReal := by
  classical
  have hb : 0 < b := hu.trans hub
  have χ0 : χ 0 = 1 := hOne 0 le_rfl hl.le
  let b₀ := min l (b/2)
  have hb₀ : 0 < b₀ := lt_min hl (half_pos hb)
  have b₀b : b₀ ≤ b := (min_le_right _ _).trans (by linarith only [hb])
  have plateau (ρ : ℝ) (hρ : ρ ∈ Ioo (0 : ℝ) b₀) : χ ρ = 1 :=
    hOne ρ hρ.1.le (hρ.2.le.trans (min_le_left _ _))
  obtain ⟨C₀,hC₀,traceData⟩ := exists_sphereEndpoint_box_bound_of_atlas
    V U angular hV hU hCover hAngular hMap b hb
  obtain ⟨C₁,hC₁,endpoint⟩ := exists_sphereEndpoint_radian_bound
  obtain ⟨gap,C₂,hGap,hC₂,correction⟩ :=
    exists_unscaled_radianLowPassCorrection_bound hχ l u hl hu.le hu1 hOne hZero
  obtain ⟨cutoff,C₃,_,hC₃,tail⟩ := exists_unscaled_atlas_dyadic_remainder_tail_bound
    V U angular hV hU hCover hAnn hAngular hMap b₀ hb₀ χ χ0 plateau
  obtain ⟨H,combine⟩ := exists_radianTrilinearForm_first_low_bound u hu
  let I := Finset.Icc (-(cutoff : ℤ) + 1) (H : ℤ)
  obtain ⟨C₄,hC₄,finite⟩ := exists_unscaled_atlas_finite_shift_remainder_bound I
    V U angular hV hU hCover hAnn hAngular hMap hu hu1 hub χ hχ χ0
  let C := C₁*C₀ + C₂*C₀ + C₃*(radialGapDecay cutoff * 2) + C₄
  have hDecay : 0 ≤ radialGapDecay cutoff := by unfold radialGapDecay; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M M₀ D hD source jets matchTrace m B hB hm bM hom low mChart f g h
  let A := ContinuousLinearEquiv.refl ℝ E
  obtain ⟨traceSmooth,traceJet⟩ := traceData M M₀ D hD source jets matchTrace
  let S : Set Joint := {p | ‖p.1‖ = 1 ∧ ‖p.2‖ = 1}
  let pullback := sphereEndpointBoxPullback M₀ ∘ boxToPair.symm
  let M₀' := S.piecewise pullback (0 : Joint → ℂ)
  have hS : IsClosed S :=
    (isClosed_eq continuous_fst.norm continuous_const).inter (isClosed_eq continuous_snd.norm continuous_const)
  have dir_unit (p : E) (hp : ‖p‖ = 1) : endpointDirection p = p := by
    simp [endpointDirection,hp]
  have ann (p : Joint) (hp : p ∈ S) : boxToPair.symm p ∈ sphereEndpointAnnuli := by
    have eqF : firstInput (boxToPair.symm p) = p.1 :=
      congrArg Prod.fst (boxToPair.apply_symm_apply p)
    have eqG : secondInput (boxToPair.symm p) = p.2 :=
      congrArg Prod.snd (boxToPair.apply_symm_apply p)
    change (1/4 : ℝ) < ‖firstInput (boxToPair.symm p)‖ ∧ ‖firstInput (boxToPair.symm p)‖ < 3 ∧
      (1/4 : ℝ) < ‖secondInput (boxToPair.symm p)‖ ∧ ‖secondInput (boxToPair.symm p)‖ < 3
    rw [eqF,eqG,hp.1,hp.2]
    norm_num
  have traceMeas : Measurable M₀' :=
    (traceSmooth.continuousOn.comp boxToPair.symm.continuous.continuousOn ann).measurable_piecewise
      continuousOn_const hS.measurableSet
  have hZeroB : 0 ≤ C₀*D := mul_nonneg hC₀ hD
  have traceBound (p : Joint) : ‖M₀' p‖ ≤ C₀*D := by
    by_cases hp : p ∈ S
    · rw [show M₀' p = pullback p from piecewise_eq_of_mem S pullback 0 hp]
      simpa only [pullback,Function.comp_apply,norm_iteratedFDeriv_zero] using
        traceJet 0 (by decide) (boxToPair.symm p) (ann p hp)
    · simpa only [M₀',piecewise_eq_of_notMem S pullback (0 : Joint → ℂ) hp,Pi.zero_apply,norm_zero] using hZeroB
  have traceEq (p : Joint) (hp : p ∈ S) : M₀' p = M₀ p := by
    have ee := boxToPair.apply_symm_apply p
    have hF : firstInput (boxToPair.symm p) = p.1 := congrArg Prod.fst ee
    have hG : secondInput (boxToPair.symm p) = p.2 := congrArg Prod.snd ee
    rw [show M₀' p = pullback p from piecewise_eq_of_mem S pullback 0 hp]
    change M₀ (endpointDirection (firstInput (boxToPair.symm p)),
      endpointDirection (secondInput (boxToPair.symm p))) = M₀ p
    rw [hF,hG,dir_unit p.1 hp.1,dir_unit p.2 hp.2]
  have matchTrace' (i : ι) (pq : FrequencyPair) (hp : pq ∈ V i) :
      M₀' (endpointDirection pq.1,endpointDirection pq.2) = M i (angular i pq,0) := by
    have a := hAnn i hp
    have hp1 : pq.1 ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1/4).trans_le a.1.1)
    have hp2 : pq.2 ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1/4).trans_le a.2.1)
    have dirs : (endpointDirection pq.1,endpointDirection pq.2) ∈ S :=
      ⟨mem_sphere_zero_iff_norm.mp (endpointDirection_mem_sphere hp1),
        mem_sphere_zero_iff_norm.mp (endpointDirection_mem_sphere hp2)⟩
    exact (traceEq _ dirs).trans (matchTrace i pq hp)
  obtain ⟨traceSmooth',traceJet'⟩ := traceData M M₀' D hD source jets matchTrace'
  let rem := radianFirstLowRemainder χ A M₀' m
  have rangeRem (p : Joint) (hq : p.2 ≠ 0)
      (hr : radianRatioRemainderSymbol χ A M₀' m p ≠ 0) :
      ‖p.1‖ / ‖p.2‖ ≤ u ∧ ‖p.1‖ ≤ u * ‖p.2‖ := by
    simpa [A] using radianRatioRemainderSymbol_support χ A M₀' m 1 1 u zero_lt_one hu.le
      hZero (fun x => by simp [A]) (fun x hq hm => ⟨by simp [A], by simpa [A] using low x hq hm⟩)
      (fun _ _ => by simp [A]) p hq hr
  have remChart (i : ι) (pq : FrequencyPair) (hp : pq ∈ V i) (t : ℝ) (ht : 0 < t)
      (hρ : t*(‖pq.1‖/‖pq.2‖) ∈ Ioo (0 : ℝ) b) :
      rem (t • pq.1,pq.2) = (t*(‖pq.1‖/‖pq.2‖)) •
        LowRatio.remainder (M i) χ (angular i pq,t*(‖pq.1‖/‖pq.2‖)) := by
    have hAnn' := hAnn i hp
    have hq : pq.2 ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1/4).trans_le hAnn'.2.1)
    have exactRatio : ‖A (t • pq.1)‖ / ‖A pq.2‖ = t*(‖pq.1‖ / ‖pq.2‖) := by
      simp only [A,ContinuousLinearEquiv.refl_apply,norm_smul,Real.norm_of_nonneg ht.le,mul_div_assoc]
    have dir : endpointDirection (t • pq.1) = endpointDirection pq.1 := by
      unfold endpointDirection
      rw [norm_smul,Real.norm_of_nonneg ht.le,smul_smul,mul_inv_rev,mul_assoc,inv_mul_cancel₀ ht.ne',mul_one]
    have agree : radianEndpointAngular M₀' (t • pq.1) pq.2 = LowRatio.endpoint (M i) (angular i pq) := by
      change M₀' (endpointDirection (t • pq.1),endpointDirection pq.2) = M i (angular i pq,0)
      rw [dir,matchTrace' i pq hp]
    have e := radianFirstLowRemainder_eq_original χ χ0 A M₀' m (M i) (t • pq.1,pq.2) hq
      (angular i pq) (by simpa only [exactRatio] using mChart i pq hp t ht hρ) agree
    simpa only [rem,exactRatio] using e
  have remSupport (p : Joint) (_ : radianWeight (fun _ => 1) f g h p ≠ 0)
      (hr : rem p ≠ 0) : ‖p.1‖ / ‖p.2‖ ≤ u := by
    have hq : p.2 ≠ 0 := fun hq => hr (by simp [rem,radianFirstLowRemainder,hq])
    exact (rangeRem p hq (by simpa only [rem,radianFirstLowRemainder,if_neg hq] using hr)).1
  have small (i : ι) := oneSided_low_box_restrict (hU i) b₀b (M i) (source i) (jets i)
  have homRem := radianFirstLowRemainder_homogeneous χ A M₀' m hom
  have boundEnd := (endpoint M₀' (C₀*D) hZeroB traceSmooth' traceJet' gap f g h).2.2
  have boundCorr := correction M₀' (C₀*D) hZeroB traceSmooth' (fun n hn => traceJet' n (by omega)) f g h
  have boundTail := (tail M D hD (fun i => (small i).1) (fun i => (small i).2)
    rem homRem (fun i pq hp t ht hρ => remChart i pq hp t ht ⟨hρ.1,hρ.2.trans_le b₀b⟩) f g h).2.2
  have boundFinite := finite M D hD source jets rem homRem remChart f g h remSupport
  refine combine χ hχ.continuous.measurable hRange A gap cutoff hGap m M₀' hm traceMeas B (C₀*D)
    hB hZeroB bM traceBound (fun p hq hr => (rangeRem p hq hr).2) f g h
    D (C₁*C₀) (C₂*C₀) (C₃*(radialGapDecay cutoff*2)) C₄ ?_ ?_ ?_ boundFinite
  · simpa only [triLpMass,ENNReal.toReal_mul,SchwartzMap.toLp,Lp.norm_toLp,mul_assoc] using boundEnd
  · simpa only [mul_assoc,A] using boundCorr
  · simpa only [mul_assoc,mul_left_comm,mul_comm] using boundTail

end Burnett.A05
