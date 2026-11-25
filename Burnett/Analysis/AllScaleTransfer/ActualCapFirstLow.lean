import Burnett.Analysis.AllScaleTransfer.ActualCapLowBranchData
import Burnett.Analysis.AllScaleTransfer.ActualCapPositiveM0
import Burnett.Analysis.AllScaleTransfer.ActualCapDyadicRemainderTail
import Burnett.Analysis.AllScaleTransfer.ActualCapFiniteShiftRemainder
import Burnett.Analysis.AllScaleTransfer.ActualCapLowPassCorrection
import Burnett.Analysis.AllScaleTransfer.CapAxialChartBudget

set_option autoImplicit false
set_option maxHeartbeats 10000000

noncomputable section

namespace Burnett.A05

open Set Metric MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis CapFourier ProjectiveNullCaps
open scoped ContDiff ENNReal

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

private theorem cap_oneSided_restrict {r R d b : ℝ} (hr : r ≤ R) (hd : d ≤ b)
    (M : LowRatio.Point → ℂ) (D : ℝ)
    (hM : ContDiffOn ℝ 100 M (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b))
    (hJets : ∀ n ≤ 100, ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
      ‖iteratedFDerivWithin ℝ n M (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ D) :
    ContDiffOn ℝ 100 M (capCorrectionAngles r ×ˢ Ico (0 : ℝ) d) ∧
    ∀ n ≤ 100, ∀ z ∈ capCorrectionAngles r ×ˢ Ico (0 : ℝ) d,
      ‖iteratedFDerivWithin ℝ n M (capCorrectionAngles r ×ˢ Ico (0 : ℝ) d) z‖ ≤ D := by
  have incl : capCorrectionAngles r ×ˢ Ico (0 : ℝ) d ⊆ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b :=
    Set.prod_mono (Set.prod_mono (ball_subset_ball hr) (ball_subset_ball hr))
      (fun _ hz => ⟨hz.1,hz.2.trans_le hd⟩)
  have uq (x y : ℝ) : UniqueDiffOn ℝ (capCorrectionAngles x ×ˢ Ico (0 : ℝ) y) :=
    (isOpen_ball.prod isOpen_ball).uniqueDiffOn.prod (uniqueDiffOn_Ico 0 y)
  refine ⟨hM.mono incl,?_⟩
  intro n hn z hz
  have hn' : (n : WithTop ℕ∞) ≤ 100 := by exact_mod_cast hn
  rw [iteratedFDerivWithin_subset incl (uq r d) (uq R b) (hM.of_le hn') hz]
  exact hJets n hn z (incl hz)

private theorem signedEndpointProfile_axialLocalize (α R b : ℝ) (hR : R < 1)
    (M : E → E → ℝ → ℂ) (signs : CapSigns) :
    EqOn (signedEndpointProfile (fun p q ρ => axialLocalizeRatio α (fun x ρ => M x.1 x.2 ρ) (p,q) ρ) signs)
      (axialLocalizeChart α (signedEndpointProfile M signs))
      (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) := by
  intro z hz
  let p := signedChartLift signs.1 z.1.1
  let q := signedChartLift signs.2 z.1.2
  have ps : p ∈ sphere (0 : E) 1 :=
    (signedChartLift_unitSphere _ ((mem_ball_zero_iff.mp hz.1.1).trans hR)).1
  have qs : q ∈ sphere (0 : E) 1 :=
    (signedChartLift_unitSphere _ ((mem_ball_zero_iff.mp hz.1.2).trans hR)).1
  have np := mem_sphere_zero_iff_norm.mp ps
  have nq := mem_sphere_zero_iff_norm.mp qs
  have pd : endpointDirection p = p := by simp [endpointDirection,np]
  have qd : endpointDirection q = q := by simp [endpointDirection,nq]
  have p0 : p ≠ 0 := norm_pos_iff.mp (by rw [np]; norm_num)
  have q0 : q ≠ 0 := norm_pos_iff.mp (by rw [nq]; norm_num)
  have pe : endpointTail (endpointDirection p) = z.1.1 := by
    rw [pd]
    exact endpointTail_signedChartLift _ _
  have qe : endpointTail (endpointDirection q) = z.1.2 := by
    rw [qd]
    exact endpointTail_signedChartLift _ _
  have e := axialLocalizeChart_eval α (signedEndpointProfile M signs) p0 q0 z.2
  rw [pe,qe] at e
  exact e.symm

/-- The four exact first-low pieces on one actual normalized parabolic
cap. The axial window is placed on the original symbol and the very
same zero trace. It leaves the original projected Fourier integral equal. -/
theorem exists_actual_cap_firstLow_bound
    (B tube outer enlarged l u b : ℝ)
    (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged)
    (hl : 0 < l) (hu : 0 < u) (hu1 : u < 1) (hub : u < b)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hRange : ∀ t ≥ 0, ‖χ t‖ ≤ 1)
    (hOne : ∀ t, 0 ≤ t → t ≤ l → χ t = 1) (hZero : ∀ t, u ≤ t → χ t = 0) :
    ∃ (R C : ℝ), 0 < R ∧ R < 1 ∧ 0 ≤ C ∧
      ∀ (metric : Form) (v : Vec) (F : NullCapChart metric v), ‖v‖ = 1 →
      ‖F.toFrequency.toContinuousLinearMap‖ ≤ B → ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → 4*B*(5*δ) ≤ 1 →
      let A := capFrequencyEquiv F hδ.ne'
      let K := tsupport (enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged v)
      ∀ (M : E → E → ℝ → ℂ) (D : ℝ), 0 ≤ D →
      (∀ signs, ContDiffOn ℝ 100 (signedEndpointProfile M signs) (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b)) →
      (∀ signs n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n (signedEndpointProfile M signs)
          (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ D) →
      ∀ (m : Joint → ℂ) (Dm D₀ : ℝ), 0 ≤ Dm → 0 ≤ D₀ →
      Measurable m → (∀ p, ‖m p‖ ≤ Dm) →
      Measurable (fun p : Joint => M p.1 p.2 0) → (∀ p : Joint, ‖M p.1 p.2 0‖ ≤ D₀) →
      (∀ p : Joint, p.2 ≠ 0 → m p ≠ 0 → ‖A p.1‖/‖A p.2‖ ≤ u) →
      ∀ f g h : SchwartzMap E ℂ, EndpointFiniteAnnulus f → EndpointFiniteAnnulus g →
      (∀ p, radianFourier f p ≠ 0 → A p ∈ K) → (∀ q, radianFourier g q ≠ 0 → A q ∈ K) →
      (∀ p, radianWeight (fun _ => 1) f g h p ≠ 0 → ‖A p.1‖/‖A p.2‖ ∈ Ioo (0 : ℝ) b →
        m p = M (endpointDirection p.1) (endpointDirection p.2) (‖A p.1‖/‖A p.2‖)) →
      ‖radianTrilinearForm m f g h‖ ≤ C*D*(triLpMass f g h 3 3 3).toReal := by
  have hb : 0 < b := hu.trans hub
  have χ0 : χ 0 = 1 := hOne 0 le_rfl hl.le
  let b₀ := min l (b/2)
  have hb₀ : 0 < b₀ := lt_min hl (half_pos hb)
  have b₀b : b₀ ≤ b := (min_le_right _ _).trans (by linarith only [hb])
  have plateau (ρ : ℝ) (hρ : ρ ∈ Ioo (0 : ℝ) b₀) : χ ρ = 1 :=
    hOne ρ hρ.1.le (hρ.2.le.trans (min_le_left _ _))
  obtain ⟨α,L,hα,hα1,hL,_,axis⟩ := exists_actual_cap_axial_window_localization B tube outer enlarged hB hTube hOut hOE
  obtain ⟨r,Rcorr,hr,hrRcorr,hRcorr,tailRadius⟩ := exists_endpointTail_radii (half_pos hα)
    (by linarith only [hα1] : α/2 ≤ 1)
  let U := B * (‖frequencyCoordinates.toContinuousLinearMap‖+1)
  have hU : 0 < U := mul_pos hB (by positivity)
  obtain ⟨H,combine⟩ := exists_radianTrilinearForm_first_low_bound (u*U/L) (div_pos (mul_pos hu hU) hL)
  obtain ⟨Rt,cutoff,Ct,hRt,hRt1,_,hCt,tail⟩ := exists_actual_cap_dyadic_remainder_tail_bound
    B tube outer enlarged b₀ hB hTube hOut hOE hb₀ χ χ0 plateau
  let I := Finset.Icc (-(cutoff : ℤ) + 1) (H : ℤ)
  obtain ⟨Rf,Cf,_,hRf1,hCf,finite⟩ := exists_actual_cap_finite_shift_remainder_bound
    I B tube outer enlarged u b hB hTube hOut hOE hu hu1 hub χ hχ χ0
  obtain ⟨Re,_,hRe1,endpoint⟩ := exists_actual_cap_radian_M0_bound_of_oneSidedC100
    B tube outer enlarged b hB hTube hOut hOE hb
  let Rmax := max (max Rt Rf) (max Re Rcorr)
  let R := (Rmax+1)/2
  have hMax : Rmax < 1 := max_lt (max_lt hRt1 hRf1) (max_lt hRe1 hRcorr)
  have hMaxR : Rmax < R := by dsimp [R]; linarith only [hMax]
  have htR : Rt < R := ((le_max_left Rt Rf).trans (le_max_left _ _)).trans_lt hMaxR
  have hfR : Rf < R := ((le_max_right Rt Rf).trans (le_max_left _ _)).trans_lt hMaxR
  have heR : Re < R := ((le_max_left Re Rcorr).trans (le_max_right _ _)).trans_lt hMaxR
  have hrR : r < R := hrRcorr.trans (((le_max_right Re Rcorr).trans (le_max_right _ _)).trans_lt hMaxR)
  have hR : 0 < R := hRt.trans htR
  have hR1 : R < 1 := by dsimp [R]; linarith only [hMax]
  have openU : IsOpen (capCorrectionAngles R) := isOpen_ball.prod isOpen_ball
  have boundedU : capCorrectionAngles R ⊆ closedBall (0 : LowRatio.Angles) R := by
    intro z hz
    rw [mem_closedBall_zero_iff,Prod.norm_def]
    exact max_le (mem_ball_zero_iff.mp hz.1).le (mem_ball_zero_iff.mp hz.2).le
  obtain ⟨Kax,hKax,axJets⟩ := exists_axialLocalizeChart_oneSidedC100_bound α R b
    (capCorrectionAngles R) openU boundedU
  obtain ⟨Ce,hCe,endEstimate⟩ := endpoint (capCorrectionAngles R) openU
    (Set.prod_mono (closedBall_subset_ball heR) (closedBall_subset_ball heR))
  obtain ⟨gap,Cc,hGap,hCc,correction⟩ := exists_actual_cap_radianLowPassCorrection_bound hχ
    B tube outer enlarged α r R b l u hB hTube hOut hOE hα hrR hb tailRadius hl hu.le hu1 hOne hZero
  let C := Ce*Kax + Cc + (Ct*(2*radialGapDecay cutoff))*Kax + ((I.card : ℝ)*Cf)*Kax
  have hDecay : 0 ≤ radialGapDecay cutoff := by unfold radialGapDecay; positivity
  refine ⟨R,C,hR,hR1,by dsimp [C]; positivity,?_⟩
  intro metric v F hv hF hFI δ hδ hδ1 hSmall A K M D hD smooth jets m Dm D₀ hDm hD₀ hm bm hM₀ bM₀
    low f g h fFin gFin hf hg matchSymbol
  let M' (p q : E) (ρ : ℝ) := axialLocalizeRatio α (fun x ρ => M x.1 x.2 ρ) (p,q) ρ
  let M₀' := capCorrectionTrace α M
  let m' := axialLocalizeEndpoint α m
  obtain ⟨_,lower,equal⟩ := axis metric v F hv hFI δ hδ hSmall
  have upper (p : E) : ‖A p‖ ≤ U*‖p‖ :=
    (A.toContinuousLinearMap.le_opNorm p).trans
      (mul_le_mul_of_nonneg_right ((capFrequencyEquiv_opNorm_le F hδ hδ1 hB.le hF).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hB.le)) (norm_nonneg p))
  have tau (signs : CapSigns) :=
    axJets (signedEndpointProfile M signs) D hD (smooth signs) (jets signs)
  have sourceAx (signs : CapSigns) :
      ContDiffOn ℝ 100 (signedEndpointProfile M' signs) (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) ∧
      ∀ n ≤ 100, ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n (signedEndpointProfile M' signs)
          (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ Kax*D := by
    have e := signedEndpointProfile_axialLocalize α R b hR1 M signs
    refine ⟨(tau signs).1.congr e,?_⟩
    intro n hn z hz
    rw [iteratedFDerivWithin_congr e hz n]
    exact (tau signs).2 n hn z hz
  have sourceTail (signs : CapSigns) := cap_oneSided_restrict htR.le b₀b (signedEndpointProfile M' signs)
    (Kax*D) (sourceAx signs).1 (sourceAx signs).2
  have sourceFinite (signs : CapSigns) := cap_oneSided_restrict hfR.le le_rfl (signedEndpointProfile M' signs)
    (Kax*D) (sourceAx signs).1 (sourceAx signs).2
  have hDa : 0 ≤ Kax*D := mul_nonneg hKax hD
  obtain ⟨hm',bm'⟩ := axialLocalizeEndpoint_measurable_bounded α m hm Dm bm
  obtain ⟨hM₀',bM₀'⟩ := axialLocalizeEndpoint_measurable_bounded α (fun p : Joint => M p.1 p.2 0) hM₀ D₀ bM₀
  let rem := radianFirstLowRemainder χ A M₀' m'
  have two (p : Joint) (hp : radianWeight (fun _ => 1) f g h p ≠ 0) : A p.1 ∈ K ∧ A p.2 ∈ K :=
    ⟨hf _ (fun e => hp (by simp only [radianWeight,e,zero_mul,mul_zero])),
      hg _ (fun e => hp (by simp only [radianWeight,e,zero_mul,mul_zero]))⟩
  have mLower (p : Joint) (hq : p.2 ≠ 0) (hmp : m' p ≠ 0) :
      L*‖p.1‖ ≤ ‖A p.1‖ ∧ ‖A p.1‖/‖A p.2‖ ≤ u := by
    have no : axialCapPairWindow α p ≠ 0 :=
      fun e => hmp (by simp only [m',axialLocalizeEndpoint,e,Complex.ofReal_zero,zero_mul])
    have nm : m p ≠ 0 := fun e => hmp (by simp only [m',axialLocalizeEndpoint,e,mul_zero])
    exact ⟨(lower p no).2.2.1,low p hq nm⟩
  have eLower (p : Joint) (hmp : radianEndpointAngular M₀' p.1 p.2 ≠ 0) : L*‖p.1‖ ≤ ‖A p.1‖ := by
    have e : radianEndpointAngular M₀' p.1 p.2 =
        (axialCapPairWindow α p : ℂ) * radianEndpointAngular (fun x : Joint => M x.1 x.2 0) p.1 p.2 :=
      axialLocalizeEndpoint_eval α (fun x : Joint => M x.1 x.2 0) p
    have no : axialCapPairWindow α p ≠ 0 := fun z => hmp (by simp only [e,z,Complex.ofReal_zero,zero_mul])
    exact (lower p no).2.2.1
  have remBound := radianRatioRemainderSymbol_support χ A M₀' m' L U u hL hu.le hZero upper mLower eLower
  have remRatio (p : Joint) (_ : radianWeight (fun _ => 1) f g h p ≠ 0) (hp : rem p ≠ 0) :
      ‖A p.1‖ / ‖A p.2‖ ≤ u := by
    have hq : p.2 ≠ 0 := fun e => hp (by simp [rem,radianFirstLowRemainder,e])
    exact (remBound p hq (by simpa only [rem,radianFirstLowRemainder,if_neg hq] using hp)).1
  have remChart (signs : CapSigns) (p : Joint) (hW : radianWeight (fun _ => 1) f g h p ≠ 0)
      (sp : 0 < signedAxis signs.1 p.1) (sq : 0 < signedAxis signs.2 p.2)
      (hρ : ‖A p.1‖/‖A p.2‖ ∈ Ioo (0 : ℝ) b) :
      rem p = (‖A p.1‖/‖A p.2‖) • LowRatio.remainder (signedEndpointProfile M' signs) χ
        ((endpointTail (endpointDirection p.1),endpointTail (endpointDirection p.2)),‖A p.1‖/‖A p.2‖) := by
    have mEq : m' p = M' (endpointDirection p.1) (endpointDirection p.2) (‖A p.1‖/‖A p.2‖) := by
      change (axialCapPairWindow α p : ℂ) * m p =
        axialLocalizeRatio α (fun x ρ => M x.1 x.2 ρ)
          (endpointDirection p.1,endpointDirection p.2) (‖A p.1‖/‖A p.2‖)
      rw [axialLocalizeRatio_eval,matchSymbol p hW hρ]
    exact radianFirstLowRemainder_eq_signedCapChart χ χ0 A m' M' p signs sp sq mEq
  have eEnd := endEstimate M' (Kax*D) hDa (fun s => sourceAx s) metric v F hv hFI δ hδ hSmall
    gap f g h fFin gFin hf hg
  have eCorr := (correction metric v F hv hF hFI δ hδ hδ1 hSmall M D hD smooth jets f g h).1
  have eTail := (tail metric v F hv hF hFI δ hδ hδ1 hSmall (signedEndpointProfile M') (Kax*D) hDa
    (fun s => (sourceTail s).1) (fun s => (sourceTail s).2) rem f g h two
    (fun s p hw h1 h2 hρ => remChart s p hw h1 h2 ⟨hρ.1,hρ.2.trans_le b₀b⟩)).2.2
  have eFin := (finite metric v F hv hF hFI δ hδ hδ1 hSmall (signedEndpointProfile M') (Kax*D) hDa
    (fun s => (sourceFinite s).1) (fun s => (sourceFinite s).2) rem f g h two remRatio remChart).2
  have eForm := (equal f g h hf hg m).2
  rw [← eForm]
  refine combine χ hχ.continuous.measurable hRange A gap cutoff hGap m' M₀' hm' hM₀'
    Dm D₀ hDm hD₀ bm' bM₀' (fun p hq hr => (remBound p hq hr).2) f g h
    D (Ce*Kax) Cc ((Ct*(2*radialGapDecay cutoff))*Kax) (((I.card : ℝ)*Cf)*Kax) ?_ eCorr ?_ ?_
  · simpa only [triLpMass,ENNReal.toReal_mul,SchwartzMap.toLp,Lp.norm_toLp,mul_assoc] using eEnd
  · simpa only [mul_assoc,mul_left_comm,mul_comm] using eTail
  · simpa only [mul_assoc] using eFin

end Burnett.A05
