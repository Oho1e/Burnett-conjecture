import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearSymbolStructure
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearVertexSmooth
import Burnett.Analysis.FrozenTransport.GaugeCorrection.CyclicLowPhaseSmooth
import Burnett.Analysis.FrozenTransport.Ward.WardLowTransferDerivatives

set_option autoImplicit false
set_option maxRecDepth 9000
set_option maxHeartbeats 15500000

noncomputable section

namespace Burnett.C02

open Set Metric Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol Burnett.A05
open Burnett.Analysis.ProjectiveNullCaps hiding Index
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.V08 (signedCyclicPhase cyclicLowNormalizedPhase cyclicLowNormalizedPhase_contDiffOn
  cyclicLowProfileSet signedCyclicPhase_div_eq_lowNormalized)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix.Norms.Elementwise

open private directionDerivativeCoefficient from Burnett.Analysis.FrozenTransport.Ward.WardLowTransferDerivatives

private theorem wardNearDirection_norm_le_one (i : Index) (x : E) :
    ‖wardNearGradientDirection i x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx,wardNearGradientDirection,directionDerivativeCoefficient,endpointDirection]
  let u := endpointDirection x
  have hu : ‖u‖ = 1 := by
    simp only [u,endpointDirection,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hU : ‖u i‖ ≤ ‖u‖ := PiLp.norm_apply_le u i
  simpa only [wardNearGradientDirection,directionDerivativeCoefficient,norm_mul,norm_inv,Complex.norm_I,
    inv_one,one_mul,Complex.norm_real,hu,u] using hU

private theorem wardPurePhysicalNearWeight_norm_le_seven (ϑ : ℝ → ℝ)
    (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1) (κ δ : ℝ) (x : Joint) :
    ‖wardPurePhysicalNearWeight ϑ κ δ x‖ ≤ 7 := by
  let p := x.1
  let q := x.2
  let r := -(p+q)
  let L (u v w : E) := lowSlotWeight ϑ κ u v w
  let A (u v w : E) := angularNearWeight ϑ δ u v w
  have hL (u v w : E) : ‖L u v w‖ ≤ 1 :=
    hRange _ (div_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))))
  have hA (u v w : E) : ‖A u v w‖ ≤ 1 := by
    change ‖ϑ (projectiveWedgeSq u v/δ^2)*ϑ (projectiveWedgeSq u w/δ^2)‖ ≤ _
    rw [norm_mul,← one_mul (1:ℝ)]
    exact mul_le_mul (hRange _ (div_nonneg (projectiveWedgeSq_nonneg _ _) (sq_nonneg _)))
      (hRange _ (div_nonneg (projectiveWedgeSq_nonneg _ _) (sq_nonneg _))) (norm_nonneg _) zero_le_one
  have hC : ‖comparableSlotWeight ϑ κ p q r‖ ≤ 4 := by
    change ‖1-L p q r-L q r p-L r p q‖ ≤ _
    have e₀ := norm_sub_le (1:ℝ) (L p q r)
    have e₁ := norm_sub_le (1-L p q r) (L q r p)
    have e₂ := norm_sub_le (1-L p q r-L q r p) (L r p q)
    rw [norm_one] at e₀
    linarith only [e₀,e₁,e₂,hL p q r,hL q r p,hL r p q]
  have hP (u v w : E) : ‖L u v w*A u v w‖ ≤ 1 := by
    rw [norm_mul,← one_mul (1:ℝ)]
    exact mul_le_mul (hL _ _ _) (hA _ _ _) (norm_nonneg _) zero_le_one
  let C := comparableSlotWeight ϑ κ p q r
  have e₀ := norm_add_le C (L p q r*A p q r)
  have e₁ := norm_add_le (C+L p q r*A p q r) (L q r p*A q r p)
  have e₂ := norm_add_le (C+L p q r*A p q r+L q r p*A q r p) (L r p q*A r p q)
  change ‖C+L p q r*A p q r+L q r p*A q r p+L r p q*A r p q‖ ≤ _
  linarith only [e₀,e₁,e₂,hC,hP p q r,hP q r p,hP r p q]

private theorem exists_wardNormalizedCyclicLinearBound (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hOdd : ∀ ξ, a (-ξ) = -a ξ) (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t*a ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q r : E, p+q+r = 0 → p ≠ 0 → q ≠ 0 → r ≠ 0 →
      ‖p‖ ≤ 1 → ‖q‖ = 1 → ‖r‖ ≤ 2 → |a p+a q+a r| ≤ C*‖p‖ := by
  let Q : Set (E × E × E) := sphere (0:E) 1 ×ˢ closedBall (0:E) (1/16) ×ˢ sphere (0:E) 1
  have hQ : IsCompact Q := (isCompact_sphere _ _).prod ((isCompact_closedBall _ _).prod (isCompact_sphere _ _))
  have hQ₀ : Q ⊆ cyclicLowProfileSet := by
    intro p hp
    have e₀ := mem_sphere_zero_iff_norm.mp hp.1
    have e₁ := mem_closedBall_zero_iff.mp hp.2.1
    have e₂ := mem_sphere_zero_iff_norm.mp hp.2.2
    exact ⟨by rw [e₀]; norm_num,e₁.trans_lt (by norm_num),by rw [e₂]; norm_num⟩
  obtain ⟨Cs,hCs,small⟩ := (hQ.image_of_continuousOn
    ((cyclicLowNormalizedPhase_contDiffOn a ha).continuousOn.mono hQ₀)).isBounded.exists_pos_norm_le
  have hOn : ContinuousOn a (sphere (0 : E) 1) := ha.continuousOn.mono (fun x hx => by
    have h := mem_sphere_zero_iff_norm.mp hx
    exact norm_pos_iff.mp (by rw [h]; exact zero_lt_one))
  obtain ⟨Ca,hCa,hHead⟩ := ((isCompact_sphere (0:E) 1).image_of_continuousOn hOn).isBounded.exists_pos_norm_le
  have hNorm (x : E) (hx : x ≠ 0) : |a x| ≤ Ca*‖x‖ := by
    let u := ‖x‖⁻¹ • x
    have hu : ‖u‖ = 1 := by simp only [u,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    have hS : ‖x‖ • u = x := by simp only [u,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]
    have hA : |a u| ≤ Ca := hHead _ ⟨u,mem_sphere_zero_iff_norm.mpr hu,rfl⟩
    calc
      _ = ‖x‖ * |a u| := by
        nth_rw 1 [← hS]
        rw [hHom _ (norm_pos_iff.mpr hx),abs_mul,abs_of_nonneg (norm_nonneg x)]
      _ ≤ ‖x‖ * Ca := mul_le_mul_of_nonneg_left hA (norm_nonneg x)
      _ = _ := mul_comm _ _
  refine ⟨max Cs (64*Ca),hCs.le.trans (le_max_left _ _),?_⟩
  intro p q r hSum hp hq hr hpN hqN hrN
  by_cases hSmall : ‖p‖ ≤ 1/16
  · let u := endpointDirection p
    have hu : ‖u‖ = 1 := by
      simp only [u,endpointDirection,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg p)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp)]
    have ep : ‖p‖ • u = p := by
      simp only [u,endpointDirection,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hp),one_smul]
    have h := signedCyclicPhase_div_eq_lowNormalized a ha hOdd hHom u p q ‖p‖ 1
      (norm_pos_iff.mpr hp) zero_lt_one hqN (hSmall.trans_lt (by norm_num)) (by rw [div_one,ep])
    rw [ep,one_smul] at h
    have b := small _ ⟨(u,p,q),⟨mem_sphere_zero_iff_norm.mpr hu,mem_closedBall_zero_iff.mpr hSmall,
      mem_sphere_zero_iff_norm.mpr hqN⟩,rfl⟩
    change ‖cyclicLowNormalizedPhase a u p q‖ ≤ Cs at b
    rw [← h,Real.norm_eq_abs,abs_div,abs_of_nonneg (norm_nonneg _)] at b
    rw [triad_third_eq_neg_add hSum]
    exact ((div_le_iff₀ (norm_pos_iff.mpr hp)).mp b).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg p))
  · have h₀ := abs_add_le (a p) (a q)
    have h₁ := abs_add_le (a p+a q) (a r)
    have h₂ := mul_le_mul_of_nonneg_left hpN hCa.le
    have h₃ := mul_le_mul_of_nonneg_left hrN hCa.le
    have h₄ : 4*Ca ≤ (64*Ca)*‖p‖ := by
      have h := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hSmall)) hCa.le
      nlinarith only [h]
    have hq' : |a q| ≤ Ca := by simpa only [hqN,mul_one] using hNorm q hq
    exact (show |a p+a q+a r| ≤ 4*Ca by
      linarith only [hNorm p hp,hq',hNorm r hr,h₂,h₃,h₀,h₁]).trans
        (h₄.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg p)))

private theorem exists_wardScreenedVertex_norm_bound (G : Mat) (hG : Matrix.det G ≠ 0)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (k j l : OrderedPair) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q r : E, p ≠ 0 → q ≠ 0 → r ≠ 0 →
      ‖p‖ ≤ 2 → ‖q‖ ≤ 2 → ‖r‖ ≤ 2 →
      ‖complexPrincipalVertex G (fun d => p d) (wardNearScreenColumn G wi wo hm hη i o k p)
        (fun d => q d) (wardNearScreenColumn G wi wo hm hη i o j q)
        (fun d => r d) (wardNearScreenColumn G wi wo hm hη i o l r)‖ ≤ C := by
  let X := (E × E × E) × (E × E × E)
  let S := thinScreenAngular (inverseMatrix G) wi wo hm hη i o
  let T := wardNearScreenColumn G wi wo hm hη i o
  let O : Set X := {x | x.2.1 ≠ 0 ∧ x.2.2.1 ≠ 0 ∧ x.2.2.2 ≠ 0}
  let K : Set X := (closedBall (0:E) 2 ×ˢ closedBall (0:E) 2 ×ˢ closedBall (0:E) 2) ×ˢ
    (sphere (0:E) 1 ×ˢ sphere (0:E) 1 ×ˢ sphere (0:E) 1)
  let V (x : X) := complexPrincipalVertex G (fun d => x.1.1 d) (T k x.2.1)
    (fun d => x.1.2.1 d) (T j x.2.2.1) (fun d => x.1.2.2 d) (T l x.2.2.2)
  have hK : IsCompact K := ((isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod
      ((isCompact_sphere _ _).prod ((isCompact_sphere _ _).prod (isCompact_sphere _ _)))
  have unit (x : E) (hx : x ∈ sphere (0:E) 1) : x ≠ 0 := norm_pos_iff.mp (by
    rw [mem_sphere_zero_iff_norm.mp hx]; exact zero_lt_one)
  have hKO : K ⊆ O := fun x hx => ⟨unit _ hx.2.1,unit _ hx.2.2.1,unit _ hx.2.2.2⟩
  have hS (f : X → E) (hf : ContDiff ℝ ∞ f) (hne : ∀ x ∈ O, f x ≠ 0)
      (k l : OrderedPair) : ContDiffOn ℝ ∞ (fun x => T k (f x) l.1 l.2) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((S.smooth l k).comp hf.contDiffOn (fun x hx => hne x hx))
  have hV : ContDiffOn ℝ ∞ V O := wardComplexPrincipalVertex_contDiffOn O (fun _ => G) contDiffOn_const
    (fun _ _ => hG) (fun x => x.1.1) (fun x => x.1.2.1) (fun x => x.1.2.2)
    contDiff_fst.fst.contDiffOn contDiff_fst.snd.fst.contDiffOn contDiff_fst.snd.snd.contDiffOn
    (fun x => T k x.2.1) (fun x => T j x.2.2.1) (fun x => T l x.2.2.2)
    (hS (fun x => x.2.1) contDiff_snd.fst (fun _ hx => hx.1) k)
    (hS (fun x => x.2.2.1) contDiff_snd.snd.fst (fun _ hx => hx.2.1) j)
    (hS (fun x => x.2.2.2) contDiff_snd.snd.snd (fun _ hx => hx.2.2) l)
  obtain ⟨C,hC,hBound⟩ := (hK.image_of_continuousOn (hV.continuousOn.mono hKO)).isBounded.exists_pos_norm_le
  refine ⟨C,hC.le,?_⟩
  intro p q r hp hq hr hpN hqN hrN
  have unit' (x : E) (hx : x ≠ 0) : endpointDirection x ∈ sphere (0:E) 1 := by
    apply mem_sphere_zero_iff_norm.mpr
    rw [endpointDirection,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hD (k : OrderedPair) (p : E) (hp : p ≠ 0) : T k (endpointDirection p) = T k p := by
    funext a b
    change (S.matrix (‖p‖⁻¹ • p) (a,b) k : ℂ) = (S.matrix p (a,b) k : ℂ)
    rw [S.degree _ (inv_pos.mpr (norm_pos_iff.mpr hp))]
  have h := hBound _ ⟨((p,q,r),endpointDirection p,endpointDirection q,endpointDirection r),
    ⟨⟨mem_closedBall_zero_iff.mpr hpN,mem_closedBall_zero_iff.mpr hqN,mem_closedBall_zero_iff.mpr hrN⟩,
      unit' p hp,unit' q hq,unit' r hr⟩,rfl⟩
  simpa only [V,hD k p hp,hD j q hq,hD l r hr,T] using h

private theorem exists_wardNearGradientSymbol_min_normalized_bound (G : Mat) (hG : Matrix.det G ≠ 0)
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t*a ξ)
    (ϑ : ℝ → ℝ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1) (κ δ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (j : WardNearEntries) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x : Joint, x.1 ≠ 0 → x.2 ≠ 0 → -(x.1+x.2) ≠ 0 →
      ‖x.1‖ ≤ ‖x.2‖ → ‖x.1‖ ≤ ‖-(x.1+x.2)‖ →
      ‖wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o j x‖ ≤ H := by
  obtain ⟨C,hC,hLinear⟩ := exists_wardNormalizedCyclicLinearBound a ha hOdd hHom
  obtain ⟨B,hB,hVertex⟩ := exists_wardScreenedVertex_norm_bound G hG wi wo hm hη i o j.1.1 j.2.1.1 j.2.2.1
  let H := ‖-Complex.I/3‖ * 7 * (2*C*B)
  refine ⟨H,by dsimp [H]; positivity,?_⟩
  intro x hp₀ hq₀ hr₀ hpq₀ hpr₀
  let t := ‖x.2‖⁻¹
  have ht : 0 < t := inv_pos.mpr (norm_pos_iff.mpr hq₀)
  let y : Joint := t • x
  let p := y.1
  let q := y.2
  let r := -(p+q)
  have hp : p ≠ 0 := smul_ne_zero ht.ne' hp₀
  have hq : q ≠ 0 := smul_ne_zero ht.ne' hq₀
  have hr' : r = t • (-(x.1+x.2)) := by
    change -(t • x.1+t • x.2) = _
    rw [smul_neg,smul_add]
  have hr : r ≠ 0 := hr'.symm ▸ smul_ne_zero ht.ne' hr₀
  have hqN : ‖q‖ = 1 := by
    change ‖t • x.2‖ = 1
    rw [norm_smul,Real.norm_of_nonneg ht.le,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq₀)]
  have hpq : ‖p‖ ≤ ‖q‖ := by
    change ‖t • x.1‖ ≤ ‖t • x.2‖
    simp only [norm_smul,Real.norm_of_nonneg ht.le]
    exact mul_le_mul_of_nonneg_left hpq₀ ht.le
  have hpr : ‖p‖ ≤ ‖r‖ := by
    change ‖t • x.1‖ ≤ _
    rw [hr']
    simp only [norm_smul,Real.norm_of_nonneg ht.le]
    exact mul_le_mul_of_nonneg_left hpr₀ ht.le
  have hSum : p+q+r = 0 := add_neg_cancel (p+q)
  have hpN : ‖p‖ ≤ 1 := hpq.trans_eq hqN
  have hrN : ‖r‖ ≤ 2 := by have h := (high_norm_diff_of_triad hSum).2; linarith only [h,hpN,hqN]
  have hrLow : 1/2 ≤ ‖r‖ := by
    have h := (high_norm_diff_of_triad hSum).1
    linarith only [h,hpr,hqN]
  have hLinear' : |a p+a q+a r| ≤ C*‖p‖ := hLinear p q r hSum hp hq hr hpN hqN hrN
  let T := wardNearScreenColumn G wi wo hm hη i o
  let Γ := complexPrincipalVertex G (fun d => p d) (T j.1.1 p) (fun d => q d) (T j.2.1.1 q)
    (fun d => r d) (T j.2.2.1 r)
  have hΓ : ‖Γ‖ ≤ B := hVertex p q r hp hq hr (hpN.trans (by norm_num)) (hqN.le.trans (by norm_num)) hrN
  have hD : 0 < ‖p‖*‖q‖*‖r‖ :=
    mul_pos (mul_pos (norm_pos_iff.mpr hp) (norm_pos_iff.mpr hq)) (norm_pos_iff.mpr hr)
  have hRatio : |a p+a q+a r| * ‖Γ‖/(‖p‖*‖q‖*‖r‖) ≤ 2*C*B := by
    apply (div_le_iff₀ hD).mpr
    calc
      _ ≤ (C*‖p‖)*B := mul_le_mul hLinear' hΓ (norm_nonneg _) (mul_nonneg hC (norm_nonneg p))
      _ ≤ (2*C*B)*(‖p‖*‖q‖*‖r‖) := by
        rw [hqN,mul_one]
        have h := mul_le_mul_of_nonneg_left hrLow (show 0 ≤ 2*C*B*‖p‖ by positivity)
        nlinarith only [h]
  rw [← wardNearGradientSymbol_homogeneous G hG a hHom ϑ κ δ wi wo hm hη i o j t ht x]
  change ‖wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o j y‖ ≤ H
  change ‖(-Complex.I/3)*(wardPurePhysicalNearWeight ϑ κ δ y : ℂ)*
    (((a p+a q+a r : ℝ):ℂ)*Γ/((‖p‖*‖q‖*‖r‖ : ℝ):ℂ))*
    (wardNearGradientDirection j.1.2 p*wardNearGradientDirection j.2.1.2 q*
      wardNearGradientDirection j.2.2.2 r)‖ ≤ _
  have hRatioNorm : ‖(((a p+a q+a r : ℝ):ℂ)*Γ/((‖p‖*‖q‖*‖r‖ : ℝ):ℂ))‖ =
      |a p+a q+a r| * ‖Γ‖/(‖p‖*‖q‖*‖r‖) := by
    rw [norm_div,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs (a p+a q+a r),Real.norm_of_nonneg hD.le]
  rw [norm_mul,norm_mul,norm_mul,hRatioNorm,Complex.norm_real]
  have hDirections : ‖wardNearGradientDirection j.1.2 p*wardNearGradientDirection j.2.1.2 q*
      wardNearGradientDirection j.2.2.2 r‖ ≤ 1 := by
    simp only [norm_mul]
    calc
      _ ≤ 1*1*1 := mul_le_mul
        (mul_le_mul (wardNearDirection_norm_le_one _ _) (wardNearDirection_norm_le_one _ _)
          (norm_nonneg _) zero_le_one) (wardNearDirection_norm_le_one _ _) (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hQuot : 0 ≤ |a p+a q+a r| * ‖Γ‖/(‖p‖*‖q‖*‖r‖) :=
    div_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hD.le
  exact (mul_le_of_le_one_right (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hQuot) hDirections).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (wardPurePhysicalNearWeight_norm_le_seven ϑ hRange κ δ y) (norm_nonneg _))
      hRatio hQuot (mul_nonneg (norm_nonneg _) (by norm_num)))

/-- The exact C02 near coefficient is globally bounded. The potentially
small slot is moved to the first position using the actual kernel cycle. -/
theorem exists_wardNearGradientSymbol_bound (G : Mat) (hG : Matrix.det G ≠ 0)
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t*a ξ)
    (ϑ : ℝ → ℝ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1) (κ δ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (hi : 0 ≤ i) (hIO : i < o) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ j x, ‖wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o j x‖ ≤ H := by
  classical
  choose H hH hBound using (fun j => exists_wardNearGradientSymbol_min_normalized_bound G hG a ha hOdd hHom
    ϑ hRange κ δ wi wo hm hη i o j)
  let B := ∑ j, H j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hH j)
  have leB (j : WardNearEntries) : H j ≤ B := Finset.single_le_sum (fun j _ => hH j) (Finset.mem_univ j)
  refine ⟨B,hB,?_⟩
  intro j x
  let m := wardNearGradientSymbol G a ϑ κ δ wi wo hm hη i o
  by_cases h : m j x = 0
  · simpa only [m] using (show ‖m j x‖ ≤ B by rw [h,norm_zero]; exact hB)
  · let p := x.1
    let q := x.2
    let r := -(p+q)
    obtain ⟨hp,hq,hr,_⟩ := wardNearGradientSymbol_support G hG a ϑ κ δ wi wo hm hη i o hi hIO j x h
    have e₁ : -(q+r) = p := by dsimp only [r]; abel
    have e₂ : -(r+p) = q := by dsimp only [r]; abel
    let rot (j : WardNearEntries) : WardNearEntries := (j.2.1,j.2.2,j.1)
    have hCycle (j : WardNearEntries) (x : Joint) : m (rot j) (radianCycle x) = m j x :=
      wardNearGradientSymbol_cycle G a ϑ κ δ wi wo hm hη i o (rot j) x
    change ‖m j x‖ ≤ B
    by_cases hpq : ‖p‖ ≤ ‖q‖ <;> by_cases hpr : ‖p‖ ≤ ‖r‖
    · exact (hBound j x hp hq hr hpq hpr).trans (leB j)
    · rw [← hCycle j x,← hCycle (rot j) (radianCycle x)]
      apply le_trans (hBound (rot (rot j)) (radianCycle (radianCycle x)) ?_ ?_ ?_ ?_ ?_) (leB _)
      · exact hr
      · rwa [show (radianCycle (radianCycle x)).2 = -(q+r) from rfl,e₁]
      · change -(r+(-(q+r))) ≠ 0
        rwa [e₁,e₂]
      · change ‖r‖ ≤ ‖-(q+r)‖
        rw [e₁]
        exact le_of_not_ge hpr
      · change ‖r‖ ≤ ‖-(r+(-(q+r)))‖
        rw [e₁,e₂]
        exact (le_of_not_ge hpr).trans hpq
    · rw [← hCycle j x]
      apply le_trans (hBound (rot j) (radianCycle x) hq hr ?_ ?_ ?_) (leB _)
      · change -(q+r) ≠ 0
        rwa [e₁]
      · exact (le_of_not_ge hpq).trans hpr
      · change ‖q‖ ≤ ‖-(q+r)‖
        rw [e₁]
        exact le_of_not_ge hpq
    · by_cases hqr : ‖q‖ ≤ ‖r‖
      · rw [← hCycle j x]
        apply le_trans (hBound (rot j) (radianCycle x) hq hr ?_ hqr ?_) (leB _)
        · change -(q+r) ≠ 0
          rwa [e₁]
        · change ‖q‖ ≤ ‖-(q+r)‖
          rw [e₁]
          exact le_of_not_ge hpq
      · rw [← hCycle j x,← hCycle (rot j) (radianCycle x)]
        apply le_trans (hBound (rot (rot j)) (radianCycle (radianCycle x)) ?_ ?_ ?_ ?_ ?_) (leB _)
        · exact hr
        · rwa [show (radianCycle (radianCycle x)).2 = -(q+r) from rfl,e₁]
        · change -(r+(-(q+r))) ≠ 0
          rwa [e₁,e₂]
        · change ‖r‖ ≤ ‖-(q+r)‖
          rw [e₁]
          exact (le_of_not_ge hqr).trans (le_of_not_ge hpq)
        · change ‖r‖ ≤ ‖-(r+(-(q+r)))‖
          rw [e₁,e₂]
          exact le_of_not_ge hqr

end Burnett.C02
