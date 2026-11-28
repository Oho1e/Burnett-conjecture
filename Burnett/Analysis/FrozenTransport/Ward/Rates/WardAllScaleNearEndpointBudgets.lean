import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearFixedCapProfile
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearProfileExtension
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearPhysicalRatio
import Burnett.Analysis.AllScaleTransfer.CapCorrectionTrace
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option maxRecDepth 8200
set_option maxHeartbeats 15000000

noncomputable section

namespace Burnett.C02

open Set Metric Filter Burnett.A05 Burnett.A05.BoxFourier Burnett.Analysis.CapFourier
open Burnett.Analysis.LowRatio (Point Angles)
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps (descendingProfile descendingProfile_range descendingProfile_eq_one
  descendingProfile_eq_zero descendingProfile_contDiff parabolicDilation parabolicDilation_contDiffOn)
open scoped ContDiff Topology

def wardNearProfileRadialLength (e : ℝ) (x : E) : ℝ :=
  Real.sqrt (‖x‖^2+e^2*descendingProfile (e^2/4) (e^2) (‖x‖^2))

private theorem wardNearProfileRadialLengthSq_pos {e : ℝ} (he : 0 < e) (x : E) :
    0 < ‖x‖^2+e^2*descendingProfile (e^2/4) (e^2) (‖x‖^2) := by
  by_cases h : x = 0
  · have hScale : e^2/4 < e^2 := by nlinarith only [sq_pos_of_pos he]
    have hT : descendingProfile (e^2/4) (e^2) 0 = 1 :=
      descendingProfile_eq_one hScale (by positivity)
    simpa only [h,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),hT,mul_one,zero_add] using sq_pos_of_pos he
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr h))
      (mul_nonneg (sq_nonneg e) (descendingProfile_range _ _ _).1)

theorem wardNearProfileRadialLength_eq {e : ℝ} (he : 0 < e) {x : E} (hx : e ≤ ‖x‖) :
    wardNearProfileRadialLength e x = ‖x‖ := by
  have hScale : e^2/4 < e^2 := by nlinarith only [sq_pos_of_pos he]
  have hT : descendingProfile (e^2/4) (e^2) (‖x‖^2) = 0 :=
    descendingProfile_eq_zero hScale (pow_le_pow_left₀ he.le hx 2)
  rw [wardNearProfileRadialLength,hT,mul_zero,add_zero,Real.sqrt_sq (norm_nonneg x)]

private theorem wardNearProfileRadialLength_contDiff {e : ℝ} (he : 0 < e) :
    ContDiff ℝ ∞ (wardNearProfileRadialLength e) := by
  have hNorm : ContDiff ℝ ∞ (fun x : E => ‖x‖^2) := contDiff_id.norm_sq ℝ
  exact (hNorm.add (contDiff_const.mul ((descendingProfile_contDiff _ _).comp hNorm))).sqrt
    (fun x => (wardNearProfileRadialLengthSq_pos he x).ne')

def wardNearEndpointInput {N : ℕ} (e : ℝ) (p : WardNearProfileParameters N) (u v : E) (ρ : ℝ) :
    WardNearProfileInput N :=
  let U := frequencyCoordinates u
  let V := frequencyCoordinates v
  let x := p.1.2.1 (parabolicDilation p.1.2.2 U)
  let y := p.1.2.1 (parabolicDilation p.1.2.2 V)
  (p,U,V,ρ * wardNearProfileRadialLength e y / wardNearProfileRadialLength e x)

private theorem wardNearEndpointInput_contDiffOn {N : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {D : Set X} {e : ℝ} (he : 0 < e)
    (p : X → WardNearProfileParameters N) (u v : X → E) (ρ : X → ℝ)
    (hp : ContDiffOn ℝ ∞ p D) (hu : ContDiffOn ℝ ∞ u D)
    (hv : ContDiffOn ℝ ∞ v D) (hρ : ContDiffOn ℝ ∞ ρ D) :
    ContDiffOn ℝ ∞ (fun x => wardNearEndpointInput e (p x) (u x) (v x) (ρ x)) D := by
  let A (x : X) (y : E) := (p x).1.2.1 (parabolicDilation (p x).1.2.2 (frequencyCoordinates y))
  have a (s : X → E) (hs : ContDiffOn ℝ ∞ s D) : ContDiffOn ℝ ∞ (fun x => A x (s x)) D :=
    hp.fst.snd.fst.clm_apply (parabolicDilation_contDiffOn hp.fst.snd.snd
      (frequencyCoordinates.contDiff.comp_contDiffOn hs))
  have R (s : X → E) (hs : ContDiffOn ℝ ∞ s D) :
      ContDiffOn ℝ ∞ (fun x => wardNearProfileRadialLength e (A x (s x))) D :=
    (wardNearProfileRadialLength_contDiff he).comp_contDiffOn (a s hs)
  have hR : ∀ x ∈ D, wardNearProfileRadialLength e (A x (u x)) ≠ 0 :=
    fun x _ => (Real.sqrt_pos.2 (wardNearProfileRadialLengthSq_pos he (A x (u x)))).ne'
  exact hp.prodMk ((frequencyCoordinates.contDiff.comp_contDiffOn hu).prodMk
    ((frequencyCoordinates.contDiff.comp_contDiffOn hv).prodMk ((hρ.mul (R v hv)).div (R u hu) hR)))

theorem wardNearEndpointInput_eq {N : ℕ} (e : ℝ) (he : 0 < e) (p : WardNearProfileParameters N)
    (u v : E) (ρ : ℝ)
    (hu : e ≤ ‖p.1.2.1 (parabolicDilation p.1.2.2 (frequencyCoordinates u))‖)
    (hv : e ≤ ‖p.1.2.1 (parabolicDilation p.1.2.2 (frequencyCoordinates v))‖) :
    wardNearEndpointInput e p u v ρ =
      (p,frequencyCoordinates u,frequencyCoordinates v,
        wardParabolicRatioOfPhysical p.1.2.1 p.1.2.2 (frequencyCoordinates u) (frequencyCoordinates v) ρ) := by
  dsimp only [wardNearEndpointInput,wardParabolicRatioOfPhysical]
  rw [wardNearProfileRadialLength_eq he hu,wardNearProfileRadialLength_eq he hv]

def wardNearEndpointProfile {N : ℕ} (F : WardNearProfileInput N → ℂ)
    (e : ℝ) (p : WardNearProfileParameters N) (u v : E) (ρ : ℝ) : ℂ :=
  F (wardNearEndpointInput e p u v ρ)

def wardNearComparableBoxProfile {N : ℕ} (F : WardNearProfileInput N → ℂ)
    (p : WardNearProfileParameters N) (k : ℤ) (z : BoxSpace) : ℂ :=
  F (p,frequencyCoordinates ((2 : ℝ)^k • firstInput z),frequencyCoordinates (secondInput z),1)

private theorem wardSignedChartLift_contDiffOn (sign : Bool) :
    ContDiffOn ℝ ∞ (signedChartLift sign) (ball (0 : EndpointAngle) 1) := by
  have hDiff : ContDiffOn ℝ ∞ (fun u : EndpointAngle => 1-‖u‖^2) (ball (0 : EndpointAngle) 1) :=
    contDiffOn_const.sub (contDiffOn_id.norm_sq ℝ)
  have hRoot := hDiff.sqrt (fun u hu => by
    have hn := (mem_ball_zero_iff.mp hu)
    have hs := (sq_lt_sq₀ (norm_nonneg u) zero_le_one).mpr hn
    exact ne_of_gt (by linarith only [hs]))
  apply contDiffOn_euclidean.mpr
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · cases sign
    · exact hRoot.neg
    · exact hRoot
  · exact (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffOn

/-- The same smooth compact extension yields the uniform one-sided
endpoint jets in all signed charts, including the actual zero-ratio trace. -/
theorem exists_wardNearEndpointProfile_jets {N : ℕ} (F : WardNearProfileInput N → ℂ)
    (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) {K : Set (WardNearProfileParameters N)}
    (hK : IsCompact K) (R b e : ℝ) (hR : R < 1) (he : 0 < e) :
    ∃ A B : ℝ, 0 ≤ A ∧
      ∀ p ∈ K,
        Measurable (fun x : Joint => wardNearEndpointProfile F e p x.1 x.2 0) ∧
        (∀ x : Joint, ‖wardNearEndpointProfile F e p x.1 x.2 0‖ ≤ B) ∧
        (∀ s : CapSigns, ContDiffOn ℝ 100 (signedEndpointProfile (wardNearEndpointProfile F e p) s)
          (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b)) ∧
        (∀ (s : CapSigns) n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
          ‖iteratedFDerivWithin ℝ n (signedEndpointProfile (wardNearEndpointProfile F e p) s)
            (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) := by
  let P := WardNearProfileParameters N
  let U : Set (P × Point) := univ ×ˢ (capCorrectionAngles 1 ×ˢ univ)
  let Q : Set (P × Point) := K ×ˢ
    ((closedBall (0 : EndpointAngle) R ×ˢ closedBall (0 : EndpointAngle) R) ×ˢ Icc (0 : ℝ) b)
  let D := capCorrectionAngles R ×ˢ Ico (0 : ℝ) b
  have hDiff : UniqueDiffOn ℝ D :=
    (isOpen_ball.prod isOpen_ball).uniqueDiffOn.prod (uniqueDiffOn_Ico 0 b)
  have hU : IsOpen U := isOpen_univ.prod ((isOpen_ball.prod isOpen_ball).prod isOpen_univ)
  have hQ : IsCompact Q := hK.prod (((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).prod isCompact_Icc)
  have hQU : Q ⊆ U := Set.prod_mono (subset_univ _)
    (Set.prod_mono (Set.prod_mono (closedBall_subset_ball hR) (closedBall_subset_ball hR)) (subset_univ _))
  have hD (p : P) (hp : p ∈ K) (z : Point) (hz : z ∈ D) : (p,z) ∈ Q :=
    ⟨hp,⟨ball_subset_closedBall hz.1.1,ball_subset_closedBall hz.1.2⟩,⟨hz.2.1,hz.2.2.le⟩⟩
  have hBounds (s : CapSigns) : ∃ A : ℝ, 0 ≤ A ∧ ∀ p ∈ K,
      ContDiffOn ℝ 100 (signedEndpointProfile (wardNearEndpointProfile F e p) s) D ∧
      ∀ n ≤ 100, ∀ z ∈ D,
        ‖iteratedFDerivWithin ℝ n (signedEndpointProfile (wardNearEndpointProfile F e p) s) D z‖ ≤ A := by
    let J (x : P × Point) := signedEndpointProfile (wardNearEndpointProfile F e x.1) s x.2
    have hFirst := (wardSignedChartLift_contDiffOn s.1).comp (contDiff_snd.fst.fst.contDiffOn (s := U))
      (fun _ hx => hx.2.1.1)
    have hSecond := (wardSignedChartLift_contDiffOn s.2).comp (contDiff_snd.fst.snd.contDiffOn (s := U))
      (fun _ hx => hx.2.1.2)
    let p₁ (x : P × Point) := x.1
    let u (x : P × Point) := signedChartLift s.1 x.2.1.1
    let v (x : P × Point) := signedChartLift s.2 x.2.1.2
    let ρ (x : P × Point) := x.2.2
    have hρ : ContDiffOn ℝ ∞ ρ U := contDiffOn_snd.snd
    have hJ : ContDiffOn ℝ ∞ J U := hF.comp_contDiffOn
      (wardNearEndpointInput_contDiffOn he p₁ u v ρ contDiffOn_fst hFirst hSecond hρ)
    obtain ⟨χ,_,_,_,hχ,hSmooth,_⟩ := exists_wardCompactProfile_extension hU hQ hQU J hJ
    let G (x : P × Point) := (χ x : ℂ)*J x
    obtain ⟨A,hA,hJets⟩ := exists_wardCompactProfile_sliceJets G hSmooth hQ 100
    refine ⟨A,hA,?_⟩
    intro p hp
    have hs : ContDiff ℝ ∞ (fun z => G (p,z)) := hSmooth.comp (contDiff_const.prodMk contDiff_id)
    have hEqual : EqOn (signedEndpointProfile (wardNearEndpointProfile F e p) s) (fun z => G (p,z)) D := by
      intro z hz
      change J (p,z) = (χ (p,z) : ℂ)*J (p,z)
      rw [hχ (p,z) (hD p hp z hz),Complex.ofReal_one,one_mul]
    refine ⟨(hs.of_le (by decide : (100 : WithTop ℕ∞) ≤ ∞)).contDiffOn.congr hEqual,?_⟩
    intro n hn z hz
    rw [iteratedFDerivWithin_congr hEqual hz n,iteratedFDerivWithin_eq_iteratedFDeriv hDiff
      (hs.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) hz]
    exact hJets n hn (p,z) (hD p hp z hz)
  classical
  choose A hA hJets using hBounds
  have hNc : HasCompactSupport (fun x => ‖F x‖) := hFc.comp_left norm_zero
  obtain ⟨B,hB⟩ := hF.continuous.norm.bddAbove_range_of_hasCompactSupport hNc
  refine ⟨∑ s, A s,B,Finset.sum_nonneg (fun s _ => hA s),?_⟩
  intro p hp
  refine ⟨?_,fun x => hB ⟨wardNearEndpointInput e p x.1 x.2 0,rfl⟩,
    fun s => (hJets s p hp).1,?_⟩
  · exact (hF.continuous.comp (contDiffOn_univ.mp
      (wardNearEndpointInput_contDiffOn (X := Joint) he (fun _ => p) Prod.fst Prod.snd (fun _ => 0)
        contDiffOn_const contDiffOn_fst contDiffOn_snd contDiffOn_const)).continuous).measurable
  · exact fun s n hn z hz => ((hJets s p hp).2 n hn z hz).trans
      (Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ s))

/-- The finite collection of actual comparable shifts consumes the same
compact profile with uniform bounds on the full radius-five joined box. -/
theorem exists_wardNearComparableBox_jets {N : ℕ} (F : WardNearProfileInput N → ℂ)
    (hF : ContDiff ℝ ∞ F) {K : Set (WardNearProfileParameters N)} (hK : IsCompact K) (I : Finset ℤ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p ∈ K,
      (∀ k ∈ I, ContDiffOn ℝ 100 (wardNearComparableBoxProfile F p k) (ball (0 : BoxSpace) 5)) ∧
      ∀ k ∈ I, ∀ n ≤ 40, ∀ z ∈ ball (0 : BoxSpace) 5,
        ‖iteratedFDeriv ℝ n (wardNearComparableBoxProfile F p k) z‖ ≤ A := by
  let V := K ×ˢ closedBall (0 : BoxSpace) 5
  have hV : IsCompact V := hK.prod (isCompact_closedBall _ _)
  have hFirst : ContDiff ℝ ∞ (firstInput : BoxSpace → E) := boxToPair.contDiff.fst
  have hSecond : ContDiff ℝ ∞ (secondInput : BoxSpace → E) := boxToPair.contDiff.snd
  have hs (k : ℤ) : ContDiff ℝ ∞ (fun x : WardNearProfileParameters N × BoxSpace =>
      wardNearComparableBoxProfile F x.1 k x.2) :=
    hF.comp (contDiff_fst.prodMk ((frequencyCoordinates.contDiff.comp
      ((contDiff_const.smul hFirst).comp contDiff_snd)).prodMk
        ((frequencyCoordinates.contDiff.comp (hSecond.comp contDiff_snd)).prodMk contDiff_const)))
  choose A hA hJ using (fun k : ↑I => exists_wardCompactProfile_sliceJets
    (fun x : WardNearProfileParameters N × BoxSpace => wardNearComparableBoxProfile F x.1 k x.2) (hs k) hV 40)
  classical
  refine ⟨∑ k, A k,Finset.sum_nonneg (fun k _ => hA k),?_⟩
  intro p hp
  refine ⟨?_,?_⟩
  · intro k _
    have he : ContDiff ℝ ∞ (wardNearComparableBoxProfile F p k) :=
      (hs k).comp ((contDiff_const : ContDiff ℝ ∞ (fun _ : BoxSpace => p)).prodMk contDiff_id)
    exact (he.of_le (by decide : (100 : WithTop ℕ∞) ≤ ∞)).contDiffOn
  · intro k hk n hn z hz
    let i : ↑I := ⟨k,hk⟩
    exact (hJ i n hn (p,z) ⟨hp,ball_subset_closedBall hz⟩).trans
      (Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i))

end Burnett.C02
