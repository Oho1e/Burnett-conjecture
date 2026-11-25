import Burnett.Analysis.AllScaleTransfer.CapCorrectionGeometry
import Burnett.Analysis.AllScaleTransfer.ActualCapRadialSeminorm
import Burnett.Analysis.AllScaleTransfer.LowPassCorrectionBound

set_option autoImplicit false
set_option maxHeartbeats 5300000
noncomputable section

namespace Burnett.A05

open Set Metric Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis CapFourier ProjectiveNullCaps
open scoped ContDiff Nat

def capCorrectionRatioCut (χ : ℝ → ℝ) (A : E ≃L[ℝ] E) (C : ℕ) (k : ℤ) (z : BoxSpace) : ℂ :=
  ((χ ((2 : ℝ)^k * (‖A (firstInput z)‖ / ‖A (secondInput z)‖)) -
    radialBallBump ((2 : ℝ)^((C : ℤ)+k) • firstInput z) : ℝ) : ℂ)

/-- The same parabolic map and the fixed finite offsets control the literal
cutoff difference through order forty on the fixed box support. -/
theorem exists_capCorrection_ratio_budget (B tube outer enlarged α R : ℝ) (hB : 0 < B)
    (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged) (hα : 0 < α)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (C : ℕ) (I : Finset ℤ)
    {K : Set BoxSpace} (hK : IsCompact K) (hKV : K ⊆ capCorrectionDomain α R) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ (m : Form) (u : Vec) (F : NullCapChart m u),
      ‖u‖ = 1 → ‖F.toFrequency.toContinuousLinearMap‖ ≤ B →
      ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → 4*B*(5*δ) ≤ 1 →
        let A := capFrequencyEquiv F hδ.ne'
        ∀ k ∈ I, ContDiffOn ℝ ∞ (capCorrectionRatioCut χ A C k) (capCorrectionDomain α R) ∧
          ∀ n ≤ 40, ∀ z ∈ K, ‖iteratedFDeriv ℝ n (capCorrectionRatioCut χ A C k) z‖ ≤ J := by
  classical
  let V := capCorrectionDomain α R
  have hV := capCorrectionDomain_open α R
  let L := boxToPair.toContinuousLinearMap
  let W := max 1 ‖L‖
  have hW : 1 ≤ W := le_max_left _ _
  have nonnegW : 0 ≤ W := zero_le_one.trans hW
  obtain ⟨Jρ,hJρ,radial⟩ := exists_uniform_capFrequency_radial_seminorms
    B tube outer enlarged (α/4) (1/4) 3 hB hTube hOut hOE (by positivity) (by norm_num) 40
  let T := 1 + ∑ k ∈ I, (2 : ℝ)^k
  have hT : 0 ≤ T := by unfold T; positivity
  have bT (k : ℤ) (hk : k ∈ I) : (2 : ℝ)^k ≤ T := by
    have H := Finset.single_le_sum (f := fun k : ℤ => (2 : ℝ)^k) (fun _ _ => by positivity) hk
    exact H.trans (le_add_of_nonneg_left zero_le_one)
  let D := max 1 (T*Jρ*W^40)
  have hD : 1 ≤ D := le_max_left _ _
  have nonnegD : 0 ≤ D := zero_le_one.trans hD
  obtain ⟨X,hX,jetχ⟩ := exists_compact_contDiffOn_jet_bound (isCompact_closedBall (0 : ℝ) D)
    isOpen_univ (subset_univ _) hχ.contDiffOn 40
  let G (k : ℤ) (z : BoxSpace) := radialBallBump ((2 : ℝ)^((C : ℤ)+k) • firstInput z)
  have smG (k : ℤ) : ContDiff ℝ ∞ (G k) :=
    radialBallBump.contDiff.comp (contDiff_const.smul (boxToPair.contDiff.fst : ContDiff ℝ ∞ firstInput))
  choose Bψ hBψ bψ using fun k : (↑I : Type) =>
    exists_compact_contDiffOn_jet_bound hK isOpen_univ (subset_univ _) (smG k).contDiffOn 40
  let Bump := ∑ k : (↑I : Type), Bψ k
  have hBump : 0 ≤ Bump := Finset.sum_nonneg (fun k _ => hBψ k)
  let Jχ : ℝ := ((40 ! : ℕ) : ℝ)*X*D^40
  refine ⟨Jχ+Bump,by positivity,?_⟩
  intro m u F hu hF hInv δ hδ hδone hSmall A k hk
  have bRat := (radial m u F hu hF hInv δ hδ hδone hSmall).2
  let Ω : Set FrequencyPair := {p | p.1 ≠ 0 ∧ p.2 ≠ 0}
  have hΩ : IsOpen Ω := (isOpen_ne_fun continuous_fst continuous_const).inter
    (isOpen_ne_fun continuous_snd continuous_const)
  let Ωbox := boxToPair ⁻¹' Ω
  have hΩbox : IsOpen Ωbox := hΩ.preimage boxToPair.continuous
  have vΩ : V ⊆ Ωbox := by
    intro z hz
    obtain ⟨p,q⟩ := capCorrectionDomain_left_right hz
    exact ⟨capCorrectionSlot_ne_zero p,capCorrectionSlot_ne_zero q⟩
  let ρA := physicalRadialRatio A.toContinuousLinearMap
  let r := ρA ∘ boxToPair
  have injects (x : E) (hx : x ≠ 0) : A x ≠ 0 := fun h => hx (A.injective (h.trans A.map_zero.symm))
  have np : ContDiffOn ℝ ∞ (fun p : FrequencyPair => ‖A p.1‖) Ω :=
    (A.contDiff.comp contDiff_fst).contDiffOn.norm ℝ (fun p hp => injects p.1 hp.1)
  have nq : ContDiffOn ℝ ∞ (fun p : FrequencyPair => ‖A p.2‖) Ω :=
    (A.contDiff.comp contDiff_snd).contDiffOn.norm ℝ (fun p hp => injects p.2 hp.2)
  have smoothρ : ContDiffOn ℝ ∞ ρA Ω := np.div nq (fun p hp => norm_ne_zero_iff.mpr (injects p.2 hp.2))
  have sr : ContDiffOn ℝ ∞ r V := (smoothρ.comp_continuousLinearMap L).mono vΩ
  have br (n : ℕ) (hn : n ≤ 40) (z : BoxSpace) (hz : z ∈ K) : ‖iteratedFDeriv ℝ n r z‖ ≤ Jρ*W^40 := by
    have zv := hKV hz
    obtain ⟨hp,hq⟩ := capCorrectionDomain_left_right zv
    have zΩ := vΩ zv
    have point (x : E) (hx : x ∈ capCorrectionSlot α R) :
        x ∈ radialJetAnnulus (1/4) 3 ∩
          ({p : E | (α/4)*‖p‖ ≤ |(frequencyCoordinates p).1|} ∪
            (A ⁻¹' tsupport (enlargedCapMultiplier m δ (tube*δ^2) outer enlarged u))) := by
      refine ⟨⟨hx.1.1.le,hx.1.2.1.le⟩,Or.inl ?_⟩
      change (α/4)*‖x‖ ≤ |(frequencyCoordinates x).1|
      rw [frequencyCoordinates_axis]
      exact hx.1.2.2.le
    have hRat : ‖iteratedFDeriv ℝ n ρA (L z)‖ ≤ Jρ := (bRat n hn _ (point _ hp) _ (point _ hq)).1
    rw [← iteratedFDerivWithin_of_isOpen n hΩbox zΩ]
    change ‖iteratedFDerivWithin ℝ n (ρA ∘ (L : BoxSpace → FrequencyPair)) (L ⁻¹' Ω) z‖ ≤ _
    rw [L.iteratedFDerivWithin_comp_right smoothρ hΩ.uniqueDiffOn hΩbox.uniqueDiffOn zΩ
        (WithTop.coe_le_coe.mpr le_top : (n : WithTop ℕ∞) ≤ ∞),
      iteratedFDerivWithin_of_isOpen (f := ρA) n hΩ (show L z ∈ Ω from zΩ)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact mul_le_mul hRat
      ((pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans (pow_le_pow_right₀ hW hn))
      (by positivity) hJρ.le
  let H (z : BoxSpace) : ℝ := (2 : ℝ)^k * r z
  have hH : ContDiffOn ℝ ∞ H V := contDiffOn_const.mul sr
  let Cut := χ ∘ H
  have hCut : ContDiffOn ℝ ∞ Cut V := hχ.comp_contDiffOn hH
  let RealQ (z : BoxSpace) := Cut z - G k z
  have hReal : ContDiffOn ℝ ∞ RealQ V := hCut.sub (smG k).contDiffOn
  refine ⟨Complex.ofRealCLM.contDiff.comp_contDiffOn hReal,?_⟩
  intro n hn z hz
  have zv := hKV hz
  have zV := hV.mem_nhds zv
  have bH (i : ℕ) (hi : i ≤ 40) : ‖iteratedFDeriv ℝ i H z‖ ≤ D := by
    have smoothAt : ContDiffAt ℝ i r z :=
      (sr.contDiffAt zV).of_le (WithTop.coe_le_coe.mpr le_top)
    change ‖iteratedFDeriv ℝ i (fun x => (2 : ℝ)^k • r x) z‖ ≤ D
    rw [iteratedFDeriv_const_smul_apply' smoothAt,norm_smul,Real.norm_of_nonneg (by positivity)]
    exact (mul_le_mul (bT k hk) (br i hi z hz) (norm_nonneg _) hT).trans
      (by unfold D; rw [mul_assoc]; exact le_max_right _ _)
  have Hz : H z ∈ closedBall (0 : ℝ) D := by
    apply mem_closedBall_zero_iff.mpr
    simpa only [norm_iteratedFDeriv_zero] using bH 0 (by decide)
  have hn' : (n : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have bCut : ‖iteratedFDeriv ℝ n Cut z‖ ≤ Jχ := by
    rw [← iteratedFDerivWithin_of_isOpen n hV zv]
    refine (norm_iteratedFDerivWithin_comp_le hχ.contDiffOn hH hn' uniqueDiffOn_univ
      hV.uniqueDiffOn (mapsTo_univ _ _) zv (C := X) (D := D)
      (fun i hi => by rw [iteratedFDerivWithin_univ]; exact jetχ i (hi.trans hn) _ Hz)
      (fun i hi hin => by
        rw [iteratedFDerivWithin_of_isOpen i hV zv]
        exact (bH i (hin.trans hn)).trans (by simpa only [pow_one] using pow_le_pow_right₀ hD hi))).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hn) hX)
      (pow_le_pow_right₀ hD hn) (pow_nonneg nonnegD _) (by positivity)
  have bG : ‖iteratedFDeriv ℝ n (G k) z‖ ≤ Bump :=
    (bψ ⟨k,hk⟩ n hn z hz).trans
      (Finset.single_le_sum (f := Bψ) (fun j _ => hBψ j)
        (Finset.mem_univ (⟨k,hk⟩ : (↑I : Type))))
  have cutAt := (hCut.contDiffAt zV).of_le hn'
  have gAt : ContDiffAt ℝ n (G k) z := (smG k).contDiffAt.of_le hn'
  change ‖iteratedFDeriv ℝ n (Complex.ofRealLI ∘ RealQ) z‖ ≤ Jχ+Bump
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hReal.contDiffAt zV) hn']
  have e : RealQ = Cut + (-G k) := by
    funext x
    exact sub_eq_add_neg _ _
  have he : iteratedFDeriv ℝ n (Cut + (-G k)) z =
      iteratedFDeriv ℝ n Cut z + iteratedFDeriv ℝ n (-G k) z :=
    iteratedFDeriv_add_apply cutAt gAt.neg
  rw [e,he,iteratedFDeriv_neg_apply]
  exact (norm_add_le _ _).trans (add_le_add bCut (by simpa only [norm_neg] using bG))

end Burnett.A05
