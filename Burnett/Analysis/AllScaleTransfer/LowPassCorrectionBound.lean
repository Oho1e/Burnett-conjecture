import Burnett.Analysis.AllScaleTransfer.LowPassCorrectionPartition
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option maxHeartbeats 6600000

noncomputable section

namespace Burnett.A05

open Filter Finset Metric MeasureTheory Set
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier (radianTrilinearForm radialBallBump)
open scoped ContDiff Topology

private theorem active_pair_in_box (P : ℝ) (hP : 4 < P) (ζ υ : E)
    (hζ : endpointHighProfile ζ ≠ 0) (hυ : endpointHighProfile υ ≠ 0) :
    joinedInputs ζ υ ∈ ball (0 : BoxSpace) P := by
  have hSquare : ‖joinedInputs ζ υ‖^2 = ‖ζ‖^2 + ‖υ‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq ζ, EuclideanSpace.norm_sq_eq υ,
      Fintype.sum_sum_type]
    rfl
  have h1 := (endpointHighProfile_properties.2.2 _ hζ).2
  have h2 := (endpointHighProfile_properties.2.2 _ hυ).2
  have norm4 : ‖joinedInputs ζ υ‖ ≤ 4 := by
    nlinarith only [hSquare, sq_nonneg (‖ζ‖-2), sq_nonneg (‖υ‖-2),
      mul_nonneg (norm_nonneg ζ) (sub_nonneg.mpr h1.le),
      mul_nonneg (norm_nonneg υ) (sub_nonneg.mpr h2.le), h1, h2,
      sq_nonneg (‖joinedInputs ζ υ‖-4)]
  exact mem_ball_zero_iff.mpr (norm4.trans_lt hP)

private theorem fixedShift_measurable_and_bound (P : ℝ) (hP : 4 < P)
    (d : SchwartzMap E ℂ) (G : BoxSpace → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (gCont : ContinuousOn G (ball (0 : BoxSpace) P))
    (gBound : ∀ x ∈ ball (0 : BoxSpace) P, ‖G x‖ ≤ B) (k j : ℤ) :
    Measurable (radianFixedShiftBoxBlock d G k j) ∧
      ∀ p, ‖radianFixedShiftBoxBlock d G k j p‖ ≤ B *
        (SchwartzMap.seminorm ℝ 0 0 endpointHighProfile *
          SchwartzMap.seminorm ℝ 0 0 endpointHighProfile * SchwartzMap.seminorm ℝ 0 0 d) := by
  classical
  let pScale (p : Joint) := (2 : ℝ)^(-(j+k)) • p.1
  let qScale (p : Joint) := (2 : ℝ)^(-j) • p.2
  let wScale (p : Joint) := (2 : ℝ)^(-j) • (-(p.1+p.2))
  let coord (p : Joint) := joinedInputs (pScale p) (qScale p)
  let mask (p : Joint) := endpointHighProfile (pScale p) * endpointHighProfile (qScale p) * d (wScale p)
  let crop := (ball (0 : BoxSpace) P).piecewise G (0 : BoxSpace → ℂ)
  have hp : Continuous pScale := continuous_const.smul continuous_fst
  have hq : Continuous qScale := continuous_const.smul continuous_snd
  have hw : Continuous wScale := continuous_const.smul (continuous_fst.add continuous_snd).neg
  let e : BoxSpace ≃L[ℝ] Joint := EuclideanSpace.sumEquivProd
  have eJoin (ζ υ : E) : e.symm (ζ,υ) = joinedInputs ζ υ := by
    ext i
    cases i <;> rfl
  have hCoord : Continuous coord := by
    have he : coord = fun p => e.symm (pScale p, qScale p) :=
      funext fun p => (eJoin (pScale p) (qScale p)).symm
    rw [he]
    exact e.symm.continuous.comp (hp.prodMk hq)
  have hMask : Continuous mask :=
    ((endpointHighProfile.continuous.comp hp).mul (endpointHighProfile.continuous.comp hq)).mul
      (d.continuous.comp hw)
  have hCrop : Measurable crop :=
    gCont.measurable_piecewise continuous_const.continuousOn measurableSet_ball
  have bCrop (x : BoxSpace) : ‖crop x‖ ≤ B := by
    by_cases hx : x ∈ ball (0 : BoxSpace) P
    · simpa [crop, hx] using gBound x hx
    · simpa [crop, hx] using hB
  have eq : radianFixedShiftBoxBlock d G k j = fun p => crop (coord p) * mask p := by
    funext p
    unfold radianFixedShiftBoxBlock
    rw [← endpointHighProfile_eq_integerRadialWindow (j+k) p.1,
      ← endpointHighProfile_eq_integerRadialWindow j p.2]
    change G (coord p) * mask p = crop (coord p) * mask p
    by_cases h1 : endpointHighProfile (pScale p) = 0
    · simp [mask, h1]
    by_cases h2 : endpointHighProfile (qScale p) = 0
    · simp [mask, h2]
    have hb : coord p ∈ ball (0 : BoxSpace) P := active_pair_in_box P hP _ _ h1 h2
    simp [crop, hb]
  rw [eq]
  refine ⟨(hCrop.comp hCoord.measurable).mul hMask.measurable, ?_⟩
  intro p
  have D : 0 ≤ SchwartzMap.seminorm ℝ 0 0 endpointHighProfile := apply_nonneg _ _
  have bMask : ‖mask p‖ ≤ SchwartzMap.seminorm ℝ 0 0 endpointHighProfile *
      SchwartzMap.seminorm ℝ 0 0 endpointHighProfile * SchwartzMap.seminorm ℝ 0 0 d := by
    simp only [mask, norm_mul]
    exact mul_le_mul
      (mul_le_mul (endpointHighProfile.norm_le_seminorm ℝ _) (endpointHighProfile.norm_le_seminorm ℝ _)
        (norm_nonneg _) D)
      (d.norm_le_seminorm ℝ _) (norm_nonneg _) (mul_nonneg D D)
  rw [norm_mul]
  exact mul_le_mul (bCrop _) bMask (norm_nonneg _) hB

/-- On the fixed punctured angular chart the exact correction retains the
source's C100 order, since both radial scalar factors are smooth. -/
theorem normalizedLowPassCorrection_contDiffOn (χ₀ : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ₀) (A : E ≃L[ℝ] E) (C : ℕ) (M₀ : Joint → ℂ) (k : ℤ)
    {V : Set BoxSpace}
    (nonzero : ∀ z ∈ V, firstInput z ≠ 0 ∧ secondInput z ≠ 0)
    (endpoint : ContDiffOn ℝ 100
      (fun z => radianEndpointAngular M₀ (firstInput z) (secondInput z)) V) :
    ContDiffOn ℝ 100 (normalizedLowPassCorrection χ₀ A C M₀ k) V := by
  let e : BoxSpace ≃L[ℝ] Joint := EuclideanSpace.sumEquivProd
  have hFirst : ContDiff ℝ ∞ firstInput := contDiff_fst.comp e.contDiff
  have hSecond : ContDiff ℝ ∞ secondInput := contDiff_snd.comp e.contDiff
  have hA0 (x : E) (hx : x ≠ 0) : A x ≠ 0 :=
    fun h => hx (A.injective (h.trans A.map_zero.symm))
  have hFirstNorm : ContDiffOn ℝ ∞ (fun z => ‖A (firstInput z)‖) V :=
    (A.contDiff.comp hFirst).contDiffOn.norm ℝ (fun z hz => hA0 _ (nonzero z hz).1)
  have hSecondNorm : ContDiffOn ℝ ∞ (fun z => ‖A (secondInput z)‖) V :=
    (A.contDiff.comp hSecond).contDiffOn.norm ℝ (fun z hz => hA0 _ (nonzero z hz).2)
  have hRatio := hFirstNorm.div hSecondNorm
    (fun z hz => norm_ne_zero_iff.mpr (hA0 _ (nonzero z hz).2))
  have hSmoothRatio : ContDiffOn ℝ ∞ (fun z => (2 : ℝ)^k * (‖A (firstInput z)‖ / ‖A (secondInput z)‖)) V :=
    contDiffOn_const.mul hRatio
  have hPsi : ContDiff ℝ ∞ (radialBallBump : E → ℝ) := radialBallBump.contDiff
  have hCut : ContDiffOn ℝ ∞
      (fun z => χ₀ ((2 : ℝ)^k * (‖A (firstInput z)‖ / ‖A (secondInput z)‖)) -
        radialBallBump ((2 : ℝ)^((C : ℤ)+k) • firstInput z)) V :=
    (hχ.comp_contDiffOn hSmoothRatio).sub
      (hPsi.comp (contDiff_const.smul hFirst)).contDiffOn
  exact endpoint.mul ((Complex.ofRealCLM.contDiff.comp_contDiffOn hCut).of_le
    (WithTop.coe_le_coe.mpr le_top))

/-- Use the true correction with a fixed chart cutoff. The derivative
budget applies on the cutoff support, and the plateau gives the precise
agreement with the source coefficient on both active radial windows. -/
theorem normalizedLowPassCorrection_cutoff_profile (χ₀ : ℝ → ℝ) (A : E ≃L[ℝ] E)
    (C : ℕ) (M₀ : Joint → ℂ) (k : ℤ) (β : BoxSpace → ℝ)
    (hβ : ContDiff ℝ ∞ β) {V : Set BoxSpace} (hV : IsOpen V) (hSupp : tsupport β ⊆ V)
    (hRaw : ContDiffOn ℝ 100 (normalizedLowPassCorrection χ₀ A C M₀ k) V)
    (D B : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (bβ : ∀ n ≤ 40, ∀ z ∈ tsupport β, ‖iteratedFDeriv ℝ n β z‖ ≤ D)
    (bRaw : ∀ n ≤ 40, ∀ z ∈ tsupport β,
      ‖iteratedFDeriv ℝ n (normalizedLowPassCorrection χ₀ A C M₀ k) z‖ ≤ B)
    (plateau : ∀ ζ υ : E, endpointHighProfile ζ ≠ 0 → endpointHighProfile υ ≠ 0 →
      normalizedLowPassCorrection χ₀ A C M₀ k (joinedInputs ζ υ) ≠ 0 →
        β (joinedInputs ζ υ) = 1) :
    let G := fun z => β z • normalizedLowPassCorrection χ₀ A C M₀ k z
    ContDiff ℝ 100 G ∧
      (∀ n ≤ 40, ∀ z, ‖iteratedFDeriv ℝ n G z‖ ≤ (2 : ℝ)^40 * D * B) ∧
      ∀ ζ υ : E, endpointHighProfile ζ ≠ 0 → endpointHighProfile υ ≠ 0 →
        G (joinedInputs ζ υ) = normalizedLowPassCorrection χ₀ A C M₀ k (joinedInputs ζ υ) := by
  intro G
  have hFinite : (100 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have sβ : ContDiffOn ℝ 100 β V := (hβ.of_le hFinite).contDiffOn
  have localSmooth : ContDiffOn ℝ 100 G V := sβ.smul hRaw
  have sG : ContDiff ℝ 100 G := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ V
    · exact localSmooth.contDiffAt (hV.mem_nhds hz)
    have hEvent : G =ᶠ[𝓝 z] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hSupp h))] with y hy
      change β y = 0 at hy
      simp [G, hy]
    exact contDiffAt_const.congr_of_eventuallyEq hEvent
  refine ⟨sG, ?_, ?_⟩
  · intro n hn z
    by_cases hz : z ∈ tsupport β
    · have hzV := hSupp hz
      have hn' : (n : WithTop ℕ∞) ≤ 100 := by
        exact_mod_cast (hn.trans (by decide : 40 ≤ 100))
      rw [← iteratedFDerivWithin_of_isOpen n hV hzV]
      refine (norm_iteratedFDerivWithin_smul_le sβ hRaw hV.uniqueDiffOn hzV hn').trans ?_
      calc
        _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*D*B := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [iteratedFDerivWithin_of_isOpen i hV hzV, iteratedFDerivWithin_of_isOpen (n-i) hV hzV]
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (bβ i (hi'.trans hn) z hz) (by positivity))
            (bRaw (n-i) ((Nat.sub_le n i).trans hn) z hz) (norm_nonneg _) (by positivity)
        _ = (2 : ℝ)^n*D*B := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          norm_cast
          rw [Nat.sum_range_choose]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hD) hB
    · have support : tsupport G ⊆ tsupport β := tsupport_smul_subset_left _ _
      have hZero : iteratedFDeriv ℝ n G z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hz (support (tsupport_iteratedFDeriv_subset n h)))
      rw [hZero, norm_zero]
      positivity
  · intro ζ υ hζ hυ
    by_cases hz : normalizedLowPassCorrection χ₀ A C M₀ k (joinedInputs ζ υ) = 0
    · simp only [G, hz, smul_zero]
    · simp only [G, plateau ζ υ hζ hυ hz, one_smul]

/-- The finite-offset estimate for the exact original low-pass correction
at all high radial indices. The box inputs are its actual two-input
normalized profiles, with their equality on both active radial windows. -/
theorem exists_radianLowPassCorrection_bound {χ₀ : ℝ → ℝ}
    (P L U l u : ℝ) (hP : 4 < P) (hL : 0 < L) (hU : 0 < U)
    (hl : 0 < l) (hu : 0 ≤ u) (hu1 : u < 1)
    (hOne : ∀ t, 0 ≤ t → t ≤ l → χ₀ t = 1) (hZero : ∀ t, u ≤ t → χ₀ t = 0) :
    ∃ (C H : ℕ) (K : ℝ), 3 ≤ C ∧ 4*(U/L)/(2 : ℝ)^C ≤ l ∧ 0 ≤ K ∧
      ∀ (A : E ≃L[ℝ] E), (∀ x : E, ‖A x‖ ≤ U*‖x‖) →
      ∀ M₀ : Joint → ℂ,
      (∀ (j : ℤ) (p : Joint), radianLowPassCorrectionBlock χ₀ A C M₀ j p ≠ 0 →
        L*‖p.1‖ ≤ ‖A p.1‖ ∧ L*‖p.2‖ ≤ ‖A p.2‖) →
      let I := lowPassCorrectionShifts C H
      let d := lowPassCorrectionThirdProfile L U u hL hU hu1
      ∀ (G : ℤ → BoxSpace → ℂ) (B : ℝ), 0 ≤ B →
      (∀ k ∈ I, ContDiffOn ℝ 100 (G k) (ball (0 : BoxSpace) P)) →
      (∀ k ∈ I, ∀ n ≤ 40, ∀ z ∈ ball (0 : BoxSpace) P, ‖iteratedFDeriv ℝ n (G k) z‖ ≤ B) →
      (∀ k ∈ I, ∀ ζ υ : E, endpointHighProfile ζ ≠ 0 → endpointHighProfile υ ≠ 0 →
        G k (joinedInputs ζ υ) = normalizedLowPassCorrection χ₀ A C M₀ k (joinedInputs ζ υ)) →
      ∀ f g w : SchwartzMap E ℂ,
        let correction (p : Joint) := ∑' j : ℤ, radianLowPassCorrectionBlock χ₀ A C M₀ j p
        radianTrilinearForm correction f g w =
          (∑ k ∈ I, radianFixedShiftBoxForm d (G k) k f g w) ∧
        ‖radianTrilinearForm correction f g w‖ ≤ K * B * (triLpMass f g w 3 3 3).toReal := by
  obtain ⟨C,H,hC,hThin,partition⟩ := exists_lowPassCorrection_fixedShift_partition L U l u
    hL hU hl hu hu1 hOne hZero
  let I := lowPassCorrectionShifts C H
  let d := lowPassCorrectionThirdProfile L U u hL hU hu1
  obtain ⟨K, hK, estimate⟩ := exists_radianFixedShift_box_forms_bound P hP d
  refine ⟨C,H,(I.card : ℝ)*K,hC,hThin,by positivity,?_⟩
  intro A hUpper M₀ hInput J d' G B hB hSmooth hBudget hMatches f g w correction
  let Z (j : ℤ) := radianLowPassCorrectionBlock χ₀ A C M₀ j
  let F (k : (↑I : Type)) (p : Joint) := ∑' j : ℤ, radianFixedShiftBoxBlock d (G k) k j p
  let Bblock := B * (SchwartzMap.seminorm ℝ 0 0 endpointHighProfile *
    SchwartzMap.seminorm ℝ 0 0 endpointHighProfile * SchwartzMap.seminorm ℝ 0 0 d)
  have bBlock : 0 ≤ Bblock := mul_nonneg hB
    (mul_nonneg (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) (apply_nonneg _ _))
  have actual (k : ℤ) (hk : k ∈ I) (j : ℤ) (p : Joint) :
      radianFixedShiftBoxBlock d (G k) k j p =
        radianFixedShiftBoxBlock d (normalizedLowPassCorrection χ₀ A C M₀ k) k j p := by
    by_cases hp : integerRadialWindow (j+k) p.1 = 0
    · simp only [radianFixedShiftBoxBlock, hp, Complex.ofReal_zero, zero_mul, mul_zero]
    by_cases hq : integerRadialWindow j p.2 = 0
    · simp only [radianFixedShiftBoxBlock, hq, Complex.ofReal_zero, mul_zero, zero_mul]
    have h1 : endpointHighProfile ((2 : ℝ)^(-(j+k)) • p.1) ≠ 0 := by
      rw [endpointHighProfile_eq_integerRadialWindow]
      exact_mod_cast hp
    have h2 : endpointHighProfile ((2 : ℝ)^(-j) • p.2) ≠ 0 := by
      rw [endpointHighProfile_eq_integerRadialWindow]
      exact_mod_cast hq
    unfold radianFixedShiftBoxBlock
    rw [hMatches k hk _ _ h1 h2]
  have outside {Q : Finset ℤ} {p : Joint}
      (hQ : ∀ j ∉ Q, integerRadialWindow j p.2 = 0)
      (k : ℤ) (G' : BoxSpace → ℂ) (j : ℤ) (hj : j ∉ Q) :
      radianFixedShiftBoxBlock d G' k j p = 0 := by
    simp only [radianFixedShiftBoxBlock, hQ j hj, Complex.ofReal_zero, mul_zero, zero_mul]
  have local_analytic (k : (↑I : Type)) (j : ℤ) :
      Measurable (radianFixedShiftBoxBlock d (G k) k j) ∧
      ∀ p, ‖radianFixedShiftBoxBlock d (G k) k j p‖ ≤ Bblock :=
    fixedShift_measurable_and_bound P hP d (G k) B hB (hSmooth k k.property).continuousOn
      (fun z hz => by simpa only [norm_iteratedFDeriv_zero] using hBudget k k.property 0 (by decide) z hz)
      k j
  have measured (k : (↑I : Type)) : AEStronglyMeasurable (F k) volume := by
    apply Measurable.aestronglyMeasurable
    apply measurable_of_tendsto_metrizable' (atTop : Filter (Finset ℤ))
      (f := fun Q p => ∑ j ∈ Q, radianFixedShiftBoxBlock d (G k) k j p)
    · exact fun Q => Finset.measurable_fun_sum Q (fun j _ => (local_analytic k j).1)
    · rw [tendsto_pi_nhds]
      intro p
      obtain ⟨Q, _, hQ⟩ := exists_integerRadialWindow_support_card_le_three p.2
      have hSum : HasSum (fun j : ℤ => radianFixedShiftBoxBlock d (G k) k j p) (F k p) :=
        (summable_of_ne_finset_zero (outside hQ k (G k))).hasSum
      exact hSum
  have bounded (k : (↑I : Type)) (p : Joint) : ‖F k p‖ ≤ 3*Bblock := by
    obtain ⟨Q,hCard,hQ⟩ := exists_integerRadialWindow_support_card_le_three p.2
    dsimp only [F]
    rw [tsum_eq_sum (s := Q) (outside hQ k (G k))]
    calc
      _ ≤ ∑ j ∈ Q, Bblock := norm_sum_le_of_le _ (fun j _ => (local_analytic k j).2 p)
      _ = (Q.card : ℝ)*Bblock := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) bBlock
  have together (p : Joint) : HasSum (fun k : (↑I : Type) => F k p) (correction p) := by
    obtain ⟨Q,_,hQ⟩ := exists_integerRadialWindow_support_card_le_three p.2
    have partitionAt (j : ℤ) :
        (∑ k ∈ I, radianFixedShiftBoxBlock d (G k) k j p) = Z j p := by
      calc
        _ = ∑ k ∈ I, radianFixedShiftBoxBlock d (normalizedLowPassCorrection χ₀ A C M₀ k) k j p :=
          Finset.sum_congr rfl (fun k hk => actual k hk j p)
        _ = _ := partition A hUpper M₀ hInput j p
    have hSum : (∑ k : (↑I : Type), F k p) = correction p := by
      change (∑ k ∈ I.attach, F k p) = _
      calc
        _ = ∑ k ∈ I.attach, ∑ j ∈ Q, radianFixedShiftBoxBlock d (G k) k j p :=
          Finset.sum_congr rfl (fun k _ => tsum_eq_sum (outside hQ k (G k)))
        _ = ∑ k ∈ I, ∑ j ∈ Q, radianFixedShiftBoxBlock d (G k) k j p :=
          Finset.sum_attach I (fun k => ∑ j ∈ Q, radianFixedShiftBoxBlock d (G k) k j p)
        _ = ∑ j ∈ Q, ∑ k ∈ I, radianFixedShiftBoxBlock d (G k) k j p := Finset.sum_comm
        _ = ∑ j ∈ Q, Z j p := Finset.sum_congr rfl (fun j _ => partitionAt j)
        _ = _ := by
          apply (tsum_eq_sum (s := Q) ?_).symm
          intro j hj
          simp only [Z, radianLowPassCorrectionBlock, hQ j hj, Complex.ofReal_zero, zero_mul, mul_zero]
    rw [← hSum]
    exact hasSum_fintype _
  have sumIntegral := radianTrilinearForm_hasSum_of_symbol_expansion F correction
    (fun _ => 3*Bblock) measured Summable.of_finite bounded (Eventually.of_forall together) f g w
  have expanded := sumIntegral.tsum_eq
  rw [tsum_fintype] at expanded
  change (∑ k ∈ I.attach, radianFixedShiftBoxForm d (G k) k f g w) =
    radianTrilinearForm correction f g w at expanded
  rw [Finset.sum_attach I (fun k => radianFixedShiftBoxForm d (G k) k f g w)] at expanded
  refine ⟨expanded.symm, ?_⟩
  rw [← expanded]
  exact (estimate I G B hB hSmooth hBudget f g w).2

end Burnett.A05
