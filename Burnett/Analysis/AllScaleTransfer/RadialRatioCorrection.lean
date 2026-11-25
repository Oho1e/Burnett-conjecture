import Burnett.Analysis.AllScaleTransfer.RadialThirdCutoff
import Burnett.Analysis.AngularCaps.CapFrequencyCoordinates
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

namespace Burnett.Analysis.CapFourier

open Set Burnett.Analysis.ProjectiveNullCaps

/-- A common two-sided norm comparison on the actual enlarged-cap supports.
The displayed constants are chosen before the form, the frame and the scale. -/
theorem exists_uniform_capFrequency_norm_compare (B a outer enlarged : ℝ)
    (hB : 0 < B) (ha : 0 < a) (hOut : 0 ≤ outer) (hOE : outer < enlarged) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧
      ∀ (m : Form) (w : Vec) (F : NullCapChart m w),
        ‖w‖ = 1 → ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
        ∀ (δ : ℝ) (hδ : 0 < δ), 4*B*(5*δ) ≤ 1 →
          ∀ p : Space, capFrequencyEquiv F hδ.ne' p ∈
            tsupport (enlargedCapMultiplier m δ (a*δ^2) outer enlarged w) →
            L*‖p‖ ≤ ‖capFrequencyEquiv F hδ.ne' p‖ ∧
              ‖capFrequencyEquiv F hδ.ne' p‖ ≤ U*‖p‖ := by
  let Z := 4*B*5
  let T := Z^2 + 4*(enlarged*a)
  let M := max 1 (max Z T)
  let D := ‖frequencyCoordinates.symm.toContinuousLinearMap‖ + 1
  let U := 2*(‖frequencyCoordinates.toContinuousLinearMap‖ + 1)
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hU : 0 < U := by dsimp only [U]; positivity
  have hDen : 0 < D*(M*B) := mul_pos hD (mul_pos hM hB)
  refine ⟨(D*(M*B))⁻¹, U, inv_pos.mpr hDen, hU, ?_⟩
  intro m w F hw hI δ hδ hSmall p hsupport
  by_cases hp : p = 0
  · simp only [hp, map_zero, norm_zero, mul_zero, le_refl, and_self]
  let u := frequencyCoordinates p
  let x := capFrequencyEquiv F hδ.ne' p
  have hx : x ≠ 0 := by
    intro h
    apply hp
    exact (capFrequencyEquiv F hδ.ne').injective (h.trans (map_zero _).symm)
  have hw0 : w ≠ 0 := by
    intro h
    simp [h] at hw
  have hη : 0 < a*δ^2 := mul_pos ha (pow_pos hδ _)
  have hE : 0 ≤ enlarged*a := mul_nonneg (hOut.trans hOE.le) ha.le
  have hSupp := enlargedCapMultiplier_tsupport_bounds hδ hη hOut hOE hw0 hx hsupport
  have hCone : |quadratic m x| ≤ (enlarged*a)*δ^2*‖x‖^2 := by
    convert hSupp.2 using 1
    ring
  have h := scaled_cap_coordinate_bounds F hI (show (0 : ℝ) ≤ 5 by norm_num) hδ hE
    hSmall hw hx hSupp.1 hCone
  have hBack : parabolicRescale δ (F.toFrequency.symm x) = u := by
    change parabolicRescale δ (F.toFrequency.symm (capFrequencyEquiv F hδ.ne' p)) = u
    rw [capFrequencyEquiv_apply]
    exact chartScaledFrequency_rescale F hδ.ne' u
  dsimp only at h
  rw [hBack] at h
  have hZ : Z ≤ M := (le_max_left Z T).trans (le_max_right _ _)
  have hT : T ≤ M := (le_max_right Z T).trans (le_max_right _ _)
  have hCoord : ‖u‖ ≤ M * |u.1| := by
    rw [Prod.norm_def, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 (max Z T)) (abs_nonneg u.1))
      (max_le
        (h.2.2.2.trans (mul_le_mul_of_nonneg_right hT (abs_nonneg u.1)))
        (h.2.2.1.trans (mul_le_mul_of_nonneg_right hZ (abs_nonneg u.1))))
  have hS : |u.1| ≤ ‖u‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact le_max_left _ _
  have hpNorm : ‖p‖ ≤ D*‖u‖ := calc
    ‖p‖ = ‖frequencyCoordinates.symm u‖ := by simp only [u, frequencyCoordinates.symm_apply_apply]
    _ ≤ ‖frequencyCoordinates.symm.toContinuousLinearMap‖*‖u‖ :=
      frequencyCoordinates.symm.toContinuousLinearMap.le_opNorm u
    _ ≤ D*‖u‖ := mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith) (norm_nonneg _)
  constructor
  · change (D*(M*B))⁻¹ * ‖p‖ ≤ ‖x‖
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ hDen).2
    calc
      _ ≤ D*‖u‖ := hpNorm
      _ ≤ D*(M*|u.1|) := mul_le_mul_of_nonneg_left hCoord hD.le
      _ ≤ D*(M*(B*‖x‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h.2.1 hM.le) hD.le
      _ = _ := by ring
  · change ‖x‖ ≤ U*‖p‖
    calc
      _ ≤ 2*|u.1| := h.1
      _ ≤ 2*‖u‖ := mul_le_mul_of_nonneg_left hS (by norm_num)
      _ ≤ 2*(‖frequencyCoordinates.toContinuousLinearMap‖*‖p‖) :=
        mul_le_mul_of_nonneg_left (frequencyCoordinates.toContinuousLinearMap.le_opNorm p) (by norm_num)
      _ ≤ U*‖p‖ := by
        dsimp only [U]
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

theorem physical_ratio_compare_of_uniform_norms (A : Space ≃L[ℝ] Space)
    {L U : ℝ} (hL : 0 < L) (hU : 0 < U) {p q : Space} (hq : 0 < ‖q‖)
    (hpComp : L*‖p‖ ≤ ‖A p‖ ∧ ‖A p‖ ≤ U*‖p‖)
    (hqComp : L*‖q‖ ≤ ‖A q‖ ∧ ‖A q‖ ≤ U*‖q‖) :
    (L/U)*(‖p‖/‖q‖) ≤ ‖A p‖/‖A q‖ ∧ ‖A p‖/‖A q‖ ≤ (U/L)*(‖p‖/‖q‖) := by
  have hAq : 0 < ‖A q‖ := (mul_pos hL hq).trans_le hqComp.1
  constructor
  · calc
      _ = (L*‖p‖)/(U*‖q‖) := by rw [div_mul_div_comm]
      _ ≤ _ := div_le_div₀ (norm_nonneg _) hpComp.1 hAq hqComp.2
  · calc
      _ ≤ (U*‖p‖)/(L*‖q‖) :=
        div_le_div₀ (mul_nonneg hU.le (norm_nonneg _)) hpComp.2 (mul_pos hL hq) hqComp.1
      _ = _ := by rw [div_mul_div_comm]

/-- The exact original low/high radial factor in the transformed variables. -/
theorem physical_ratio_scaled (A : Space ≃L[ℝ] Space) {r : ℝ} (hr : 0 < r)
    (s : ℕ) (p q : Space) (hq : q ≠ 0) :
    ‖A ((r/(2 : ℝ)^s) • p)‖ / ‖A (r • q)‖ =
      (1/(2 : ℝ)^s)*(‖A p‖/‖A q‖) := by
  have hAq : ‖A q‖ ≠ 0 := by
    intro hn
    apply hq
    exact A.injective ((norm_eq_zero.mp hn).trans (map_zero A).symm)
  rw [map_smul, map_smul, norm_smul, norm_smul,
    Real.norm_of_nonneg (div_nonneg hr.le (by positivity)), Real.norm_of_nonneg hr.le]
  field_simp [hr.ne', hAq]

private theorem ratioCutoffCorrection_bounds {χ : ℝ → ℝ} {a b ℓ u r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hOne : ∀ t, 0 ≤ t → t ≤ ℓ → χ t = 1) (hZero : ∀ t, u ≤ t → χ t = 0)
    (C : ℕ) (hgap : 4*b/(2 : ℝ)^C ≤ ℓ) {p q : Space} {ρ : ℝ}
    (hq : r/2 ≤ ‖q‖ ∧ ‖q‖ ≤ 2*r)
    (hlo : a*(‖p‖/‖q‖) ≤ ρ) (hhi : ρ ≤ b*(‖p‖/‖q‖)) :
    (radialLowCutoff (r/(2 : ℝ)^C) p ≠ 0 → χ ρ = 1) ∧
    (‖p‖ ≤ r/(2 : ℝ)^C → χ ρ = 1 ∧ radialLowCutoff (r/(2 : ℝ)^C) p = 1) ∧
    (χ ρ - radialLowCutoff (r/(2 : ℝ)^C) p ≠ 0 →
      a/(2*(2 : ℝ)^C) < ρ ∧ ρ < u ∧
        r/(2 : ℝ)^C < ‖p‖ ∧ ‖p‖ < (2*u/a)*r) := by
  let P := (2 : ℝ)^C
  have hP : 0 < P := by dsimp only [P]; positivity
  have hscale : 0 < r/P := div_pos hr hP
  have hq0 : 0 < ‖q‖ := (by positivity : 0 < r/2).trans_le hq.1
  have hrho0 : 0 ≤ ρ := (mul_nonneg ha.le (div_nonneg (norm_nonneg _) hq0.le)).trans hlo
  have lowFlat (hn : radialLowCutoff (r/P) p ≠ 0) : χ ρ = 1 := by
    have hp : ‖p‖ ≤ 2*(r/P) := le_of_lt (lt_of_not_ge
      (fun h => hn (radialLowCutoff_eq_zero hscale h)))
    have hquotient : ‖p‖/‖q‖ ≤ 4/P := by
      apply (div_le_iff₀ hq0).2
      calc
        _ ≤ 2*(r/P) := hp
        _ = (4/P)*(r/2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hq.1 (by positivity)
    apply hOne ρ hrho0
    calc
      _ ≤ b*(‖p‖/‖q‖) := hhi
      _ ≤ b*(4/P) := mul_le_mul_of_nonneg_left hquotient hb.le
      _ = 4*b/P := by ring
      _ ≤ ℓ := hgap
  have bothFlat (hp : ‖p‖ ≤ r/P) : χ ρ = 1 ∧ radialLowCutoff (r/P) p = 1 := by
    have hone := radialLowCutoff_eq_one hscale hp
    exact ⟨lowFlat (by rw [hone]; norm_num), hone⟩
  refine ⟨lowFlat, bothFlat, ?_⟩
  intro hd
  change χ ρ - radialLowCutoff (r/P) p ≠ 0 at hd
  have hpL : r/P < ‖p‖ := by
    by_contra! hh
    obtain ⟨hi, hj⟩ := bothFlat hh
    rw [hi, hj, sub_self] at hd
    exact hd rfl
  have hrhoU : ρ < u := by
    by_contra! hh
    by_cases hz : radialLowCutoff (r/P) p = 0
    · rw [hZero ρ hh, hz, sub_self] at hd
      exact hd rfl
    · have eq := (lowFlat hz).symm.trans (hZero ρ hh)
      exact one_ne_zero eq
  have hqL : 1/(2*P) < ‖p‖/‖q‖ := by
    apply (lt_div_iff₀ hq0).2
    calc
      _ ≤ (1/(2*P))*(2*r) := mul_le_mul_of_nonneg_left hq.2 (by positivity)
      _ = r/P := by field_simp
      _ < _ := hpL
  have hrhoL : a/(2*P) < ρ := by
    simpa only [mul_one_div] using (mul_lt_mul_of_pos_left hqL ha).trans_le hlo
  have hqU : ‖p‖/‖q‖ < u/a := by
    apply (lt_div_iff₀ ha).2
    rw [mul_comm]
    exact hlo.trans_lt hrhoU
  have hu : 0 < u := hrho0.trans_lt hrhoU
  refine ⟨hrhoL, hrhoU, hpL, ?_⟩
  calc
    _ < (u/a)*‖q‖ := (div_lt_iff₀ hq0).1 hqU
    _ ≤ (u/a)*(2*r) := mul_le_mul_of_nonneg_left hq.2 (div_nonneg hu.le ha.le)
    _ = _ := by ring

private theorem relative_shift_in_interval {r M : ℝ} (hr : 0 < r)
    {C H : ℕ} (hH : 2*M < (2 : ℝ)^H) {p : Space}
    (hpL : r/(2 : ℝ)^C < ‖p‖) (hpU : ‖p‖ < M*r) {k : ℤ}
    (hk : radialAnnularCutoff ((2 : ℝ)^k*r) p ≠ 0) :
    k ∈ Finset.Icc (-((C : ℤ) + 1)) (H : ℤ) := by
  have hp := radialAnnularCutoff_nonzero (by positivity) hk
  have hlo : (2 : ℝ)^(-((C : ℤ)+1)) < (2 : ℝ)^k := by
    rw [zpow_neg, show (C : ℤ)+1 = ((C+1 : ℕ) : ℤ) by norm_cast, zpow_natCast,
      pow_succ', ← one_div]
    apply (mul_lt_mul_iff_right₀ (by positivity : 0 < 2*r)).1
    calc
      _ = r/(2 : ℝ)^C := by field_simp
      _ < ‖p‖ := hpL
      _ < _ := hp.2.trans_eq (by ring)
  have hhi : (2 : ℝ)^k < (2 : ℝ)^(H : ℤ) := by
    rw [zpow_natCast]
    apply lt_trans _ hH
    apply (mul_lt_mul_iff_right₀ (by positivity : 0 < r/2)).1
    calc
      _ = ((2 : ℝ)^k*r)/2 := by ring
      _ < ‖p‖ := hp.1
      _ < M*r := hpU
      _ = _ := by ring
  exact Finset.mem_Icc.2
    ⟨(zpow_lt_zpow_iff_right₀ (by norm_num) |>.mp hlo).le,
      (zpow_lt_zpow_iff_right₀ (by norm_num) |>.mp hhi).le⟩

/-- The correction has fixed physical ratio bounds, and its low radial
annuli use a single finite interval of shifts at every high scale. -/
theorem exists_radialRatioCorrection_finiteShifts {χ : ℝ → ℝ} {a b ℓ u : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hℓ : 0 < ℓ)
    (hOne : ∀ t, 0 ≤ t → t ≤ ℓ → χ t = 1) (hZero : ∀ t, u ≤ t → χ t = 0) :
    ∃ C H : ℕ, 3 ≤ C ∧ 4*b/(2 : ℝ)^C ≤ ℓ ∧
      ∀ (r : ℝ), 0 < r → ∀ (p q : Space) (ρ : ℝ), r/2 ≤ ‖q‖ ∧ ‖q‖ ≤ 2*r →
        a*(‖p‖/‖q‖) ≤ ρ → ρ ≤ b*(‖p‖/‖q‖) →
        (radialLowCutoff (r/(2 : ℝ)^C) p ≠ 0 → χ ρ = 1) ∧
        (‖p‖ ≤ r/(2 : ℝ)^C → χ ρ = 1 ∧ radialLowCutoff (r/(2 : ℝ)^C) p = 1) ∧
        (χ ρ - radialLowCutoff (r/(2 : ℝ)^C) p ≠ 0 →
          a/(2*(2 : ℝ)^C) < ρ ∧ ρ < u ∧
          ∀ k : ℤ, radialAnnularCutoff ((2 : ℝ)^k*r) p ≠ 0 →
            k ∈ Finset.Icc (-((C : ℤ)+1)) (H : ℤ)) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (4*b/ℓ) (show (1 : ℝ) < 2 by norm_num)
  let C := max 3 n
  have h2C : 0 < (2 : ℝ)^C := by positivity
  have hC : 4*b/(2 : ℝ)^C ≤ ℓ := by
    apply (div_le_iff₀ h2C).2
    have hn' := hn.le.trans (pow_le_pow_right₀ (by norm_num) (le_max_right 3 n))
    simpa only [mul_comm] using (div_le_iff₀ hℓ).1 hn'
  obtain ⟨H,hH⟩ := pow_unbounded_of_one_lt (2*(2*u/a)) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨C,H,le_max_left _ _,hC,?_⟩
  intro r hr p q ρ hq hlo hhi
  obtain ⟨hflat,hboth,hcorr⟩ := ratioCutoffCorrection_bounds ha hb hr hOne hZero C hC hq hlo hhi
  refine ⟨hflat,hboth,?_⟩
  intro hd
  obtain ⟨hL,hU,hpL,hpU⟩ := hcorr hd
  exact ⟨hL,hU,fun _ hk => relative_shift_in_interval hr hH hpL hpU hk⟩

end Burnett.Analysis.CapFourier
