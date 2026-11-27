import Burnett.Analysis.PrincipalEnergy.Freezing.RegularizedPrincipalGapSymbol
import Burnett.Analysis.PrincipalEnergy.Freezing.AffineOriginalTestComparison

set_option autoImplicit false
set_option maxHeartbeats 4200000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal Topology

/-- Actual compact-base regularized Weyl principal minus actual left
homogeneous principal, with an order-zero estimate for the entire sum. -/
theorem exists_compact_fixed_principal_weyl_left_gap_W13
    (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (a : E → E → ℝ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderOneBudget a M)
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (plateau : ∀ᶠ ζ in 𝓝 (0 : E), fixedRadianProfile cut ζ = 1) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧
      SchwartzOrderZeroJetBound (fun u => compactBaseFixedInfraredWeyl P ρ hρ hS cut a u -
        radianLeftQuantization (fun x ξ => (a x ξ : ℂ)) u) K K := by
  let I := (Index → ℤ) × Fin 2
  let f (i : I) := compactBaseSpatialMode P ρ hρ hS i.1 i.2
  let b (i : I) := compactBaseRealMode P a i.1 i.2
  let v (i : I) := fixedInfraredSymbol cut 0 (b i)
  let C := max 1 ((3 / spatialModeRate P)^8) * M
  let D (i : I) := C / spatialLatticeWeight i.1 ^ 8
  have C0 : 0 ≤ C := mul_nonneg (zero_le_one.trans (le_max_left _ _)) M0
  obtain ⟨DS,J,rec⟩ := compact_base_order_one_series_data P R hP hRP ρ hρ hS ρone a support ha hom M M0 hM
  have D0 (i : I) : 0 ≤ D i := (J i).1
  have bSm (i : I) : ContDiffOn ℝ ∞ (b i) {ξ | ξ ≠ 0} := (J i).2.1
  have bMeas (i : I) : Measurable (b i) :=
    measurable_of_continuousOn_compl_singleton 0 (bSm i).continuousOn
  have vSm (i : I) : ContDiff ℝ ∞ (v i) :=
    fixedInfraredSymbol_smooth cut 0 (b i) (bSm i) plateau
  let L := 1 + (SchwartzMap.seminorm ℝ 0 0) cut
  have L0 : 0 ≤ L := add_nonneg zero_le_one (apply_nonneg _ _)
  have bGrow (i : I) (ξ : E) : ‖b i ξ‖ ≤ D i * (1+‖ξ‖) :=
    ((J i).2.2.2.2 ξ).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (D0 i))
  have vGrow (i : I) (ξ : E) : ‖v i ξ‖ ≤ (L*D i)*(1+‖ξ‖) := by
    have k : ‖1-fixedRadianProfile cut ξ‖ ≤ L := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]
      exact add_le_add_left (fixed_radian_profile_norm_bound cut hcut ξ) 1
    change ‖fixedInfraredSymbol cut 0 (b i) ξ‖ ≤ _
    simp only [fixedInfraredSymbol, fixedRadianProfile, SchwartzMap.zero_apply, Complex.zero_re, add_zero, norm_mul]
    exact (mul_le_mul k (bGrow i ξ) (norm_nonneg _) L0).trans_eq (by ring)
  have H (r : ℕ) (hr : r ≤ 2) : Summable (fun i : I => D i * patchFourierMoment r (f i)) := by
    obtain ⟨C',_,same⟩ := exists_summable_localized_mode_fourier_moments 8 r (by decide) hr P hP ρ hρ hS
    have bd (k : Index → ℤ) (j : Fin 2) : 0 ≤ D (k,j) ∧ D (k,j) ≤ C * 1 / spatialLatticeWeight k ^ 8 :=
      ⟨D0 (k,j),by simp [D]⟩
    obtain ⟨h,_⟩ := same 0 1 zero_lt_one C C0 (fun k j => D (k,j)) bd
    apply (summable_prod_of_nonneg (fun i : I => mul_nonneg (D0 i) (patch_moment_nonneg _ _))).mpr
    exact ⟨fun _ => (hasSum_fintype _).summable,by simpa only [tsum_fintype, f, compactBaseSpatialMode] using h⟩
  obtain ⟨K,K0,B⟩ := exists_regularized_principal_gap_frequency_bound cut hcut plateau
  let G (i : I) := regularizedPrincipalGapSymbol cut (b i)
  have budget (i : I) := B (b i) (bSm i) (J i).2.2.1 (D i) (D0 i) (J i).2.2.2.1
  have moment (r : ℕ) (hr : r ≤ 2) : Summable (fun i : I => (K * D i) * patchFourierMoment r (f i)) := by
    have h := (H r hr).mul_left K
    simpa only [mul_assoc] using h
  obtain ⟨A,Afin,whole⟩ := exists_weighted_radian_order_zero_mode_sum_W13 f G (fun i => (budget i).1)
    (fun i => K*D i) (fun i => mul_nonneg K0 (D0 i)) (fun i => (budget i).2.1) (fun i => (budget i).2.2) moment
  refine ⟨A,Afin,?_⟩
  obtain ⟨U,U0,hU⟩ := compact_base_spatial_mode_uniform_bound P ρ hρ hS
  have pSum : Summable (fun i : I => D i * radianFirstFourierMass (f i)) := by
    simpa only [radianFirstFourierMass, mul_add, Pi.add_apply]
      using (H 0 (by decide)).add (H 1 (by decide))
  have abs (σ T : ℝ) (T0 : 0 ≤ T) (g : I → E → ℝ) (gm : ∀ i, Measurable (g i))
      (size : ∀ i ξ, ‖g i ξ‖ ≤ (T*D i)*(1+‖ξ‖)) (u : SchwartzMap E ℂ) (x : E) :
      Summable (fun i : I => separatedRadianQuantization σ (g i) (f i) u x) := by
    apply Summable.of_norm_bounded
      ((pSum.mul_left (T*(1+tau+tau*‖σ‖))).mul_right (radianFirstFourierMass u))
    intro i
    refine (slanted_radian_linear_growth_mass σ _ (gm i) _ (mul_nonneg T0 (D0 i)) (size i) (f i) u x).trans_eq ?_
    ring
  have eq : (fun u x => ∑' i, radianFourierAverage (G i) (f i) u x) =
      fun u => compactBaseFixedInfraredWeyl P ρ hρ hS cut a u -
        radianLeftQuantization (fun x ξ => (a x ξ : ℂ)) u := by
    funext u x
    have bs := abs 0 1 zero_le_one b bMeas (fun i ξ => by simpa only [one_mul] using bGrow i ξ) u x
    have vs := abs (1/2) L L0 v (fun i => (vSm i).continuous.measurable) vGrow u x
    have left := radian_left_quantization_separated_sum (fun x ξ => (a x ξ : ℂ)) f b bMeas D D0 DS bGrow
      U U0 (fun i => hU i.1 i.2) (fun x ξ _ => rec x ξ) u x
    change (∑' i, radianFourierAverage (G i) (f i) u x) =
      (∑' i, separatedRadianQuantization (1/2) (v i) (f i) u x) -
        radianLeftQuantization (fun x ξ => (a x ξ : ℂ)) u x
    rw [left, ← vs.tsum_sub bs]
    apply tsum_congr
    intro i
    have vmeas := (vSm i).continuous.measurable
    have a1 := slanted_radian_symbol_measurable (1/2) (v i) vmeas
    have a0 := slanted_radian_symbol_measurable 0 (b i) (bMeas i)
    have g1 := slanted_radian_symbol_growth (1/2) (v i) (L*D i) (mul_nonneg L0 (D0 i)) (vGrow i)
    have g0 := slanted_radian_symbol_growth 0 (b i) (D i) (D0 i) (bGrow i)
    exact congrFun (radian_fourier_average_sub _ _ a1 a0 g1 g0 (f i) u) x
  rw [← eq]
  exact whole

end Burnett.A03
