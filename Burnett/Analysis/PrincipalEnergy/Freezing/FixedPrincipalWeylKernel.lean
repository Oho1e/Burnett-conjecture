import Burnett.Analysis.PrincipalEnergy.Freezing.CompactWeylOrderOneLimit

set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal Topology

/-- The genuine compact-base real Weyl principal action with one fixed
infrared cutoff. Each coefficient is that of the unchanged homogeneous
symbol, regularized by the same fixed frequency profile. -/
def compactBaseFixedInfraredWeyl (P : ℝ) (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hS : tsupport ρ ⊆ ball (0 : E) P) (cut : SchwartzMap E ℂ) (a : E → E → ℝ)
    (u : SchwartzMap E ℂ) (x : E) : ℂ :=
  ∑' i : (Index → ℤ) × Fin 2,
    separatedRadianQuantization (1/2) (fixedInfraredSymbol cut 0 (compactBaseRealMode P a i.1 i.2))
      (compactBaseSpatialMode P ρ hρ hS i.1 i.2) u x

/-- The actual compact-base regularized principal Weyl action is the
limit of the literal midpoint integral of its whole regularized symbol. -/
theorem compact_base_fixed_infrared_weyl_is_midpoint_limit
    (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (a : E → E → ℝ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderOneBudget a M)
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (plateau : ∀ᶠ ζ in 𝓝 (0 : E), fixedRadianProfile cut ζ = 1)
    (u : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun n => radianMidpointTruncation (fun y ξ => (fixedInfraredSymbol cut 0 (a y) ξ : ℂ)) n u x)
      atTop (𝓝 (compactBaseFixedInfraredWeyl P ρ hρ hS cut a u x)) := by
  let I := (Index → ℤ) × Fin 2
  let f (i : I) := compactBaseSpatialMode P ρ hρ hS i.1 i.2
  let b (i : I) := compactBaseRealMode P a i.1 i.2
  let v (i : I) := fixedInfraredSymbol cut 0 (b i)
  let C := max 1 ((3 / spatialModeRate P)^8) * M
  let D (i : I) := C / spatialLatticeWeight i.1 ^ 8
  have C0 : 0 ≤ C := mul_nonneg (zero_le_one.trans (le_max_left _ _)) M0
  obtain ⟨DS,B,rec⟩ := compact_base_order_one_series_data P R hP hRP ρ hρ hS ρone a support ha hom M M0 hM
  have D0 (i : I) : 0 ≤ D i := (B i).1
  have vS (i : I) : ContDiff ℝ ∞ (v i) :=
    fixedInfraredSymbol_smooth cut 0 (b i) (B i).2.1 plateau
  let K := 1 + (SchwartzMap.seminorm ℝ 0 0) cut
  let A (i : I) := K * D i
  have K0 : 0 ≤ K := add_nonneg zero_le_one (apply_nonneg _ _)
  have A0 (i : I) : 0 ≤ A i := mul_nonneg K0 (D0 i)
  have AS : Summable A := DS.mul_left K
  have grow (i : I) (ξ : E) : ‖v i ξ‖ ≤ A i * (1+‖ξ‖) := by
    have k : ‖1 - fixedRadianProfile cut ξ‖ ≤ K := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]
      exact add_le_add_left (fixed_radian_profile_norm_bound cut hcut ξ) 1
    change ‖fixedInfraredSymbol cut 0 (b i) ξ‖ ≤ _
    simp only [fixedInfraredSymbol, fixedRadianProfile, SchwartzMap.zero_apply, Complex.zero_re, add_zero, norm_mul]
    have o : ‖b i ξ‖ ≤ D i * (1+‖ξ‖) :=
      ((B i).2.2.2.2 ξ).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (D0 i))
    exact (mul_le_mul k o (norm_nonneg _) K0).trans_eq (by dsimp only [A]; ring)
  have H (r : ℕ) (hr : r ≤ 2) : Summable (fun i : I => D i * patchFourierMoment r (f i)) := by
    obtain ⟨C',_,same⟩ := exists_summable_localized_mode_fourier_moments 8 r (by decide) hr P hP ρ hρ hS
    have bd (k : Index → ℤ) (j : Fin 2) : 0 ≤ D (k,j) ∧ D (k,j) ≤ C * 1 / spatialLatticeWeight k ^ 8 :=
      ⟨D0 (k,j),by simp [D]⟩
    obtain ⟨h,_⟩ := same 0 1 zero_lt_one C C0 (fun k j => D (k,j)) bd
    apply (summable_prod_of_nonneg (fun i : I => mul_nonneg (D0 i) (patch_moment_nonneg _ _))).mpr
    exact ⟨fun _ => (hasSum_fintype _).summable, by simpa only [tsum_fintype, f, compactBaseSpatialMode] using h⟩
  have sum : Summable (fun i : I => A i * (patchFourierMoment 0 (f i) + patchFourierMoment 1 (f i))) := by
    have s := ((H 0 (by decide)).add (H 1 (by decide))).mul_left K
    convert s using 1
    funext i
    dsimp only [A, Pi.add_apply]
    ring
  have expand (y ξ : E) (_ : ξ ≠ 0) : HasSum (fun i => f i y * (v i ξ : ℂ))
      (fixedInfraredSymbol cut 0 (a y) ξ : ℂ) := by
    have s := (rec y ξ).mul_left ((1 - fixedRadianProfile cut ξ : ℝ) : ℂ)
    have same (q : E → ℝ) : (fixedInfraredSymbol cut 0 q ξ : ℂ) =
        ((1 - fixedRadianProfile cut ξ : ℝ) : ℂ) * (q ξ : ℂ) := by
      simp only [fixedInfraredSymbol, fixedRadianProfile, SchwartzMap.zero_apply,
        Complex.zero_re, add_zero, Complex.ofReal_mul]
    rw [← same (a y)] at s
    apply HasSum.congr_fun s
    intro i
    rw [same (b i)]
    ring
  obtain ⟨U,U0,hU⟩ := compact_base_spatial_mode_uniform_bound P ρ hρ hS
  exact radian_midpoint_linear_growth_mode_limit _ f v vS A A0 AS sum grow U U0 (fun i => hU i.1 i.2)
    expand u x

end Burnett.A03
