import Burnett.Analysis.PrincipalEnergy.Freezing.CompactWeylPrincipalComparison

set_option autoImplicit false
set_option maxHeartbeats 4900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal Topology

/-- The literal difference of the fixed-infrared and homogeneous left
symbols has a finite order-zero W¹,³ action. This estimate also treats
the nonsmooth angular homogeneous symbol at zero frequency. -/
theorem exists_compact_fixed_infrared_left_principal_gap_W13
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
    ∃ A : ℝ≥0∞, A < ⊤ ∧ SchwartzOrderZeroJetBound (radianLeftQuantization (fun x ξ =>
      ((fixedInfraredSymbol cut 0 (a x) ξ - a x ξ : ℝ) : ℂ))) A A := by
  let I := (Index → ℤ) × Fin 2
  let f (i : I) := compactBaseSpatialMode P ρ hρ hS i.1 i.2
  let b (i : I) := compactBaseRealMode P a i.1 i.2
  let C := max 1 ((3 / spatialModeRate P)^8) * M
  let D (i : I) := C / spatialLatticeWeight i.1 ^ 8
  let r (b : E → ℝ) (ξ : E) := fixedInfraredSymbol cut 0 b ξ - b ξ
  let G (i : I) (q : E × E) := r (b i) q.2
  have C0 : 0 ≤ C := mul_nonneg (zero_le_one.trans (le_max_left _ _)) M0
  obtain ⟨DS,J,rec⟩ := compact_base_order_one_series_data P R hP hRP ρ hρ hS ρone a support ha hom M M0 hM
  have D0 (i : I) : 0 ≤ D i := (J i).1
  have H (m : ℕ) (hm : m ≤ 2) : Summable (fun i : I => D i * patchFourierMoment m (f i)) := by
    obtain ⟨_,_,same⟩ := exists_summable_localized_mode_fourier_moments 8 m (by decide) hm P hP ρ hρ hS
    have bd (k : Index → ℤ) (j : Fin 2) : 0 ≤ D (k,j) ∧ D (k,j) ≤ C * 1 / spatialLatticeWeight k ^ 8 :=
      ⟨D0 (k,j),by simp [D]⟩
    obtain ⟨s,_⟩ := same 0 1 zero_lt_one C C0 (fun k j => D (k,j)) bd
    apply (summable_prod_of_nonneg (fun i : I => mul_nonneg (D0 i) (patch_moment_nonneg _ _))).mpr
    exact ⟨fun _ => (hasSum_fintype _).summable,by simpa only [tsum_fintype,f,compactBaseSpatialMode] using s⟩
  obtain ⟨L,L0,e⟩ := exists_regularized_principal_gap_frequency_bound cut hcut plateau
  have z (i : I) (ξ : E) : regularizedPrincipalGapSymbol cut (b i) (0,ξ) = r (b i) ξ := by
    simp [regularizedPrincipalGapSymbol,slantedRadianSymbol,r]
  have test (i : I) := e (b i) (J i).2.1 (J i).2.2.1 (D i) (D0 i) (J i).2.2.2.1
  have rm (i : I) : Measurable (r (b i)) := by
    have f : Continuous (fun ξ : E => ((0 : E),ξ)) := continuous_const.prodMk continuous_id
    have h := (test i).1.comp f.measurable
    have eq : ((regularizedPrincipalGapSymbol cut (b i)) ∘ (fun ξ : E => ((0 : E),ξ))) = r (b i) :=
      funext (z i)
    rw [eq] at h
    exact h
  have rb (i : I) (ξ : E) : ‖r (b i) ξ‖ ≤ L * D i := by
    simpa only [z i,norm_zero,add_zero,mul_one] using (test i).2.1 0 ξ
  have gb (i : I) (η ξ : E) : ‖G i (η,ξ)‖ ≤ (L*D i)*(1+‖η‖) :=
    (rb i ξ).trans (le_mul_of_one_le_right (mul_nonneg L0 (D0 i))
      (le_add_of_nonneg_right (norm_nonneg _)))
  have sections (i : I) (η : E) (u : SchwartzMap E ℂ) :
      let v := radianAction (fun ξ => G i (η,ξ)) u
      MemLp v (ENNReal.ofReal 3) volume ∧
        eLpNorm v (ENNReal.ofReal 3) volume ≤
        ENNReal.ofReal ((L*D i)*(1+‖η‖)) * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume := by
    have h := (test i).2.2 0 u
    simp only [z i,norm_zero,add_zero,mul_one] at h
    refine ⟨h.1,h.2.trans ?_⟩
    apply mul_le_mul_right'
    exact ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right (mul_nonneg L0 (D0 i))
      (le_add_of_nonneg_right (norm_nonneg _)))
  have mo (m : ℕ) (hm : m ≤ 2) : Summable (fun i : I => (L*D i)*patchFourierMoment m (f i)) := by
    simpa only [mul_assoc] using (H m hm).mul_left L
  obtain ⟨A,Afin,bound⟩ := exists_weighted_radian_order_zero_mode_sum_W13 f G
    (fun i => (rm i).comp measurable_snd) (fun i => L*D i) (fun i => mul_nonneg L0 (D0 i))
    gb sections mo
  have rEq (v : E → ℝ) (ξ : E) : r v ξ = -(fixedRadianProfile cut ξ) * v ξ := by
    simp only [r,fixedInfraredSymbol,fixedRadianProfile,SchwartzMap.zero_apply,Complex.zero_re,add_zero]
    ring
  have actual (x ξ : E) : HasSum (fun i => f i x * (r (b i) ξ : ℂ)) (r (a x) ξ : ℂ) := by
    have h := (rec x ξ).mul_left ((-(fixedRadianProfile cut ξ) : ℝ) : ℂ)
    rw [rEq (a x),Complex.ofReal_mul]
    apply h.congr_fun
    intro i
    rw [rEq (b i),Complex.ofReal_mul]
    ring
  obtain ⟨U,U0,hU⟩ := compact_base_spatial_mode_uniform_bound P ρ hρ hS
  have eq : radianLeftQuantization (fun x ξ => (r (a x) ξ : ℂ)) =
      (fun u x => ∑' i, radianFourierAverage (G i) (f i) u x) := by
    funext u x
    rw [radian_left_quantization_separated_sum _ f (fun i => r (b i)) rm (fun i => L*D i)
      (fun i => mul_nonneg L0 (D0 i)) (DS.mul_left L)
      (fun i ξ => (rb i ξ).trans (le_mul_of_one_le_right (mul_nonneg L0 (D0 i))
        (le_add_of_nonneg_right (norm_nonneg _))))
      U U0 (fun i => hU i.1 i.2) (fun y ξ _ => actual y ξ) u x]
    apply tsum_congr
    intro i
    have h : slantedRadianSymbol 0 (r (b i)) = G i := by
      funext q
      rcases q with ⟨η,ξ⟩
      simp [slantedRadianSymbol,G]
    rw [separatedRadianQuantization,h]
  rw [eq]
  exact ⟨A,Afin,bound⟩

end Burnett.A03
