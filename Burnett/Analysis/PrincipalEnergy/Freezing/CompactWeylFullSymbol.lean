import Burnett.Analysis.PrincipalEnergy.Freezing.CompactOrderZeroLeft

set_option autoImplicit false
set_option maxHeartbeats 6800000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal ContDiff FourierTransform Topology

theorem tendsto_countable_mode_sum {ι : Type} [Countable ι]
    (F : ℕ → ι → ℂ) (G : ι → ℂ) (w : ι → ℝ) (hw : Summable w)
    (h0 : ∀ i, 0 ≤ w i) (hF : ∀ n i, ‖F n i‖ ≤ w i)
    (hcv : ∀ i, Tendsto (fun n => F n i) atTop (𝓝 (G i))) :
    Tendsto (fun n => ∑' i, F n i) atTop (𝓝 (∑' i, G i)) := by
  letI : MeasurableSpace ι := ⊤
  letI : MeasurableSingletonClass ι := ⟨fun i => trivial⟩
  let μ : Measure ι := Measure.count
  have wI : Integrable w μ := integrable_count_iff.mpr (by simpa [Real.norm_of_nonneg (h0 _)] using hw)
  have Fint (n : ℕ) : Integrable (F n) μ := integrable_count_iff.mpr
    (Summable.of_nonneg_of_le (fun i => norm_nonneg _) (hF n) hw)
  have Gbound (i : ι) : ‖G i‖ ≤ w i :=
    le_of_tendsto (tendsto_norm.comp (hcv i)) (Eventually.of_forall fun n => hF n i)
  have Gint : Integrable G μ := integrable_count_iff.mpr
    (Summable.of_nonneg_of_le (fun i => norm_nonneg _) Gbound hw)
  have eq (f : ι → ℂ) (hi : Integrable f μ) : (∫ i, f i ∂μ) = ∑' i, f i := by
    rw [integral_countable' hi]
    simp only [μ, measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  have d := tendsto_integral_of_dominated_convergence w (fun n => (Fint n).1) wI
    (fun n => Eventually.of_forall (hF n)) (Eventually.of_forall hcv)
  simpa only [eq (F _) (Fint _), eq G Gint] using d

/-- The actual complete midpoint kernel at the same explicit normalized
frequency truncation as the separated Weyl proof. -/
def radianMidpointTruncation (a : E → E → ℂ) (n : ℕ) (u : SchwartzMap E ℂ) (x : E) : ℂ :=
  ∫ y : E, (∫ ξ : E, patchFourierPhase ξ (x-y) *
    (mikhlinBall (((n : ℝ)+1)⁻¹ • ξ) : ℂ) * a ((1/2 : ℝ) • (x+y)) (tau • ξ)) * u y

private theorem cutoff_profile_at_frequency (b : E → ℝ) (hb : ContDiff ℝ ∞ b) (n : ℕ) (ξ : E) :
    normalizedRadianCutoffProfile b hb n ξ =
      (mikhlinBall (((n : ℝ)+1)⁻¹ • ξ) * b (tau • ξ) : ℝ) := rfl

private theorem inverse_schwartz_phase (f : SchwartzMap E ℂ) (z : E) :
    (SchwartzMap.fourierTransformCLE ℂ).symm f z = ∫ ξ : E, patchFourierPhase ξ z * f ξ := by
  rw [SchwartzMap.fourierTransformCLE_symm_apply, Real.fourierIntegralInv_eq']
  rfl

/-- For every finite frequency cutoff, the literal two-point kernel sums
the actual separated Weyl kernels under an absolute coefficient budget. -/
theorem radian_midpoint_truncation_separated_sum {ι : Type} [Countable ι]
    (a : E → E → ℂ) (f : ι → SchwartzMap E ℂ) (b : ι → E → ℝ)
    (smooth : ∀ i, ContDiff ℝ ∞ (b i)) (D : ι → ℝ) (_D0 : ∀ i, 0 ≤ D i) (hD : Summable D)
    (growth : ∀ i ξ, ‖b i ξ‖ ≤ D i * (1 + ‖ξ‖))
    (U : ℝ) (U0 : 0 ≤ U) (uniform : ∀ i x, ‖f i x‖ ≤ U)
    (reconstruction : ∀ x ξ, ξ ≠ 0 → HasSum (fun i => f i x * (b i ξ : ℂ)) (a x ξ))
    (n : ℕ) (u : SchwartzMap E ℂ) (x : E) :
    radianMidpointTruncation a n u x =
      ∑' i, ∫ y : E,
        (SchwartzMap.fourierTransformCLE ℂ).symm (normalizedRadianCutoffProfile (b i) (smooth i) n) (x-y) *
          f i ((1/2 : ℝ) • (x+y)) * u y := by
  let N := normalizedRadianCutoffProfile (fun _ => 1) contDiff_const n
  let h (ξ : E) := mikhlinBall (((n : ℝ)+1)⁻¹ • ξ)
  let S (ξ : E) := (1 + tau * ‖ξ‖) * ‖N ξ‖
  let m (y : E) := (1/2 : ℝ) • (x+y)
  let T (i : ι) (ξ y : E) := patchFourierPhase ξ (x-y) * (h ξ : ℂ) *
    (f i (m y) * (b i (tau • ξ) : ℂ))
  let K (i : ι) := (SchwartzMap.fourierTransformCLE ℂ).symm (normalizedRadianCutoffProfile (b i) (smooth i) n)
  have τp : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have S0 (ξ : E) : 0 ≤ S ξ := mul_nonneg (by positivity) (norm_nonneg _)
  have SI : Integrable S volume := by
    apply (N.integrable.norm.add ((N.integrable_pow_mul volume 1).const_mul tau)).congr
    filter_upwards with ξ
    change ‖N ξ‖ + tau * (‖ξ‖ ^ 1 * ‖N ξ‖) = S ξ
    rw [pow_one]
    dsimp only [S]
    ring
  have hN (ξ : E) : ‖(h ξ : ℂ)‖ = ‖N ξ‖ := by
    rw [show N ξ = _ from cutoff_profile_at_frequency _ _ _ _, mul_one]
  have innerB (i : ι) (ξ y : E) : ‖T i ξ y‖ ≤ (U * D i) * S ξ := by
    simp only [T, norm_mul, patch_fourier_phase_norm, one_mul, hN, Complex.norm_real, S]
    have r := growth i (tau • ξ)
    rw [norm_smul, Real.norm_of_nonneg τp.le] at r
    calc
      _ ≤ ‖N ξ‖ * (U * (D i * (1 + tau * ‖ξ‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (uniform i _) r (norm_nonneg _) U0) (norm_nonneg _)
      _ = _ := by ring
  have innerI (i : ι) (y : E) : Integrable (fun ξ => T i ξ y) volume := by
    let args (ξ : E) : E × E := (ξ,x-y)
    have argsC : Continuous args := continuous_id.prodMk continuous_const
    have pC : Continuous (fun ξ : E => patchFourierPhase ξ (x-y)) := by
      change Continuous ((fun z : E × E => patchFourierPhase z.1 z.2) ∘ args)
      exact patch_fourier_phase_continuous.comp argsC
    have hC : Continuous (fun ξ : E => (h ξ : ℂ)) := by
      apply Complex.continuous_ofReal.comp
      exact mikhlinBall.continuous.comp (continuous_const.smul continuous_id)
    have bC : Continuous (fun ξ : E => (b i (tau • ξ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((smooth i).continuous.comp (continuous_const.smul continuous_id))
    exact (SI.const_mul (U * D i)).mono'
      ((pC.mul hC).mul (continuous_const.mul bC)).aestronglyMeasurable
      (Eventually.of_forall fun ξ => innerB i ξ y)
  have innerSum (y : E) : Summable (fun i => ∫ ξ, ‖T i ξ y‖) := by
    apply Summable.of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _)) _
      ((hD.mul_left U).mul_right (∫ ξ, S ξ))
    intro i
    exact (integral_mono (innerI i y).norm (SI.const_mul _) (fun ξ => innerB i ξ y)).trans_eq (integral_const_mul _ _)
  have link (i : ι) (y : E) : (∫ ξ, T i ξ y) = K i (x-y) * f i (m y) := by
    rw [show K i (x-y) = _ from inverse_schwartz_phase _ _, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [cutoff_profile_at_frequency, Complex.ofReal_mul]
    dsimp only [T,h]
    ring
  have outer (y : E) : (∫ ξ : E, patchFourierPhase ξ (x-y) * (h ξ : ℂ) *
      a (m y) (tau • ξ)) * u y = ∑' i, K i (x-y) * f i (m y) * u y := by
    calc
      _ = (∑' i, ∫ ξ, T i ξ y) * u y := by
        rw [integral_tsum_of_summable_integral_norm (fun i => innerI i y) (innerSum y)]
        congr 1
        apply integral_congr_ae
        have ae0 : ∀ᵐ ξ : E ∂volume, ξ ≠ 0 := by rw [ae_iff]; simp
        filter_upwards [ae0] with ξ hξ
        have s := (reconstruction (m y) (tau • ξ) (smul_ne_zero τp.ne' hξ)).mul_left
          (patchFourierPhase ξ (x-y) * (h ξ : ℂ))
        exact s.tsum_eq.symm
      _ = _ := by simp only [link, tsum_mul_right]
  let M := U * ∫ ξ, S ξ
  have outerB (i : ι) (y : E) : ‖K i (x-y) * f i (m y) * u y‖ ≤ (D i * M) * ‖u y‖ := by
    rw [← link, norm_mul]
    have hh := norm_integral_le_of_norm_le (SI.const_mul (U * D i)) (Eventually.of_forall fun ξ => innerB i ξ y)
    rw [integral_const_mul] at hh
    exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (by dsimp only [M]; ring)
  have outerI (i : ι) : Integrable (fun y => K i (x-y) * f i (m y) * u y) volume :=
    (u.integrable.norm.const_mul (D i * M)).mono'
      ((((K i).continuous.comp (continuous_const.sub continuous_id)).mul
        ((f i).continuous.comp (continuous_const.smul (continuous_const.add continuous_id)))).mul
          u.continuous).aestronglyMeasurable (Eventually.of_forall (outerB i))
  have outerS : Summable (fun i => ∫ y, ‖K i (x-y) * f i (m y) * u y‖) := by
    apply Summable.of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _)) _
      ((hD.mul_right M).mul_right (∫ y, ‖u y‖))
    intro i
    exact (integral_mono (outerI i).norm (u.integrable.norm.const_mul _) (outerB i)).trans_eq
      (integral_const_mul _ _)
  change (∫ y, _) = ∑' i, ∫ y, K i (x-y) * f i (m y) * u y
  rw [integral_tsum_of_summable_integral_norm outerI outerS]
  exact integral_congr_ae (Eventually.of_forall outer)

/-- The full order-zero test action is the limit of the actual complete
midpoint kernel, with a genuine W¹,³ bound on that same action. -/
theorem exists_compact_base_order_zero_midpoint_limit_W13 (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1) (a : E → E → ℝ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) univ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderZeroBudget a M) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧
      SchwartzOrderZeroJetBound (compactBaseModeQuantization P ρ hρ hS (1/2) a) A A ∧
      ∀ (u : SchwartzMap E ℂ) (x : E),
        Tendsto (fun n => radianMidpointTruncation (fun y ξ => (a y ξ : ℂ)) n u x) atTop
          (𝓝 (compactBaseModeQuantization P ρ hρ hS (1/2) a u x)) := by
  obtain ⟨A,Afin,est⟩ := exists_compact_base_order_zero_mode_action_W13 P R hP hRP.le ρ hρ hS a support ha M M0 hM
  refine ⟨A,Afin,est (1/2),?_⟩
  intro u x
  let I := (Index → ℤ) × Fin 2
  let f (i : I) := compactBaseSpatialMode P ρ hρ hS i.1 i.2
  let b (i : I) := compactBaseRealMode P a i.1 i.2
  let D (i : I) := max 1 ((3 / spatialModeRate P)^8) * M / spatialLatticeWeight i.1 ^ 8
  obtain ⟨DS,B,sum⟩ := compact_base_order_zero_series_data P R hP hRP ρ hρ hS ρone a support ha M M0 hM
  obtain ⟨U,U0,hU⟩ := compact_base_spatial_mode_uniform_bound P ρ hρ hS
  have bSmooth (i : I) : ContDiff ℝ ∞ (b i) := (B i).2.1
  have D0 (i : I) : 0 ≤ D i := (B i).1
  have growth (i : I) (ξ : E) : ‖b i ξ‖ ≤ D i * (1 + ‖ξ‖) :=
    ((B i).2.2 ξ).trans (le_mul_of_one_le_right (D0 i) (le_add_of_nonneg_right (norm_nonneg _)))
  let V (n : ℕ) (i : I) (ξ : E) := fixedRadianProfile (normalizedRadianCutoffProfile (b i) (bSmooth i) n) ξ
  let F (n : ℕ) (i : I) := ∫ y : E,
    ((SchwartzMap.fourierTransformCLE ℂ).symm (normalizedRadianCutoffProfile (b i) (bSmooth i) n)) (x-y) *
      f i ((1/2 : ℝ) • (x+y)) * u y
  let G (i : I) := separatedRadianQuantization (1/2) (b i) (f i) u x
  have eq (n : ℕ) : radianMidpointTruncation (fun y ξ => (a y ξ : ℂ)) n u x = ∑' i, F n i :=
    radian_midpoint_truncation_separated_sum _ f b bSmooth D D0 DS growth U U0 (fun i => hU i.1 i.2)
      sum n u x
  simp_rw [eq]
  have cv (i : I) : Tendsto (fun n => F n i) atTop (𝓝 (G i)) :=
    separated_radian_weyl_is_midpoint_kernel_limit (b i) (bSmooth i) (D i) (D0 i) (growth i) (f i) u x
  have q (n : ℕ) (i : I) : ‖F n i‖ ≤ D i * patchFourierMoment 0 (f i) * patchFourierMoment 0 u := by
    have rr (ξ : E) :
        (((normalizedRadianCutoffProfile (b i) (bSmooth i) n) ξ).re : ℂ) =
          (normalizedRadianCutoffProfile (b i) (bSmooth i) n) ξ := by
      rw [cutoff_profile_at_frequency, Complex.ofReal_re]
    have k := separated_radian_weyl_fixed_profile_kernel _ rr (f i) u x
    change separatedRadianQuantization (1/2) (V n i) (f i) u x = F n i at k
    have B' (ξ : E) : ‖V n i ξ‖ ≤ D i := by
      dsimp only [V]
      rw [normalized_radian_cutoff_apply, norm_mul, Real.norm_of_nonneg mikhlinBall.nonneg]
      exact (mul_le_of_le_one_left (norm_nonneg _) mikhlinBall.le_one).trans ((B i).2.2 ξ)
    rw [← k]
    exact (bounded_separated_radian_action_pointwise (1/2) _ (fixed_radian_profile_measurable _) _ (D0 i) B'
      (f i) u).1 x
  obtain ⟨C,C0,H⟩ := exists_summable_localized_mode_fourier_moments 8 0 (by decide) (by decide) P hP ρ hρ hS
  let D' := max 1 ((3 / spatialModeRate P)^8) * M
  have D'0 : 0 ≤ D' := mul_nonneg (zero_le_one.trans (le_max_left _ _)) M0
  have d (k : Index → ℤ) (j : Fin 2) : 0 ≤ D (k,j) ∧ D (k,j) ≤ D' * 1 / spatialLatticeWeight k ^ 8 :=
    ⟨D0 (k,j), by simp [D,D']⟩
  obtain ⟨Hsum,_⟩ := H 0 1 zero_lt_one D' D'0 (fun k j => D (k,j)) d
  have hs : Summable (fun i : I => D i * patchFourierMoment 0 (f i)) := by
    apply (summable_prod_of_nonneg (fun i : I => mul_nonneg (D0 i) (patch_moment_nonneg _ _))).mpr
    refine ⟨fun _ => hasSum_fintype _ |>.summable, ?_⟩
    simpa only [tsum_fintype, f, compactBaseSpatialMode] using Hsum
  exact tendsto_countable_mode_sum F G _ (hs.mul_right _) (fun i => mul_nonneg (mul_nonneg (D0 i) (patch_moment_nonneg _ _)) (patch_moment_nonneg _ _)) q cv

end Burnett.A03
