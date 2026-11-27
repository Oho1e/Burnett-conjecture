import Burnett.Analysis.PrincipalEnergy.Freezing.CompactOrderOneModes
import Burnett.Analysis.PrincipalEnergy.Freezing.LeftCommutatorModeSum
import Burnett.Analysis.PrincipalEnergy.Freezing.RadianLeftFullSymbol
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedFrozenLeftDefinitions

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal FourierTransform

private theorem linear_growth_radian_multiplier_norm (b : E → ℝ) (D : ℝ)
    (bound : ∀ ξ, ‖b ξ‖ ≤ D * ‖ξ‖) (u : SchwartzMap E ℂ) (x : E) :
    ‖radianAction b u x‖ ≤ (D * tau) * patchFourierMoment 1 u := by
  let F := SchwartzMap.fourierTransformCLM ℂ u
  have τ0 : 0 ≤ tau := by unfold tau; positivity
  let B := D * tau
  have integralEq : B * patchFourierMoment 1 u = ∫ ξ : E, B * (‖ξ‖ * ‖F ξ‖) := by
    rw [integral_const_mul]
    simp only [patchFourierMoment, pow_one, F, SchwartzMap.fourierTransformCLM_apply]
  change ‖radianAction b u x‖ ≤ B * patchFourierMoment 1 u
  rw [radian_action_fourier_integral, integralEq]
  have hInt : Integrable (fun ξ : E => B * (‖ξ‖ * ‖F ξ‖)) volume := by
    simpa only [pow_one] using (F.integrable_pow_mul volume 1).const_mul B
  apply norm_integral_le_of_norm_le hInt
  filter_upwards with ξ
  simp only [norm_mul, patch_fourier_phase_norm, one_mul, Complex.norm_real]
  have h := bound (tau • ξ)
  rw [norm_smul, Real.norm_of_nonneg τ0] at h
  exact (mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans_eq (by simp only [B, F, SchwartzMap.fourierTransformCLM_apply]; ring)

private theorem compact_base_spatial_partial_uniform_bound (P : ℝ) (ρ : E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (S : tsupport ρ ⊆ ball (0 : E) P) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ (k : Index → ℤ) (i : Fin 2) (j : Index) (x : E),
      ‖energyPartial j (compactBaseSpatialMode P ρ hρ S k i) x‖ ≤ U * spatialLatticeWeight k := by
  obtain ⟨C,C0,base⟩ := exists_localized_spatial_mode_profile_jet_bound P
  have comp : HasCompactSupport ρ :=
    (isCompact_closedBall (0 : E) P).of_isClosed_subset isClosed_closure (S.trans ball_subset_closedBall)
  let ρ' := comp.toSchwartzMap hρ
  let B := ∑ m ∈ Finset.range 3, (SchwartzMap.seminorm ℝ 0 m) ρ'
  have B0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => apply_nonneg _ _
  have H (j : ℕ) (hj : j ≤ 2) (x : E) : ‖iteratedFDeriv ℝ j ρ x‖ ≤ B := by
    exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ ρ' j x).trans
      (Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_range.mpr (by omega)))
  refine ⟨C*B,mul_nonneg C0 B0,?_⟩
  intro k i j x
  let f := compactBaseSpatialMode P ρ hρ S k i
  let g := localizedRealSpatialModeProfile P k ρ 0 1 i
  let e : E := EuclideanSpace.single j 1
  have e1 : ‖e‖ = 1 := by simp [e, EuclideanSpace.norm_single]
  have realSmooth : ContDiff ℝ ∞ g := by
    have eq : g = fun x => (f x).re := by
      funext y
      simp only [f, g, compactBaseSpatialMode, localized_real_spatial_mode_schwartz_apply, Complex.ofReal_re]
    rw [eq]
    exact Complex.reCLM.contDiff.comp f.smooth'
  have normEq : ‖iteratedFDeriv ℝ 1 (f : E → ℂ) x‖ = ‖iteratedFDeriv ℝ 1 g x‖ := by
    have eq : (f : E → ℂ) = Complex.ofRealLI ∘ g := rfl
    rw [eq]
    exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left realSmooth.contDiffAt (by exact_mod_cast le_top)
  have dBound : ‖fderiv ℝ (f : E → ℂ) x e‖ ≤ ‖iteratedFDeriv ℝ 1 (f : E → ℂ) x‖ := by
    have H := (iteratedFDeriv ℝ 1 (f : E → ℂ) x).le_opNorm (fun _ : Fin 1 => e)
    simpa only [iteratedFDeriv_one_apply, e1, Finset.prod_const_one, mul_one] using H
  have jBound := base ρ hρ B B0 H k 0 1 zero_lt_one 1 (by decide) x
  change ‖fderiv ℝ (f : E → ℂ) x e‖ ≤ C*B*spatialLatticeWeight k
  apply dBound.trans
  rw [normEq]
  by_cases hi : i = 0
  · simpa only [g, localizedRealSpatialModeProfile, if_pos hi, inv_one, one_pow, pow_one, mul_one] using jBound.1
  · simpa only [g, localizedRealSpatialModeProfile, if_neg hi, inv_one, one_pow, pow_one, mul_one] using jBound.2

/-- Exact series for this actual variable-coefficient left commutator.
The field and its original cutoff are the same on both sides. -/
theorem radian_left_quantization_separated_commutator {ι : Type} [Countable ι]
    (a : E → E → ℝ) (f : ι → SchwartzMap E ℂ) (b : ι → E → ℝ)
    (meas : ∀ i, Measurable (b i)) (D : ι → ℝ) (D0 : ∀ i, 0 ≤ D i) (Ds : Summable D)
    (growth : ∀ i ξ, ‖b i ξ‖ ≤ D i * ‖ξ‖)
    (U : ℝ) (U0 : 0 ≤ U) (fBound : ∀ i x, ‖f i x‖ ≤ U)
    (rec : ∀ x ξ, ξ ≠ 0 → HasSum (fun i => f i x * (b i ξ : ℂ)) (a x ξ : ℂ))
    (θ u : SchwartzMap E ℂ) (x : E) :
    radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) (energyProduct θ u) x -
      θ x * radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) u x =
      ∑' i, f i x * radianCommutator (b i) θ u x := by
  have growth' (i : ι) (ξ : E) : ‖b i ξ‖ ≤ D i * (1 + ‖ξ‖) :=
    (growth i ξ).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (D0 i))
  have s (v : SchwartzMap E ℂ) :
      radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) v x = ∑' i, f i x * radianAction (b i) v x := by
    rw [radian_left_quantization_separated_sum _ f b meas D D0 Ds growth' U U0 fBound rec]
    simp only [separated_radian_quantization_left _ (meas _)
      (slanted_radian_symbol_growth 0 _ _ (D0 _) (growth' _))]
  have sum (v : SchwartzMap E ℂ) : Summable (fun i => f i x * radianAction (b i) v x) := by
    apply Summable.of_norm_bounded (((Ds.mul_right tau).mul_right (patchFourierMoment 1 v)).mul_left U)
    intro i
    rw [norm_mul]
    exact mul_le_mul (fBound i x) (linear_growth_radian_multiplier_norm (b i) (D i) (growth i) v x)
      (norm_nonneg _) U0
  have eq (i : ι) : f i x * radianCommutator (b i) θ u x =
      f i x * radianAction (b i) (energyProduct θ u) x - θ x * (f i x * radianAction (b i) u x) := by
    change f i x * (radianAction (b i) (energyProduct θ u) x - θ x * radianAction (b i) u x) = _
    ring
  simp only [s, eq]
  rw [((sum (energyProduct θ u)).tsum_sub ((sum u).mul_left (θ x))), tsum_mul_left]

/-- The unlocalized commutator of the actual homogeneous left quantization
with multiplication by a fixed Schwartz cutoff. -/
def compactPrincipalLeftCommutator (a : E → E → ℝ) (θ : SchwartzMap E ℂ)
    (u : SchwartzMap E ℂ) (x : E) : ℂ :=
  radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) (energyProduct θ u) x -
    θ x * radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) u x

/-- The ordinary first-jet (L^3) bounds for the complete variable
coefficient commutator, with constants fixed before the input. -/
theorem exists_compact_principal_left_commutator_W13 (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (a : E → E → ℝ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderOneBudget a M)
    (F₁ F₂ : ℝ) (F₁0 : 0 ≤ F₁) (F₂0 : 0 ≤ F₂) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧
      ∀ θ : SchwartzMap E ℂ, patchFourierMoment 1 θ ≤ F₁ → patchFourierMoment 2 θ ≤ F₂ →
        SchwartzOrderZeroJetBound (compactPrincipalLeftCommutator a θ) A A := by
  let I := (Index → ℤ) × Fin 2
  let f (i : I) := compactBaseSpatialMode P ρ hρ hS i.1 i.2
  let b (i : I) := compactBaseRealMode P a i.1 i.2
  let Q := max 1 ((3 / spatialModeRate P)^8) * M
  let D (i : I) := Q / spatialLatticeWeight i.1 ^ 8
  obtain ⟨DS,J,rec⟩ := compact_base_order_one_series_data P R hP hRP ρ hρ hS ρone a support ha hom M M0 hM
  have D0 (i : I) : 0 ≤ D i := (J i).1
  have bSm (i : I) : ContDiffOn ℝ ∞ (b i) {ξ | ξ ≠ 0} := (J i).2.1
  obtain ⟨U,U0,hU⟩ := compact_base_spatial_mode_uniform_bound P ρ hρ hS
  obtain ⟨V,V0,hV⟩ := compact_base_spatial_partial_uniform_bound P ρ hρ hS
  let V' (i : I) := V * spatialLatticeWeight i.1
  have V'0 (i : I) : 0 ≤ V' i := mul_nonneg V0 (by unfold spatialLatticeWeight; positivity)
  have sb (k : Index → ℤ) : 1 ≤ spatialLatticeWeight k := le_add_of_nonneg_right (norm_nonneg _)
  have H : Summable (fun i : I => D i * (U + V' i)) := by
    have Q0 : 0 ≤ Q := mul_nonneg (zero_le_one.trans (le_max_left _ _)) M0
    have S₁ : Summable (fun i : I => spatialLatticeWeight i.1 ^ 1 / spatialLatticeWeight i.1 ^ 8) := by
      apply (summable_prod_of_nonneg (fun i : I => div_nonneg (pow_nonneg (zero_le_one.trans (sb i.1)) _)
        (pow_nonneg (zero_le_one.trans (sb i.1)) _))).mpr
      refine ⟨fun _ => (hasSum_fintype _).summable,?_⟩
      simp only [tsum_fintype, Fin.sum_univ_two, ← two_mul]
      exact (summable_spatial_lattice_weighted_decay 8 1 (by decide) (by decide)).mul_left 2
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (D0 i) (add_nonneg U0 (V'0 i))) _ (S₁.mul_left ((U+V)*Q))
    intro i
    have step : U + V' i ≤ (U+V)*spatialLatticeWeight i.1 := by
      rw [add_mul]
      exact add_le_add (le_mul_of_one_le_right U0 (sb i.1)) le_rfl
    apply (mul_le_mul_of_nonneg_left step (D0 i)).trans_eq
    simp only [D, pow_one, div_eq_mul_inv]
    ring
  obtain ⟨A,Afin,base⟩ := exists_separated_left_commutator_mode_sum_W13 f b bSm
    (fun i => (J i).2.2.1) D (fun _ => U) V' D0 (fun _ => U0) V'0
    (fun i => (J i).2.2.2.1) (fun i => hU i.1 i.2)
    (fun i j x => hV i.1 i.2 j x) H F₁ F₂ F₁0 F₂0
  refine ⟨A, Afin, fun θ θ1 θ2 => ?_⟩
  have eq : compactPrincipalLeftCommutator a θ = fun u x => ∑' i, f i x * radianCommutator (b i) θ u x := by
    funext u x
    exact radian_left_quantization_separated_commutator a f b
      (fun i => measurable_of_continuousOn_compl_singleton 0 (bSm i).continuousOn)
      D D0 DS (fun i => (J i).2.2.2.2) U U0 (fun i => hU i.1 i.2)
      (fun x ξ _ => rec x ξ) θ u x
  rw [eq]
  exact base θ θ1 θ2

/-- Actual uniform cutoff commutator after two fixed scale moment bounds.
The constants precede the actual center, cutoff and input field. -/
theorem exists_localized_frozen_left_commutator_W13 (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (a : E → E → ℝ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderOneBudget a M)
    (F₁ F₂ : ℝ) (F₁0 : 0 ≤ F₁) (F₂0 : 0 ≤ F₂)
    (Pθ Tθ : ℝ≥0∞) (Pfin : Pθ < ⊤) (Tfin : Tθ < ⊤) :
    ∃ A B : ℝ≥0∞, A < ⊤ ∧ B < ⊤ ∧
      ∀ (c : E) (θ : SchwartzMap E ℂ), patchFourierMoment 1 θ ≤ F₁ → patchFourierMoment 2 θ ≤ F₂ →
        eLpNorm (θ : E → ℂ) ⊤ volume ≤ Pθ →
        (∀ j : Index, eLpNorm (energyPartial j θ : E → ℂ) ⊤ volume ≤ Tθ) →
          SchwartzOrderZeroJetBound (localizedFrozenLeftCommutator a c θ) A B := by
  obtain ⟨A, Afin, base⟩ :=
    exists_compact_principal_left_commutator_W13 P R hP hRP ρ hρ hS ρone a support ha hom M M0 hM
      F₁ F₂ F₁0 F₂0
  obtain ⟨K,K0,frozen⟩ := exists_radian_commutator_order_zero_W13
  have τ0 : 0 ≤ tau := by unfold tau; positivity
  let A₀ := ENNReal.ofReal (K*M*F₁)
  let B₀ := ENNReal.ofReal (K*M*tau*F₂)
  refine ⟨Pθ*(A+A₀), Tθ*(A+A₀)+Pθ*(A+B₀), ?_, ?_, ?_⟩
  · exact ENNReal.mul_lt_top Pfin (ENNReal.add_lt_top.mpr ⟨Afin,ENNReal.ofReal_lt_top⟩)
  · exact ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top Tfin (ENNReal.add_lt_top.mpr ⟨Afin,ENNReal.ofReal_lt_top⟩),
        ENNReal.mul_lt_top Pfin (ENNReal.add_lt_top.mpr ⟨Afin,ENNReal.ofReal_lt_top⟩)⟩
  intro c θ θ1 θ2 cutoff cutoffJet
  have ha' : ContDiffOn ℝ ∞ (a c) {ξ | ξ ≠ 0} :=
    Complex.reCLM.contDiff.fun_comp_contDiffOn (ha.frequencySmooth c)
  have aJet (n : ℕ) (hn : n ≤ 7) (ξ : E) (hξ : ξ ∈ sphere (0 : E) 1) :
      ‖iteratedFDeriv ℝ n (a c) ξ‖ ≤ M := by
    have hU : IsOpen {ξ : E | ξ ≠ 0} := isClosed_singleton.isOpen_compl
    have nz : ξ ≠ 0 := by
      have q : ‖ξ‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hξ
      exact norm_ne_zero_iff.mp (q.trans_ne one_ne_zero)
    have hA := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (ha'.contDiffAt (hU.mem_nhds nz))
      (show (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    exact hA.symm.trans_le (hM n hn ξ hξ c).1
  have r0 := frozen (a c) ha' (fun t ht => hom t ht c) M M0 aJet θ
  have a0 := schwartz_order_zero_jet_bound_mono (radianCommutator (a c) θ) _ _ A₀ B₀ r0
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left θ1 (mul_nonneg K0 M0)))
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left θ2 (mul_nonneg (mul_nonneg K0 M0) τ0)))
  let Act := compactPrincipalLeftCommutator a θ
  have bSub := schwartz_order_zero_jet_bound_sub Act (radianCommutator (a c) θ) A A A₀ B₀
    (base θ θ1 θ2) a0
  have out := schwartz_order_zero_jet_bound_output_product θ _ _ _ Pθ Tθ bSub cutoff cutoffJet
  have eq : localizedFrozenLeftCommutator a c θ =
      fun u x => θ x * (Act u x - radianCommutator (a c) θ u x) := rfl
  rw [eq]
  exact out

end Burnett.A03
