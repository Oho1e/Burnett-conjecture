import Burnett.Analysis.PrincipalEnergy.Freezing.CompactOrderZeroModeAction
import Burnett.Analysis.PrincipalEnergy.Freezing.RadianLeftFullSymbol

set_option autoImplicit false
set_option maxHeartbeats 3900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal ContDiff FourierTransform

theorem compact_base_spatial_mode_uniform_bound (P : ℝ) (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hS : tsupport ρ ⊆ ball (0 : E) P) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ (k : Index → ℤ) (j : Fin 2) (x : E),
      ‖compactBaseSpatialMode P ρ hρ hS k j x‖ ≤ U := by
  let ρS := patchCutoffSchwartz P ρ hρ hS
  let U := (SchwartzMap.seminorm ℝ 0 0) ρS
  have U0 : 0 ≤ U := apply_nonneg _ _
  refine ⟨U,U0,?_⟩
  intro k j x
  have base : ‖ρ x‖ ≤ U := by
    convert SchwartzMap.norm_le_seminorm ℝ ρS x
    change ‖ρ x‖ = ‖((ρ x : ℝ) : ℂ)‖
    rw [Complex.norm_real]
  rw [compact_base_spatial_mode_apply, Complex.norm_real, norm_mul]
  apply (mul_le_of_le_one_right (norm_nonneg _) ?_).trans base
  split
  · exact Real.abs_cos_le_one _
  · exact Real.abs_sin_le_one _

private theorem compact_base_zero_slice_continuous (a : E → E → ℝ)
    (U : Set E) (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) U) (ξ : E) (hξ : ξ ∈ U) :
    Continuous (fun x => a x ξ) := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℂ (fun _ => 0)
  have c := Complex.reCLM.continuous.comp (L.continuous.comp (ha.baseJetSmooth 0 ξ hξ).continuous)
  exact c

/-- Literal mode reconstruction with a single summable frequency growth
budget, ready for the left Fourier integral and the cut-off midpoint kernel. -/
theorem compact_base_order_zero_series_data (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (a : E → E → ℝ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) univ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderZeroBudget a M) :
    let I := (Index → ℤ) × Fin 2
    let f (i : I) := compactBaseSpatialMode P ρ hρ hS i.1 i.2
    let b (i : I) := compactBaseRealMode P a i.1 i.2
    let D (i : I) := max 1 ((3 / spatialModeRate P)^8) * M / spatialLatticeWeight i.1 ^ 8
    Summable D ∧ (∀ i, 0 ≤ D i ∧ ContDiff ℝ ∞ (b i) ∧ ∀ ξ, ‖b i ξ‖ ≤ D i) ∧
      ∀ x ξ, ξ ≠ 0 → HasSum (fun i => f i x * (b i ξ : ℂ)) (a x ξ : ℂ) := by
  intro I f b D
  let C := max 1 ((3 / spatialModeRate P)^8) * M
  let d (k : Index → ℤ) := C / spatialLatticeWeight k ^ 8
  have C0 : 0 ≤ C := mul_nonneg (zero_le_one.trans (le_max_left _ _)) M0
  have d0 (k : Index → ℤ) : 0 ≤ d k := by
    apply div_nonneg C0 (pow_nonneg ?_ _)
    unfold spatialLatticeWeight
    positivity
  have Sd : Summable d := by
    have h := (summable_spatial_lattice_weighted_decay 8 0 (by decide) (by decide)).mul_left C
    simpa [d, pow_zero, mul_div_assoc] using h
  have hD : Summable D := by
    apply (summable_prod_of_nonneg (fun i : I => d0 i.1)).mpr
    refine ⟨fun _ => hasSum_fintype _ |>.summable, ?_⟩
    simp only [tsum_fintype, ← show ∀ k, C / spatialLatticeWeight k ^ 8 = d k from fun _ => rfl]
    convert Sd.mul_left 2 using 1
    funext k
    rw [Fin.sum_univ_two]
    ring
  have all (i : I) : 0 ≤ D i ∧ ContDiff ℝ ∞ (b i) ∧ ∀ ξ, ‖b i ξ‖ ≤ D i := by
    have J := compact_base_order_zero_real_mode_budget P R hP hRP.le a support ha M M0 hM i.1 i.2
    exact ⟨d0 i.1, J.1, fun ξ => mikhlin_order_zero_budget_value_bound (b i) J.1 (D i) J.2 ξ⟩
  refine ⟨hD, all, ?_⟩
  intro x ξ hξ
  let v (i : I) := f i x * (b i ξ : ℂ)
  obtain ⟨U,U0,hU⟩ := compact_base_spatial_mode_uniform_bound P ρ hρ hS
  have vs : Summable v := Summable.of_norm_bounded (hD.mul_left U) fun i => by
    rw [show v i = f i x * (b i ξ : ℂ) from rfl, norm_mul, Complex.norm_real]
    exact mul_le_mul (hU i.1 i.2 x) ((all i).2.2 ξ) (norm_nonneg _) U0
  have hs : Summable (fun k => compactBaseCubeCoefficient P (fun x q => (a x q : ℂ)) k ξ) := by
    apply Summable.of_norm_bounded Sd
    intro k
    have elem (y : E) := hM 0 (by decide) ξ hξ y
    have hV (y : E) : ‖iteratedFDeriv ℝ 0 (fun q => (a y q : ℂ)) ξ‖ ≤ M := by
      simpa only [pow_zero, one_mul] using (elem y).1
    have hJ (y : E) : ‖iteratedFDeriv ℝ 8 (fun z => iteratedFDeriv ℝ 0 (fun q => (a z q : ℂ)) ξ) y‖ ≤ M := by
      simpa only [pow_zero, one_mul] using (elem y).2
    have H := compact_base_cube_coefficient_jet_decay P R hP hRP.le _ (fun y q hy => by simp [support y q hy])
      univ isOpen_univ ha 0 8 ξ (mem_univ _) M M0 hV hJ k
    simpa only [norm_iteratedFDeriv_zero, d, C] using H
  have H := compact_base_real_symbol_hasSum P R hP hRP a ξ
    (compact_base_zero_slice_continuous a univ ha ξ (mem_univ _)) (fun y hy => support y ξ hy)
    hs ρ hρ hS ρone x
  have eq : (∑' i, v i) = (a x ξ : ℂ) := by
    rw [vs.tsum_prod' (fun _ => (hasSum_fintype _).summable)]
    simp_rw [tsum_fintype]
    exact H.tsum_eq
  exact eq ▸ vs.hasSum

/-- The proven real order-zero space series is exactly the original left
quantization of a compact-base full symbol. -/
theorem compact_base_order_zero_left_eq_mode_action (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1) (a : E → E → ℝ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) univ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderZeroBudget a M) :
    radianLeftQuantization (fun x ξ => (a x ξ : ℂ)) = compactBaseModeQuantization P ρ hρ hS 0 a := by
  obtain ⟨Dsum,B,series⟩ := compact_base_order_zero_series_data P R hP hRP ρ hρ hS ρone a support ha M M0 hM
  obtain ⟨U,U0,hU⟩ := compact_base_spatial_mode_uniform_bound P ρ hρ hS
  funext u x
  exact radian_left_quantization_separated_sum _
    (fun i : (Index → ℤ) × Fin 2 => compactBaseSpatialMode P ρ hρ hS i.1 i.2)
    (fun i => compactBaseRealMode P a i.1 i.2)
    (fun i => (B i).2.1.continuous.measurable) _
    (fun i => (B i).1) Dsum
    (fun i ξ => ((B i).2.2 ξ).trans (le_mul_of_one_le_right (B i).1 (le_add_of_nonneg_right (norm_nonneg _))))
    U U0 (fun i => hU i.1 i.2) series u x

/-- The real compact-base full symbol gives an actual left order-zero W¹,³ action. -/
theorem exists_compact_base_order_zero_left_action_W13 (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1) (a : E → E → ℝ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) univ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderZeroBudget a M) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ SchwartzOrderZeroJetBound (radianLeftQuantization (fun x ξ => (a x ξ : ℂ))) A A := by
  rw [compact_base_order_zero_left_eq_mode_action P R hP hRP ρ hρ hS ρone a support ha M M0 hM]
  obtain ⟨A,Afin,hA⟩ := exists_compact_base_order_zero_mode_action_W13 P R hP hRP.le ρ hρ hS a support ha M M0 hM
  exact ⟨A,Afin,hA 0⟩

end Burnett.A03
