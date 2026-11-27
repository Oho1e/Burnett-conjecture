import Burnett.Analysis.PrincipalEnergy.Freezing.CompactOrderZeroLeft
import Burnett.Analysis.PrincipalEnergy.Freezing.SchwartzOrderZeroCommutator
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 3100000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ContDiff ENNReal

/-- Mixed jets of the actual compact-base homogeneous principal symbol on
the unit sphere. The lattice losses come only from eight base derivatives. -/
def CompactBaseOrderOneBudget (a : E → E → ℝ) (M : ℝ) : Prop :=
  ∀ n : ℕ, n ≤ 7 → ∀ ξ ∈ sphere (0 : E) 1, ∀ x : E,
    ‖iteratedFDeriv ℝ n (fun q => (a x q : ℂ)) ξ‖ ≤ M ∧
      ‖iteratedFDeriv ℝ 8 (fun y => iteratedFDeriv ℝ n (fun q => (a y q : ℂ)) ξ) x‖ ≤ M

private theorem compact_base_homogeneous_cube_coefficient (P : ℝ) (a : E → E → ℝ)
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (k : Index → ℤ) (t : ℝ) (ht : 0 < t) (ξ : E) :
    compactBaseCubeCoefficient P (fun x q => (a x q : ℂ)) k (t • ξ) =
      t • compactBaseCubeCoefficient P (fun x q => (a x q : ℂ)) k ξ := by
  unfold compactBaseCubeCoefficient spatialCubeFourierCoefficient
  have integrand (y : E) :
      Complex.exp ((↑(-spatialModePhase P k y) : ℂ) * Complex.I) • (a y (t • ξ) : ℂ) =
        t • (Complex.exp ((↑(-spatialModePhase P k y) : ℂ) * Complex.I) • (a y ξ : ℂ)) := by
    rw [hom t ht y ξ]
    simp only [Complex.ofReal_mul, smul_eq_mul, Complex.real_smul]
    ring
  simp_rw [integrand, integral_smul]
  rw [smul_comm]

private theorem compact_base_homogeneous_mode_jet_le (P : ℝ) (a : E → E → ℝ)
    (U : Set E) (hU : IsOpen U) (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) U)
    (n : ℕ) (ξ : E) (hξ : ξ ∈ U) (k : Index → ℤ) (j : Fin 2) :
    ‖iteratedFDeriv ℝ n (compactBaseRealMode P a k j) ξ‖ ≤
      ‖iteratedFDeriv ℝ n (compactBaseCubeCoefficient P (fun x q => (a x q : ℂ)) k) ξ‖ := by
  let c := compactBaseCubeCoefficient P (fun x q => (a x q : ℂ)) k
  let L : ℂ →L[ℝ] ℝ := if j = 0 then Complex.reCLM else -Complex.imCLM
  have normL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro z
    by_cases hj : j = 0
    · simpa [L, hj, Real.norm_eq_abs] using Complex.abs_re_le_norm z
    · simpa [L, hj, Real.norm_eq_abs] using Complex.abs_im_le_norm z
  have eq : compactBaseRealMode P a k j = L ∘ c := by
    funext q
    by_cases hj : j = 0 <;> simp [L, c, hj, compactBaseRealMode]
  have hC := (compact_base_cube_coefficient_smooth P _ U hU ha k).contDiffAt (hU.mem_nhds hξ)
  rw [eq, L.iteratedFDeriv_comp_left hC (by exact_mod_cast le_top)]
  exact (L.norm_compContinuousMultilinearMap_le _).trans (mul_le_of_le_one_left (norm_nonneg _) normL)

/-- Actual Fourier profiles of a compact-base homogeneous principal
symbol remain degree one with all sphere-jet budgets decaying together. -/
theorem compact_base_order_one_real_mode_budget (P R : ℝ) (hP : 0 < P) (hRP : R ≤ P)
    (a : E → E → ℝ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderOneBudget a M)
    (k : Index → ℤ) (j : Fin 2) :
    let b := compactBaseRealMode P a k j
    let D := max 1 ((3 / spatialModeRate P)^8) * M / spatialLatticeWeight k ^ 8
    ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} ∧
      (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) ∧
      ∀ n : ℕ, n ≤ 7 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D := by
  intro b D
  have opened : IsOpen {ξ : E | ξ ≠ 0} := isClosed_singleton.isOpen_compl
  refine ⟨compact_base_real_mode_smooth P a _ opened ha k j,?_,?_⟩
  · intro t ht ξ
    change compactBaseRealMode P a k j (t • ξ) = t * compactBaseRealMode P a k j ξ
    unfold compactBaseRealMode
    rw [compact_base_homogeneous_cube_coefficient P a hom k t ht ξ]
    by_cases hj : j = 0
    · simp [hj, Complex.real_smul]
    · simp [hj, Complex.real_smul, mul_neg]
  intro n hn ξ hξ
  have nz : ξ ≠ 0 := by
    have q : ‖ξ‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hξ
    exact norm_ne_zero_iff.mp (q.trans_ne one_ne_zero)
  exact (compact_base_homogeneous_mode_jet_le P a _ opened ha n ξ nz k j).trans
    (compact_base_cube_coefficient_jet_decay P R hP hRP _
      (fun x q hx => by simp [support x q hx]) _ opened ha n 8 ξ nz M M0
      (fun x => (hM n hn ξ hξ x).1) (fun x => (hM n hn ξ hξ x).2) k)

/-- Literal separated reconstruction of the principal symbol, with the
same lattice budget as its unit-sphere jets. -/
theorem compact_base_order_one_series_data (P R : ℝ) (hP : 0 < P) (hRP : R < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) R, ρ x = 1)
    (a : E → E → ℝ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderOneBudget a M) :
    let I := (Index → ℤ) × Fin 2
    let f (i : I) := compactBaseSpatialMode P ρ hρ hS i.1 i.2
    let b (i : I) := compactBaseRealMode P a i.1 i.2
    let D (i : I) := max 1 ((3 / spatialModeRate P)^8) * M / spatialLatticeWeight i.1 ^ 8
    Summable D ∧
      (∀ i, 0 ≤ D i ∧ ContDiffOn ℝ ∞ (b i) {ξ | ξ ≠ 0} ∧
        (∀ t : ℝ, 0 < t → ∀ ξ, b i (t • ξ) = t * b i ξ) ∧
        (∀ n : ℕ, n ≤ 7 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n (b i) ξ‖ ≤ D i) ∧
        ∀ ξ, ‖b i ξ‖ ≤ D i * ‖ξ‖) ∧
      ∀ x ξ, HasSum (fun i => f i x * (b i ξ : ℂ)) (a x ξ : ℂ) := by
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
    change Summable (fun k => ∑' (_ : Fin 2), d k)
    simp only [tsum_fintype, Fin.sum_univ_two, ← two_mul]
    exact Sd.mul_left 2
  have all (i : I) :=
    compact_base_order_one_real_mode_budget P R hP hRP.le a support ha hom M M0 hM i.1 i.2
  have lin (i : I) (ξ : E) : ‖b i ξ‖ ≤ D i * ‖ξ‖ := by
    have e := norm_symbol_shift_sub_le (b i) (all i).1 (all i).2.1 (D i) (d0 i.1)
      ((all i).2.2 1 (by decide)) ξ 0
    have hz : b i 0 = 0 := homogeneous_value_zero (all i).2.1
    simpa only [zero_add, hz, sub_zero, mul_comm ‖ξ‖] using e
  refine ⟨hD,fun i => ⟨d0 i.1,(all i).1,(all i).2.1,(all i).2.2,lin i⟩,?_⟩
  intro x ξ
  by_cases nz : ξ = 0
  · have hz : a x 0 = 0 := homogeneous_value_zero (fun t ht q => hom t ht x q)
    have bz (i : I) : b i 0 = 0 := homogeneous_value_zero (all i).2.1
    simpa only [nz, hz, bz, Complex.ofReal_zero, mul_zero] using (hasSum_zero : HasSum (0 : I → ℂ) 0)
  let w := ‖ξ‖⁻¹ • ξ
  have np : 0 < ‖ξ‖ := norm_pos_iff.mpr nz
  have ws : w ∈ sphere (0 : E) 1 := by
    simpa only [mem_sphere, dist_zero_right, w] using norm_smul_inv_norm (𝕜 := ℝ) nz
  have wn : w ≠ 0 := by
    have z : ‖w‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using ws
    exact norm_ne_zero_iff.mp (z.trans_ne one_ne_zero)
  have scale : ‖ξ‖ • w = ξ := by simp [w, smul_smul, np.ne']
  have openU : IsOpen {ξ : E | ξ ≠ 0} := isClosed_singleton.isOpen_compl
  have hs : Summable (fun k => compactBaseCubeCoefficient P (fun x q => (a x q : ℂ)) k ξ) := by
    apply Summable.of_norm_bounded (Sd.mul_right ‖ξ‖)
    intro k
    have H := compact_base_cube_coefficient_jet_decay P R hP hRP.le _ (fun y q hy => by simp [support y q hy])
      _ openU ha 0 8 w wn M M0 (fun y => (hM 0 (by decide) w ws y).1)
      (fun y => (hM 0 (by decide) w ws y).2) k
    rw [norm_iteratedFDeriv_zero] at H
    have hScale := compact_base_homogeneous_cube_coefficient P a hom k ‖ξ‖ np w
    rw [scale] at hScale
    rw [hScale, norm_smul, Real.norm_of_nonneg np.le, mul_comm]
    exact mul_le_mul_of_nonneg_right H np.le
  have hc : Continuous (fun y => a y ξ) := by
    let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℂ (fun _ => 0)
    exact Complex.reCLM.continuous.comp (L.continuous.comp (ha.baseJetSmooth 0 ξ nz).continuous)
  obtain ⟨U,U0,hU⟩ := compact_base_spatial_mode_uniform_bound P ρ hρ hS
  let v (i : I) := f i x * (b i ξ : ℂ)
  have vs : Summable v := Summable.of_norm_bounded ((hD.mul_right ‖ξ‖).mul_left U) fun i => by
    rw [show v i = f i x * (b i ξ : ℂ) from rfl, norm_mul, Complex.norm_real]
    exact mul_le_mul (hU i.1 i.2 x) (lin i ξ) (norm_nonneg _) U0
  have H := compact_base_real_symbol_hasSum P R hP hRP a ξ hc (fun y hy => support y ξ hy)
    hs ρ hρ hS ρone x
  have eq : (∑' i, v i) = (a x ξ : ℂ) := by
    rw [vs.tsum_prod' (fun _ => (hasSum_fintype _).summable)]
    simp_rw [tsum_fintype]
    exact H.tsum_eq
  exact eq ▸ vs.hasSum

end Burnett.A03
