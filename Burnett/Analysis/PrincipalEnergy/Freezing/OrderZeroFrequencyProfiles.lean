import Burnett.Analysis.PrincipalEnergy.Freezing.CubeFourierDecay
import Burnett.Analysis.PrincipalEnergy.Freezing.CubeFourierReconstruction
import Burnett.Analysis.SpatialFreezing.SpatialLatticeSummability
import Burnett.Analysis.CubicEnergy.JointMultiplier.MikhlinPartition
import Burnett.Analysis.CubicEnergy.CompleteEnergy.SymbolSeminormLow
import Burnett.Analysis.PrincipalEnergy.Freezing.ModulatedAngularAction

set_option autoImplicit false
set_option maxHeartbeats 2550000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped ContDiff RealInnerProductSpace

/-- The usual finite Mikhlin seminorm, in the normalized Euclidean frequency.
A smooth \(S^0_{1,0}\) symbol satisfies this bound for a finite symbol budget. -/
def MikhlinOrderZeroBudget (m : E → ℝ) (D : ℝ) : Prop :=
  ∀ n : ℕ, n ≤ 8 → ∀ ξ : E, ξ ≠ 0 → ‖ξ‖ ^ n * ‖iteratedFDeriv ℝ n m ξ‖ ≤ D

private def orderZeroAnnularExtension (ξ : E) : ℝ :=
  mikhlinBall ((1 / 2 : ℝ) • ξ) * (1 - mikhlinBall ((4 : ℝ) • ξ))

private theorem real_norm_scale (s : ℝ) (hs : 0 ≤ s) (ξ : E) : ‖s • ξ‖ = s * ‖ξ‖ := by
  rw [norm_smul, Real.norm_of_nonneg hs]

private theorem inner_bump_one (ξ : E) (h : ‖ξ‖ ≤ 1) : mikhlinBall ξ = 1 :=
  mikhlinBall.one_of_mem_closedBall (by simpa only [mem_closedBall, dist_zero_right] using h)

private theorem outer_bump_zero (ξ : E) (h : 2 ≤ ‖ξ‖) : mikhlinBall ξ = 0 :=
  mikhlinBall.zero_of_le_dist (by simpa only [dist_zero_right] using h)

private theorem order_zero_annular_extension_one (ξ : E) (hlo : (1 / 2 : ℝ) ≤ ‖ξ‖) (hhi : ‖ξ‖ ≤ 2) :
    orderZeroAnnularExtension ξ = 1 := by
  have h₁ : ‖((1 / 2 : ℝ) • ξ)‖ ≤ 1 := by
    rw [real_norm_scale _ (by norm_num)]; linarith
  have h₂ : 2 ≤ ‖((4 : ℝ) • ξ)‖ := by
    rw [real_norm_scale _ (by norm_num)]; linarith
  rw [orderZeroAnnularExtension, inner_bump_one _ h₁, outer_bump_zero _ h₂, sub_zero, one_mul]

private def orderZeroAnnularSupport : Set E := {ξ | (1 / 4 : ℝ) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 4}

private theorem order_zero_annular_support :
    tsupport (orderZeroAnnularExtension : E → ℝ) ⊆ orderZeroAnnularSupport := by
  apply closure_minimal _ ((isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const))
  intro ξ hs
  change (1 / 4 : ℝ) ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 4
  constructor
  · by_contra! h
    have h₁ : ‖((4 : ℝ) • ξ)‖ ≤ 1 := by rw [real_norm_scale _ (by norm_num)]; linarith
    exact hs (by rw [orderZeroAnnularExtension, inner_bump_one _ h₁, sub_self, mul_zero])
  · by_contra! h
    have h₁ : 2 ≤ ‖((1 / 2 : ℝ) • ξ)‖ := by rw [real_norm_scale _ (by norm_num)]; linarith
    exact hs (by rw [orderZeroAnnularExtension, outer_bump_zero _ h₁, zero_mul])

private theorem order_zero_annular_extension_smooth : ContDiff ℝ ∞ orderZeroAnnularExtension :=
  (mikhlinBall.contDiff.comp (contDiff_const.smul contDiff_id)).mul
    (contDiff_const.sub (mikhlinBall.contDiff.comp (contDiff_const.smul contDiff_id)))

private theorem normalized_order_zero_jet (m : E → ℝ) (hm : ContDiff ℝ ∞ m)
    (D : ℝ) (D0 : 0 ≤ D) (budget : MikhlinOrderZeroBudget m D)
    (s : ℝ) (s0 : 0 < s) (n : ℕ) (hn : n ≤ 8) (ξ : E) (x0 : (1 / 4 : ℝ) ≤ ‖ξ‖) :
    ‖iteratedFDeriv ℝ n (fun x : E => m (s⁻¹ • x)) ξ‖ ≤ D * 4 ^ 8 := by
  let L : E →L[ℝ] E := s⁻¹ • ContinuousLinearMap.id ℝ E
  have eq (x : E) : L x = s⁻¹ • x := rfl
  have nL : ‖L‖ ≤ s⁻¹ := by
    rw [show L = s⁻¹ • ContinuousLinearMap.id ℝ E from rfl, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr s0.le)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr s0.le) (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
  change ‖iteratedFDeriv ℝ n (m ∘ L) ξ‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hm ξ (by exact_mod_cast le_top)]
  have c := (iteratedFDeriv ℝ n m (L ξ)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at c
  have xp : 0 < ‖ξ‖ := lt_of_lt_of_le (by norm_num) x0
  have lξ : L ξ ≠ 0 := by rw [eq]; exact smul_ne_zero (inv_ne_zero s0.ne') (norm_pos_iff.mp xp)
  have power : 1 ≤ (4 : ℝ) ^ n * ‖ξ‖ ^ n := by
    rw [← mul_pow, ← one_pow n]
    exact pow_le_pow_left₀ zero_le_one (by linarith) _
  have weighted : ‖iteratedFDeriv ℝ n m (L ξ)‖ * (s⁻¹)^n ≤ D * 4 ^ n := by
    apply (mul_le_mul_iff_right₀ (pow_pos xp n)).mp
    calc
      _ = ‖L ξ‖ ^ n * ‖iteratedFDeriv ℝ n m (L ξ)‖ := by
        rw [eq, real_norm_scale _ (inv_nonneg.mpr s0.le), mul_pow]
        ring
      _ ≤ D := budget n hn _ lξ
      _ ≤ _ := (le_mul_of_one_le_right D0 power).trans_eq (by ring)
  calc
    _ ≤ ‖iteratedFDeriv ℝ n m (L ξ)‖ * ‖L‖ ^ n := c
    _ ≤ ‖iteratedFDeriv ℝ n m (L ξ)‖ * (s⁻¹)^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) nL _) (norm_nonneg _)
    _ ≤ D * 4 ^ n := weighted
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hn) D0

/-- These are the actual normalized cube Fourier coefficients of the
rescaled nonhomogeneous order-zero symbol. -/
def normalizedMikhlinCubeCoefficient (m : E → ℝ) (s : ℝ) (k : Index → ℤ) : ℂ :=
  spatialCubeFourierCoefficient 5 k (fun ξ => ((orderZeroAnnularExtension ξ * m (s⁻¹ • ξ) : ℝ) : ℂ))

/-- All rescalings of an actual \(S^0\) frequency symbol have a single
normalized Fourier coefficient budget and reconstruct the uncut symbol
on the fixed annulus. -/
theorem exists_normalized_order_zero_annular_expansion :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : E → ℝ), ContDiff ℝ ∞ m →
    ∀ D : ℝ, 0 ≤ D → MikhlinOrderZeroBudget m D →
    ∀ (s : ℝ), 0 < s →
      (∀ k, ‖normalizedMikhlinCubeCoefficient m s k‖ ≤ K * D / spatialLatticeWeight k ^ 8) ∧
      ∀ ξ : E, (1 / 2 : ℝ) ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 →
        HasSum (fun k : Index → ℤ => normalizedMikhlinCubeCoefficient m s k *
          patchFourierPhase ξ (spatialModeFrequency 5 k)) (m (s⁻¹ • ξ) : ℂ) := by
  obtain ⟨A, A0, Ap⟩ := compact_derivative_bound 8 (isCompact_closedBall (0 : E) 4)
    isOpen_univ (subset_univ _) orderZeroAnnularExtension order_zero_annular_extension_smooth.contDiffOn
  let B := (2 : ℝ)^8 * A * 4^8
  let K := max 1 ((3 / spatialModeRate 5)^8) * B
  have B0 : 0 ≤ B := by unfold B; positivity
  have K0 : 0 ≤ K := mul_nonneg (le_trans zero_le_one (le_max_left _ _)) B0
  refine ⟨K, K0, ?_⟩
  intro m hm D D0 budget s s0
  let g (ξ : E) := orderZeroAnnularExtension ξ * m (s⁻¹ • ξ)
  let F (ξ : E) := (g ξ : ℂ)
  have hmRescale : ContDiff ℝ ∞ (fun ξ : E => m (s⁻¹ • ξ)) := hm.comp (contDiff_const.smul contDiff_id)
  have hg : ContDiff ℝ ∞ g := order_zero_annular_extension_smooth.mul hmRescale
  have hF : ContDiff ℝ ∞ F := Complex.ofRealCLM.contDiff.comp hg
  have Sg : tsupport g ⊆ orderZeroAnnularSupport :=
    (tsupport_mul_subset_left (f := orderZeroAnnularExtension) (g := fun ξ => m (s⁻¹ • ξ))).trans
      order_zero_annular_support
  have supportEq : Function.support F = Function.support g := by
    ext x
    simp only [F, Function.mem_support]
    exact not_congr Complex.ofReal_eq_zero
  have SF : tsupport F ⊆ closedBall (0 : E) 4 := by
    intro ξ hξ
    have h := Sg (by simpa only [tsupport, supportEq] using hξ)
    exact (mem_closedBall.mpr (by rw [dist_zero_right]; exact h.2))
  have hcompact : HasCompactSupport F := (isCompact_closedBall (0 : E) 4).of_isClosed_subset isClosed_closure SF
  let v := hcompact.toSchwartzMap hF
  have vFun : (v : E → ℂ) = F := rfl
  have jets (n : ℕ) (hn : n ≤ 8) (ξ : E) : ‖iteratedFDeriv ℝ n F ξ‖ ≤ B * D := by
    by_cases supp : ξ ∈ orderZeroAnnularSupport
    · have hBall : ξ ∈ closedBall (0 : E) 4 := by rw [mem_closedBall, dist_zero_right]; exact supp.2
      change ‖iteratedFDeriv ℝ n (Complex.ofRealLI ∘ g) ξ‖ ≤ B * D
      rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hg.contDiffAt (by exact_mod_cast le_top)]
      have b := product_jet_bound isOpen_univ order_zero_annular_extension_smooth.contDiffOn hmRescale.contDiffOn
        (mem_univ ξ) hn A0 (mul_nonneg D0 (by positivity : 0 ≤ (4 : ℝ)^8)) (fun j hj => Ap j hj ξ hBall)
        (fun j hj => normalized_order_zero_jet m hm D D0 budget s s0 j hj ξ supp.1)
      exact b.trans_eq (by unfold B; ring)
    · have outside : ξ ∉ tsupport (iteratedFDeriv ℝ n F) := by
        intro q
        have h := tsupport_iteratedFDeriv_subset n q
        exact supp (Sg (by simpa only [tsupport, supportEq] using h))
      rw [image_eq_zero_of_notMem_tsupport outside, norm_zero]
      positivity
  have decay (k : Index → ℤ) : ‖normalizedMikhlinCubeCoefficient m s k‖ ≤ K * D / spatialLatticeWeight k ^ 8 := by
    have hval (ξ : E) : ‖v ξ‖ ≤ B * D := by simpa only [vFun, norm_iteratedFDeriv_zero] using jets 0 (by decide) ξ
    have hjet (ξ : E) : ‖iteratedFDeriv ℝ 8 (v : E → ℂ) ξ‖ ≤ B * D := by rw [vFun]; exact jets 8 le_rfl ξ
    have hvS : tsupport (v : E → ℂ) ⊆ spatialFourierCube 5 := SF.trans (closed_ball_subset_spatial_fourier_cube 4 5 (by norm_num))
    have est := spatial_cube_fourier_coefficient_polynomial_decay v 5 (by norm_num) 8 _ (mul_nonneg B0 D0)
      hvS (fun ξ _ => hval ξ) (fun ξ _ => hjet ξ) k
    change ‖spatialCubeFourierCoefficient 5 k F‖ ≤ _
    rw [← vFun]
    exact est.trans_eq (by dsimp only [K, spatialLatticeWeight]; ring)
  refine ⟨decay, ?_⟩
  have coefSummable : Summable (normalizedMikhlinCubeCoefficient m s) := by
    apply Summable.of_norm_bounded (((summable_spatial_lattice_weighted_decay 8 0 (by decide) (by decide)).mul_left (K * D))) _
    intro k
    simpa only [pow_zero, mul_one_div] using decay k
  intro ξ hlo hhi
  have near : ξ ∈ spatialFourierCube 5 := closed_ball_subset_spatial_fourier_cube 4 5 (by norm_num)
    (by rw [mem_closedBall, dist_zero_right]; linarith)
  have expansion := hasSum_spatial_cube_fourier_series 5 4 (by norm_num) (by norm_num) F hF.continuous SF coefSummable ξ near
  have exactF : F ξ = (m (s⁻¹ • ξ) : ℂ) := by simp only [F, g, order_zero_annular_extension_one ξ hlo hhi, one_mul]
  rw [exactF] at expansion
  apply expansion.congr_fun
  intro k
  rfl

end Burnett.A03
