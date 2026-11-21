import Burnett.Analysis.PrincipalEnergy.Commutator.NormalizedWeakBound

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.Analysis.SymmetricEnergy

open Filter MeasureTheory
open scoped InnerProductSpace SchwartzMap ComplexConjugate BigOperators ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

private theorem scalarMultiplier_toLp_norm_le (r : 𝓢(Space, ℂ)) (U : ℝ) (hU : 0 ≤ U)
    (h : ∀ z, ‖r z‖ ≤ U) (f : 𝓢(Space, F)) :
    ‖(scalarSchwartzMultiplier r f).toLp 2 volume‖ ≤ U * ‖f.toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
  apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg hU ENNReal.toReal_nonneg)
  rw [ENNReal.ofReal_mul hU, ENNReal.ofReal_toReal (f.memLp 2 volume).eLpNorm_ne_top]
  let A : NNReal := ⟨U,hU⟩
  have hPt : ∀ᵐ z ∂(volume : Measure Space), ‖scalarSchwartzMultiplier r f z‖₊ ≤ A * ‖f z‖₊ := by
    filter_upwards with z
    have hb : ‖scalarSchwartzMultiplier r f z‖ ≤ (A : ℝ) * ‖f z‖ := by
      rw [scalarSchwartzMultiplier_apply, norm_smul]
      exact mul_le_mul_of_nonneg_right (h z) (norm_nonneg _)
    exact_mod_cast hb
  have hCo : (A : ℝ≥0∞) = ENNReal.ofReal U := ENNReal.ofReal_coe_nnreal.symm
  simpa only [ENNReal.smul_def, smul_eq_mul, hCo] using eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hPt 2

private theorem boundedScalarMultiplier_isSymmetric (r : 𝓢(Space, ℂ))
    (hr : ∀ z : Space, conj (r z) = r z) :
    (transportSchwartzOp (scalarSchwartzMultiplier (F := F) r)).IsSymmetric := by
  intro u v
  obtain ⟨f, rfl⟩ := schwartzTestEquiv.surjective u
  obtain ⟨g, rfl⟩ := schwartzTestEquiv.surjective v
  simp only [transportSchwartzOp_on_equiv, schwartzTestEquiv_inner, scalarSchwartzMultiplier_apply]
  apply integral_congr_ae
  filter_upwards with z
  rw [inner_smul_left, inner_smul_right, hr z]

theorem normalizedLargeBallTest_norms (f : 𝓢(Space, F)) (c : Space) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hf : tsupport (f : Space → F) ⊆ Metric.closedBall c ρ) (hf₀ : ∀ x, ‖f x‖ ≤ 1)
    (hf₁ : ∀ (j : Fin 4) x, ‖fderiv ℝ (⇑f) x (coordinateDirection j)‖ ≤ ρ⁻¹) :
    ‖f.toLp 2 volume‖ ≤ ρ^2 * Real.sqrt unitBallVolume ∧
      coordinateH1 f ≤ ρ^2 * Real.sqrt (5*unitBallVolume) := by
  have hρ₀ := zero_le_one.trans hρ
  have hBound (g : 𝓢(Space, F)) (hg : tsupport (g : Space → F) ⊆ Metric.closedBall c ρ)
      (h : ∀ x, ‖g x‖ ≤ 1) : ‖g.toLp 2 volume‖ ≤ ρ^2 * Real.sqrt unitBallVolume := by
    simpa only [one_mul] using schwartz_ball_norm_le g c ρ 1 hρ₀ zero_le_one hg h
  have hD (j : Fin 4) : ‖(SchwartzMap.pderivCLM ℂ (coordinateDirection j) f).toLp 2 volume‖ ≤
      ρ^2 * Real.sqrt unitBallVolume := by
    let v := SchwartzMap.pderivCLM ℂ (coordinateDirection j) f
    apply hBound v
    · apply closure_minimal _ Metric.isClosed_closedBall
      intro z hz
      apply hf (support_fderiv_subset ℝ ?_)
      intro hz'
      exact hz (by simp only [v, SchwartzMap.pderivCLM_apply, hz', ContinuousLinearMap.zero_apply])
    · intro z
      exact ((hf₁ j z).trans (inv_le_one_of_one_le₀ hρ) : ‖v z‖ ≤ 1)
  refine ⟨hBound f hf hf₀,?_⟩
  have hSquare (g : 𝓢(Space, F)) (h : ‖g.toLp 2 volume‖ ≤ ρ^2 * Real.sqrt unitBallVolume) :
      ‖g.toLp 2 volume‖^2 ≤ ρ^4 * unitBallVolume := by
    simpa only [mul_pow, ← pow_mul, Nat.reduceMul, Real.sq_sqrt unitBallVolume_nonneg] using
      pow_le_pow_left₀ (norm_nonneg _) h 2
  have hSum : (∑ j : Fin 4, ‖(SchwartzMap.pderivCLM ℂ (coordinateDirection j) f).toLp 2 volume‖^2) ≤
      4 * (ρ^4 * unitBallVolume) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using
      (Finset.sum_le_sum fun j _ => hSquare _ (hD j))
  unfold coordinateH1
  calc
    _ ≤ Real.sqrt (ρ^4 * unitBallVolume + 4 * (ρ^4 * unitBallVolume)) :=
      Real.sqrt_le_sqrt (add_le_add (hSquare f (hBound f hf hf₀)) hSum)
    _ = ρ^2 * Real.sqrt (5*unitBallVolume) := by
      rw [show ρ^4 * unitBallVolume + 4 * (ρ^4 * unitBallVolume) = (ρ^2)^2 * (5*unitBallVolume) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]

theorem coordinate_commutator_largeBall_weakBound (r : 𝓢(Space, ℂ)) (U : ℝ)
    (hReal : ∀ z : Space, conj (r z) = r z) (hU : 0 ≤ U) (hBound : ∀ z, ‖r z‖ ≤ U)
    (B : 𝓢(Space, F) →ₗ[ℂ] 𝓢(Space, F)) (hSym : (transportSchwartzOp B).IsSymmetric)
    (K : ℝ) (hK : 0 ≤ K) (hMap : ∀ u : 𝓢(Space, F), ‖(B u).toLp 2 volume‖ ≤ K * coordinateH1 u)
    (c : Space) (ρ : ℝ) (hρ : 1 ≤ ρ) (f g : 𝓢(Space, F))
    (hf : tsupport (f : Space → F) ⊆ Metric.closedBall c ρ)
    (hg : tsupport (g : Space → F) ⊆ Metric.closedBall c ρ)
    (hf₀ : ∀ x, ‖f x‖ ≤ 1) (hg₀ : ∀ x, ‖g x‖ ≤ 1)
    (hf₁ : ∀ (j : Fin 4) x, ‖fderiv ℝ (⇑f) x (coordinateDirection j)‖ ≤ ρ⁻¹)
    (hg₁ : ∀ (j : Fin 4) x, ‖fderiv ℝ (⇑g) x (coordinateDirection j)‖ ≤ ρ⁻¹) :
    ‖∫ x, ⟪scalarSchwartzMultiplier r (B f) x - B (scalarSchwartzMultiplier r f) x, g x⟫_ℂ‖ ≤
      2 * K * U * Real.sqrt (5*unitBallVolume) * Real.sqrt unitBallVolume * ρ^4 := by
  obtain ⟨hfL, hfH⟩ := normalizedLargeBallTest_norms f c ρ hρ hf hf₀ hf₁
  obtain ⟨hgL, hgH⟩ := normalizedLargeBallTest_norms g c ρ hρ hg hg₀ hg₁
  let R := transportSchwartzOp (scalarSchwartzMultiplier (F := F) r)
  let T := transportSchwartzOp B
  have hR : (R - (0 : ℂ) • (1 : Op (SchwartzTest F))).IsSymmetric := by
    simpa only [zero_smul, sub_zero, R] using boundedScalarMultiplier_isSymmetric (F := F) r hReal
  have hT (u : SchwartzTest F) : ‖T u‖ ≤ K * firstOrderEnergy coordinatePartial u := by
    obtain ⟨v, rfl⟩ := schwartzTestEquiv.surjective u
    change ‖transportSchwartzOp B (schwartzTestEquiv v)‖ ≤ _
    rw [firstOrderEnergy_eq_coordinateH1, transportSchwartzOp_on_equiv]
    exact hMap v
  have hU0 (u : 𝓢(Space, F)) : ‖(R - (0 : ℂ) • (1 : Op (SchwartzTest F))) (schwartzTestEquiv u)‖ ≤
      U * ‖schwartzTestEquiv u‖ := by
    simpa only [zero_smul, sub_zero, R, transportSchwartzOp_on_equiv] using
      scalarMultiplier_toLp_norm_le r U hU hBound u
  have h := symmetric_commutator_weakPair_bound coordinatePartial R T (0 : ℂ) hR hSym K hT
    (schwartzTestEquiv f) (schwartzTestEquiv g) U hU (hU0 f) (hU0 g)
  have hSpatial : ‖∫ x, ⟪scalarSchwartzMultiplier r (B f) x - B (scalarSchwartzMultiplier r f) x, g x⟫_ℂ‖ ≤
      K * U * (coordinateH1 f * ‖g.toLp 2 volume‖ + ‖f.toLp 2 volume‖ * coordinateH1 g) := by
    simpa only [R, T, comm, LinearMap.sub_apply, Module.End.mul_apply, transportSchwartzOp_on_equiv,
      ← map_sub, schwartzTestEquiv_inner, SchwartzMap.sub_apply, firstOrderEnergy_eq_coordinateH1] using h
  have h₁ := mul_le_mul hfH hgL (norm_nonneg _) (by positivity : 0 ≤ ρ^2 * Real.sqrt (5*unitBallVolume))
  have h₂ := mul_le_mul hfL hgH (Real.sqrt_nonneg _) (by positivity : 0 ≤ ρ^2 * Real.sqrt unitBallVolume)
  exact hSpatial.trans ((mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity)).trans_eq (by ring))

/-- Weak boundedness for every ball radius, combining the local Lipschitz
gain with the global boundedness of the same coefficient. -/
theorem coordinate_commutator_allBalls_weakBound (r : 𝓢(Space, ℂ)) (L : NNReal) (U : ℝ)
    (hReal : ∀ z : Space, conj (r z) = r z) (hLip : LipschitzWith L r) (hU : 0 ≤ U)
    (hBound : ∀ z, ‖r z‖ ≤ U)
    (B : 𝓢(Space, F) →ₗ[ℂ] 𝓢(Space, F)) (hSym : (transportSchwartzOp B).IsSymmetric)
    (K : ℝ) (hK : 0 ≤ K) (hMap : ∀ u : 𝓢(Space, F), ‖(B u).toLp 2 volume‖ ≤ K * coordinateH1 u)
    (c : Space) (ρ : ℝ) (hρ : 0 < ρ) (f g : 𝓢(Space, F))
    (hf : tsupport (f : Space → F) ⊆ Metric.closedBall c ρ)
    (hg : tsupport (g : Space → F) ⊆ Metric.closedBall c ρ)
    (hf₀ : ∀ x, ‖f x‖ ≤ 1) (hg₀ : ∀ x, ‖g x‖ ≤ 1)
    (hf₁ : ∀ (j : Fin 4) x, ‖fderiv ℝ (⇑f) x (coordinateDirection j)‖ ≤ ρ⁻¹)
    (hg₁ : ∀ (j : Fin 4) x, ‖fderiv ℝ (⇑g) x (coordinateDirection j)‖ ≤ ρ⁻¹) :
    ‖∫ x, ⟪scalarSchwartzMultiplier r (B f) x - B (scalarSchwartzMultiplier r f) x, g x⟫_ℂ‖ ≤
      2 * K * ((L : ℝ) + U) * Real.sqrt (5*unitBallVolume) * Real.sqrt unitBallVolume * ρ^4 := by
  have mono {x y : ℝ} (hxy : x ≤ y) :
      2 * K * x * Real.sqrt (5*unitBallVolume) * Real.sqrt unitBallVolume * ρ^4 ≤
        2 * K * y * Real.sqrt (5*unitBallVolume) * Real.sqrt unitBallVolume * ρ^4 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hxy (by positivity)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (by positivity)
  by_cases hs : ρ ≤ 1
  · exact (coordinate_commutator_normalizedBall_weakBound r L hReal hLip B hSym K hK hMap c ρ hρ hs
      f g hf hg hf₀ hg₀ hf₁ hg₁).trans (mono (le_add_of_nonneg_right hU))
  · exact (coordinate_commutator_largeBall_weakBound r U hReal hU hBound B hSym K hK hMap c ρ (le_of_not_ge hs)
      f g hf hg hf₀ hg₀ hf₁ hg₁).trans (mono (le_add_of_nonneg_left L.coe_nonneg))

end Burnett.Analysis.SymmetricEnergy
