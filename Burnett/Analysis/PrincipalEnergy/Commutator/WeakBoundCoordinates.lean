import Burnett.Analysis.PrincipalEnergy.Energy.CoordinateH1Energy
import Burnett.Analysis.PrincipalEnergy.Commutator.WeakBoundForm

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace Burnett.Analysis.SymmetricEnergy

open Filter MeasureTheory
open scoped InnerProductSpace SchwartzMap ENNReal ComplexConjugate

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

def scalarSchwartzMultiplier (r : 𝓢(Space, ℂ)) : 𝓢(Space, F) →ₗ[ℂ] 𝓢(Space, F) :=
  (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℂ ℂ).flip r.hasTemperateGrowth).toLinearMap

@[simp] theorem scalarSchwartzMultiplier_apply (r : 𝓢(Space, ℂ)) (f : 𝓢(Space, F)) (z : Space) :
    scalarSchwartzMultiplier r f z = r z • f z := rfl

private theorem scalarSchwartzMultiplier_isSymmetric (r : 𝓢(Space, ℂ))
    (hr : ∀ z : Space, conj (r z) = r z) :
    (transportSchwartzOp (scalarSchwartzMultiplier (F := F) r)).IsSymmetric := by
  intro u v
  obtain ⟨f, rfl⟩ := schwartzTestEquiv.surjective u
  obtain ⟨g, rfl⟩ := schwartzTestEquiv.surjective v
  simp only [transportSchwartzOp_on_equiv, schwartzTestEquiv_inner, scalarSchwartzMultiplier_apply]
  apply integral_congr_ae
  filter_upwards with z
  rw [inner_smul_left, inner_smul_right, hr z]

private theorem scalar_identity_symmetric (c : ℂ) (hc : conj c = c) :
    (c • (1 : Op (SchwartzTest F))).IsSymmetric := by
  intro u v
  change ⟪c • u, v⟫_ℂ = ⟪u, c • v⟫_ℂ
  rw [inner_smul_left, inner_smul_right, hc]

/-- On a test supported in a single ball, subtracting the coefficient at
the center makes the genuine multiplier small in its original L² norm. -/
theorem centeredScalarMultiplier_ball_norm_le (r : 𝓢(Space, ℂ)) (L : NNReal)
    (hr : LipschitzWith L r) (c : Space) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (f : 𝓢(Space, F)) (hf : tsupport (f : Space → F) ⊆ Metric.closedBall c ρ) :
    ‖((transportSchwartzOp (scalarSchwartzMultiplier (F := F) r) - r c • 1) : Op (SchwartzTest F))
        (schwartzTestEquiv f)‖ ≤ ((L : ℝ) * ρ) * ‖schwartzTestEquiv f‖ := by
  let C := scalarSchwartzMultiplier (F := F) r f - r c • f
  have hC : ((transportSchwartzOp (scalarSchwartzMultiplier (F := F) r) - r c • 1) : Op (SchwartzTest F))
        (schwartzTestEquiv f) = schwartzTestEquiv C := by
    simp only [C, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      transportSchwartzOp_on_equiv, map_sub, map_smul]
  rw [hC]
  change ‖C.toLp 2 volume‖ ≤ _ * ‖f.toLp 2 volume‖
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
  let A := (L : ℝ) * ρ
  have hA : 0 ≤ A := mul_nonneg L.coe_nonneg hρ
  apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg hA ENNReal.toReal_nonneg)
  rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_toReal (f.memLp 2 volume).eLpNorm_ne_top]
  let Apos : NNReal := ⟨A,hA⟩
  have hPoint : ∀ᵐ z ∂(volume : Measure Space), ‖C z‖₊ ≤ Apos * ‖f z‖₊ := by
    filter_upwards with z
    have hval : C z = (r z-r c) • f z := by
      simp only [C, SchwartzMap.sub_apply, SchwartzMap.smul_apply, scalarSchwartzMultiplier_apply, sub_smul]
    have hNorm : ‖C z‖ ≤ (Apos : ℝ) * ‖f z‖ := by
      by_cases hz : f z = 0
      · simp [hval, hz]
      have hm : z ∈ Metric.closedBall c ρ := hf (subset_closure hz)
      have hRad : ‖z-c‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hm
      have hLip : ‖r z-r c‖ ≤ (L : ℝ) * ‖z-c‖ := by
        simpa only [dist_eq_norm] using hr.dist_le_mul z c
      rw [hval, norm_smul]
      exact mul_le_mul_of_nonneg_right (hLip.trans (mul_le_mul_of_nonneg_left hRad L.coe_nonneg)) (norm_nonneg _)
    exact_mod_cast hNorm
  have hNN : (Apos : ℝ≥0∞) = ENNReal.ofReal A := ENNReal.ofReal_coe_nnreal.symm
  simpa only [ENNReal.smul_def, smul_eq_mul, hNN] using eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hPoint 2

/-- An actual local weak bound with shared supports and a first-order map
on the same test domain. It uses a single subtraction of `r` at the center. -/
theorem coordinate_commutator_weakPair_bound (r : 𝓢(Space, ℂ)) (L : NNReal)
    (hReal : ∀ z : Space, conj (r z) = r z) (hLip : LipschitzWith L r)
    (B : 𝓢(Space, F) →ₗ[ℂ] 𝓢(Space, F)) (hSym : (transportSchwartzOp B).IsSymmetric)
    (K : ℝ) (hMap : ∀ u : 𝓢(Space, F), ‖(B u).toLp 2 volume‖ ≤ K * coordinateH1 u)
    (c : Space) (ρ : ℝ) (hρ : 0 ≤ ρ) (f g : 𝓢(Space, F))
    (hf : tsupport (f : Space → F) ⊆ Metric.closedBall c ρ)
    (hg : tsupport (g : Space → F) ⊆ Metric.closedBall c ρ) :
    ‖∫ x, ⟪scalarSchwartzMultiplier r (B f) x - B (scalarSchwartzMultiplier r f) x, g x⟫_ℂ‖ ≤
      K * ((L : ℝ) * ρ) * (coordinateH1 f * ‖g.toLp 2 volume‖ + ‖f.toLp 2 volume‖ * coordinateH1 g) := by
  let R := transportSchwartzOp (scalarSchwartzMultiplier (F := F) r)
  let T := transportSchwartzOp B
  have hR : (R - r c • (1 : Op (SchwartzTest F))).IsSymmetric :=
    (scalarSchwartzMultiplier_isSymmetric r hReal).sub (scalar_identity_symmetric (r c) (hReal c))
  have hT (u : SchwartzTest F) : ‖T u‖ ≤ K * firstOrderEnergy coordinatePartial u := by
    obtain ⟨v, rfl⟩ := schwartzTestEquiv.surjective u
    change ‖transportSchwartzOp B (schwartzTestEquiv v)‖ ≤ _
    rw [firstOrderEnergy_eq_coordinateH1, transportSchwartzOp_on_equiv]
    exact hMap v
  have h := symmetric_commutator_weakPair_bound coordinatePartial R T _ hR hSym K hT
    (schwartzTestEquiv f) (schwartzTestEquiv g) _ (mul_nonneg L.coe_nonneg hρ)
    (centeredScalarMultiplier_ball_norm_le r L hLip c ρ hρ f hf)
    (centeredScalarMultiplier_ball_norm_le r L hLip c ρ hρ g hg)
  simpa only [R, T, comm, LinearMap.sub_apply, Module.End.mul_apply, transportSchwartzOp_on_equiv,
    ← map_sub, schwartzTestEquiv_inner, SchwartzMap.sub_apply, firstOrderEnergy_eq_coordinateH1] using h

end Burnett.Analysis.SymmetricEnergy
