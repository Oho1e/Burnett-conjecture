import Burnett.Counterexamples.RotatingNull.ScaledCutoffs
import Burnett.Counterexamples.RotatingNull.SpacetimeSplit
import Burnett.Counterexamples.RotatingNull.TimeIntegral

/-!
# Genuine spacetime cutoffs for the large-spatial-radius contradiction

The Cartesian split is separately constructed as a continuous linear
equivalence. Its inverse transports compact product support to Euclidean
R4, and its spatial CLM has the actual standard-basis derivatives.
The previously proved volume-preserving measurable split supplies real
Fubini integrals. These are two proved properties of the same explicit
coordinates, not assumed volume or derivative fields.

The true Frechet product and chain rules give D0(phi_R) and the summed
spatial derivative bound by beta_R, with one constant valid at every
positive R. Both cutoffs are smooth, compact, time supported as required,
and genuinely integrable. Weighted time integrals and beta_R have their
exact R3 scaling; the actual one-dimensional IBP is consumed to compute
the four-dimensional temporal integral with its negative sign.
-/


noncomputable section
namespace Burnett.RotatingNullMoments.SpacetimeCutoffs
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open Set MeasureTheory
open scoped ContDiff Topology BigOperators
open Burnett.RotatingNullMoments.ScaledCutoffs

abbrev Base := Burnett.CubicExplicit.Space
abbrev Spatial := EuclideanSpace ℝ (Fin 3)

/-- A genuine continuous linear splitting of the four Cartesian coordinates. -/
def splitL : Base ≃L[ℝ] ℝ × Spatial :=
  (EuclideanSpace.equiv (Fin 4) ℝ).trans
    ((Fin.consLinearEquiv ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearEquiv.trans
      ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (EuclideanSpace.equiv (Fin 3) ℝ).symm))

theorem splitL_apply (x : Base) : splitL x = (x 0, WithLp.toLp 2 (fun j : Fin 3 => x j.succ)) := rfl

/-- The spatial projection is a true CLM, not an assumed derivative. -/
def rest : Base →L[ℝ] Spatial :=
  (ContinuousLinearMap.snd ℝ ℝ Spatial).comp splitL.toContinuousLinearMap

theorem rest_apply (x : Base) : rest x = WithLp.toLp 2 (fun j : Fin 3 => x j.succ) := rfl

theorem rest_basis_time : rest (Burnett.CubicExplicit.basis 0) = 0 := by
  ext j
  simp [rest_apply, Burnett.CubicExplicit.basis, EuclideanSpace.single_apply]

theorem rest_basis_spatial (j : Fin 3) :
    rest (Burnett.CubicExplicit.basis j.succ) = EuclideanSpace.single j 1 := by
  ext k
  simp [rest_apply, Burnett.CubicExplicit.basis, EuclideanSpace.single_apply]

def separated (χ : ℝ → ℝ) (η : Spatial → ℝ) (x : Base) : ℝ := χ (x 0) * η (rest x)

theorem separated_smooth (χ : ℝ → ℝ) (η : Spatial → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η) : ContDiff ℝ ∞ (separated χ η) :=
  (hχ.comp (Burnett.CubicExplicit.coord 0).contDiff).mul (hη.comp rest.contDiff)

theorem separated_compactSupport (χ : ℝ → ℝ) (η : Spatial → ℝ)
    (hχ : HasCompactSupport χ) (hη : HasCompactSupport η) : HasCompactSupport (separated χ η) := by
  have hp : HasCompactSupport (fun p : ℝ × Spatial => χ p.1 * η p.2) := by
    apply HasCompactSupport.intro (hχ.prod hη)
    intro p hp
    by_cases ht : p.1 ∈ tsupport χ
    · have hy : p.2 ∉ tsupport η := fun hy => hp ⟨ht, hy⟩
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
  exact hp.comp_homeomorph splitL.toHomeomorph

theorem separated_time_support (χ : ℝ → ℝ) (η : Spatial → ℝ) (I : Set ℝ)
    (hχ : tsupport χ ⊆ I) : tsupport (separated χ η) ⊆ {x | x 0 ∈ I} := by
  have hs : tsupport (separated χ η) ⊆ (fun x : Base => x 0) ⁻¹' tsupport χ := by
    apply closure_minimal
    · intro x hx
      by_contra ht
      exact hx (by unfold separated; rw [image_eq_zero_of_notMem_tsupport ht, zero_mul])
    · exact (isClosed_tsupport χ).preimage (Burnett.CubicExplicit.coord 0).continuous
  exact fun x hx => hχ (hs hx)

theorem separated_integrable (χ : ℝ → ℝ) (η : Spatial → ℝ)
    (hχ : Integrable χ) (hη : Integrable η) : Integrable (separated χ η) :=
  Burnett.RotatingNullSpacetime.integrable_separated χ η hχ hη

theorem separated_integral (χ : ℝ → ℝ) (η : Spatial → ℝ) :
    (∫ x, separated χ η x) = (∫ t, χ t) * ∫ y, η y :=
  Burnett.RotatingNullSpacetime.integral_separated χ η

theorem separated_D_time (χ : ℝ → ℝ) (η : Spatial → ℝ)
    (hχ : Differentiable ℝ χ) (hη : Differentiable ℝ η) (x : Base) :
    Burnett.CubicExplicit.D 0 (separated χ η) x = deriv χ (x 0) * η (rest x) := by
  have ht : HasFDerivAt (fun y : Base => χ (y 0))
      ((fderiv ℝ χ (x 0)).comp (Burnett.CubicExplicit.coord 0)) x :=
    (hχ _).hasFDerivAt.comp x (Burnett.CubicExplicit.coord 0).hasFDerivAt
  have hy : HasFDerivAt (fun y : Base => η (rest y)) ((fderiv ℝ η (rest x)).comp rest) x :=
    (hη _).hasFDerivAt.comp x rest.hasFDerivAt
  have h : HasFDerivAt (separated χ η) _ x := ht.mul hy
  unfold Burnett.CubicExplicit.D
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply]
  rw [rest_basis_time]
  simp [Burnett.CubicExplicit.coord_apply, Burnett.CubicExplicit.basis_apply]
  ring

theorem separated_D_spatial (χ : ℝ → ℝ) (η : Spatial → ℝ)
    (hχ : Differentiable ℝ χ) (hη : Differentiable ℝ η) (j : Fin 3) (x : Base) :
    Burnett.CubicExplicit.D j.succ (separated χ η) x = χ (x 0) * directional j η (rest x) := by
  have ht : HasFDerivAt (fun y : Base => χ (y 0))
      ((fderiv ℝ χ (x 0)).comp (Burnett.CubicExplicit.coord 0)) x :=
    (hχ _).hasFDerivAt.comp x (Burnett.CubicExplicit.coord 0).hasFDerivAt
  have hy : HasFDerivAt (fun y : Base => η (rest y)) ((fderiv ℝ η (rest x)).comp rest) x :=
    (hη _).hasFDerivAt.comp x rest.hasFDerivAt
  have h : HasFDerivAt (separated χ η) _ x := ht.mul hy
  unfold Burnett.CubicExplicit.D
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply]
  rw [rest_basis_spatial]
  simp [Burnett.CubicExplicit.coord_apply, Burnett.CubicExplicit.basis_apply, directional, Ne.symm (Fin.succ_ne_zero j)]

def phi (χ : ℝ → ℝ) (R : ℝ) : Base → ℝ := separated χ (scale R spatialBump)

def beta (χ : ℝ → ℝ) (C R : ℝ) (x : Base) : ℝ :=
  χ (x 0) * (C/R) * scale R majorantBump (rest x)

theorem phi_smooth (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (R : ℝ) : ContDiff ℝ ∞ (phi χ R) :=
  separated_smooth χ _ hχ (smooth_scale R _ spatialBump.contDiff)

theorem phi_compactSupport (χ : ℝ → ℝ) (hc : HasCompactSupport χ) (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (phi χ R) :=
  separated_compactSupport χ _ hc (compactSupport_scale R hR.ne' _ spatialBump.hasCompactSupport)

theorem phi_time_support (χ : ℝ → ℝ) (I : Set ℝ) (hχ : tsupport χ ⊆ I) (R : ℝ) :
    tsupport (phi χ R) ⊆ {x | x 0 ∈ I} := separated_time_support χ _ I hχ

theorem beta_eq_separated (χ : ℝ → ℝ) (C R : ℝ) :
    beta χ C R = separated (fun t => χ t * (C/R)) (scale R majorantBump) := rfl

theorem beta_smooth (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (C R : ℝ) :
    ContDiff ℝ ∞ (beta χ C R) := by
  rw [beta_eq_separated]
  exact separated_smooth _ _ (hχ.mul contDiff_const) (smooth_scale R _ majorantBump.contDiff)

theorem beta_compactSupport (χ : ℝ → ℝ) (hc : HasCompactSupport χ) (C R : ℝ) (hR : 0 < R) :
    HasCompactSupport (beta χ C R) := by
  rw [beta_eq_separated]
  exact separated_compactSupport _ _ hc.mul_right (compactSupport_scale R hR.ne' _ majorantBump.hasCompactSupport)

theorem beta_nonneg (χ : ℝ → ℝ) (hn : ∀ t, 0 ≤ χ t) (C : ℝ) (hC : 0 ≤ C) (R : ℝ) (hR : 0 < R)
    (x : Base) : 0 ≤ beta χ C R x :=
  mul_nonneg (mul_nonneg (hn _) (div_nonneg hC hR.le)) majorantBump.nonneg

theorem phi_D_time (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (R : ℝ) (x : Base) :
    Burnett.CubicExplicit.D 0 (phi χ R) x = deriv χ (x 0) * scale R spatialBump (rest x) :=
  separated_D_time χ _ (hχ.differentiable (by simp))
    ((smooth_scale R _ spatialBump.contDiff).differentiable (by simp)) x

/-- The same constant works for every spatial scale and every base point. -/
theorem phi_spatial_majorant (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hn : ∀ t, 0 ≤ χ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ x : Base,
      (∑ j : Fin 3, |Burnett.CubicExplicit.D j.succ (phi χ R) x|) ≤ beta χ C R x := by
  obtain ⟨C, hC, hbound⟩ := scaled_spatial_derivative_majorant
  refine ⟨C, hC, ?_⟩
  intro R hR x
  change (∑ j : Fin 3, |Burnett.CubicExplicit.D j.succ (separated χ (scale R spatialBump)) x|) ≤ _
  simp_rw [separated_D_spatial χ _ (hχ.differentiable (by simp))
    ((smooth_scale R _ spatialBump.contDiff).differentiable (by simp)), abs_mul, abs_of_nonneg (hn (x 0))]
  rw [← Finset.mul_sum]
  change χ (x 0) * derivativeSum (scale R spatialBump) (rest x) ≤ _
  exact (mul_le_mul_of_nonneg_left (hbound R hR (rest x)) (hn _)).trans_eq (by unfold beta; ring)

theorem phi_integrable (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (R : ℝ) (hR : 0 < R) : Integrable (phi χ R) :=
  (phi_smooth χ hχ R).continuous.integrable_of_hasCompactSupport (phi_compactSupport χ hc R hR)

theorem beta_integrable (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (C R : ℝ) (hR : 0 < R) : Integrable (beta χ C R) :=
  (beta_smooth χ hχ C R).continuous.integrable_of_hasCompactSupport (beta_compactSupport χ hc C R hR)

theorem beta_time_support (χ : ℝ → ℝ) (I : Set ℝ) (hχ : tsupport χ ⊆ I) (C R : ℝ) :
    tsupport (beta χ C R) ⊆ {x | x 0 ∈ I} := by
  rw [beta_eq_separated]
  apply separated_time_support _ _ I
  exact tsupport_mul_subset_left.trans hχ

theorem phi_cos_two_integrable (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (R : ℝ) (hR : 0 < R) :
    Integrable (fun x : Base => phi χ R x * Real.cos (2 * x 0)) := by
  have ht : Integrable (fun t : ℝ => χ t * Real.cos (2*t)) :=
    (hχ.continuous.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport hc.mul_right
  have h := separated_integrable _ (scale R spatialBump) ht
    (integrable_scale R hR.ne' _ spatialBump.contDiff spatialBump.hasCompactSupport)
  convert h using 1
  funext x
  unfold phi separated
  ring

theorem phi_cos_two_integral (χ : ℝ → ℝ) (R : ℝ) (hR : 0 < R) :
    (∫ x : Base, phi χ R x * Real.cos (2*x 0)) =
      R^3 * (∫ y : Spatial, spatialBump y) * (∫ t : ℝ, χ t * Real.cos (2*t)) := by
  have heq : (fun x : Base => phi χ R x * Real.cos (2*x 0)) =
      separated (fun t => χ t * Real.cos (2*t)) (scale R spatialBump) := by
    funext x
    unfold phi separated
    ring
  rw [heq, separated_integral, integral_scale R hR.le]
  ring

theorem beta_integral (χ : ℝ → ℝ) (C R : ℝ) (hR : 0 < R) :
    (∫ x : Base, beta χ C R x) =
      (C/R) * R^3 * (∫ y : Spatial, majorantBump y) * (∫ t : ℝ, χ t) := by
  rw [beta_eq_separated, separated_integral, integral_scale R hR.le, integral_mul_const]
  ring

theorem phi_temporal_integrable (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (R : ℝ) (hR : 0 < R) :
    Integrable (fun x : Base => Burnett.CubicExplicit.D 0 (phi χ R) x * (Real.cos (x 0) * Real.sin (x 0))) := by
  have ht : Integrable (fun t : ℝ => deriv χ t * (Real.cos t * Real.sin t)) :=
    ((hχ.continuous_deriv (by simp)).mul (Real.continuous_cos.mul Real.continuous_sin)).integrable_of_hasCompactSupport hc.deriv.mul_right
  have h := separated_integrable _ (scale R spatialBump) ht
    (integrable_scale R hR.ne' _ spatialBump.contDiff spatialBump.hasCompactSupport)
  convert h using 1
  funext x
  rw [phi_D_time χ hχ]
  unfold separated
  ring

theorem phi_temporal_integral (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (R : ℝ) (hR : 0 < R) :
    (∫ x : Base, Burnett.CubicExplicit.D 0 (phi χ R) x * (Real.cos (x 0) * Real.sin (x 0))) =
      -(R^3 * (∫ y : Spatial, spatialBump y) * (∫ t : ℝ, χ t * Real.cos (2*t))) := by
  have heq : (fun x : Base => Burnett.CubicExplicit.D 0 (phi χ R) x * (Real.cos (x 0) * Real.sin (x 0))) =
      separated (fun t => deriv χ t * (Real.cos t * Real.sin t)) (scale R spatialBump) := by
    funext x
    rw [phi_D_time χ hχ]
    unfold separated
    ring
  rw [heq, separated_integral, integral_scale R hR.le, Burnett.RotatingNullTime.time_integral_identity χ hχ hc]
  ring

end Burnett.RotatingNullMoments.SpacetimeCutoffs
