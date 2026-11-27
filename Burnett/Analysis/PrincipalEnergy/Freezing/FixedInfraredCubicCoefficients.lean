import Burnett.Analysis.PrincipalEnergy.Freezing.ActualFrozenCubicCoefficients
import Burnett.Analysis.PrincipalEnergy.Freezing.PrincipalCutoffErrorBounds
import Burnett.Analysis.PrincipalEnergy.Freezing.FrozenInfraredComparison
import Burnett.Analysis.TransportWard.Weyl.FixedInfraredTestDerivative

set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxRecDepth 4200

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol Burnett.A03
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open scoped ENNReal BigOperators ContDiff ComplexConjugate Burnett.A03

open private principal_variation_density_integrable from Burnett.Analysis.PrincipalEnergy.Freezing.FiniteModeEnergyLinearity

private theorem principalVariationDensity_congr_on_field_support {J : Type} [Fintype J]
    (C D : Index → Index → J → J → J → E → ℂ)
    (z : J → SchwartzMap E ℂ) (w : J → E → ℂ) (U : Set E)
    (hz : tsupport (fieldValueArray z) ⊆ U)
    (hC : ∀ a d i j k x, x ∈ U → C a d i j k x = D a d i j k x) :
    principalVariationDensity C z w = principalVariationDensity D z w := by
  have hSupport (i : J) : tsupport (z i : E → ℂ) ⊆ U := by
    apply (closure_mono ?_).trans hz
    intro x hx
    change z i x ≠ 0 at hx
    change fieldValueArray z x ≠ 0
    intro h
    exact hx (congrArg (fun v => v i) h)
  funext x
  by_cases hx : x ∈ U
  · simp only [principalVariationDensity, fun a d i j k => hC a d i j k x hx]
  · have hOff (i : J) : x ∉ tsupport (z i : E → ℂ) := fun hi => hx (hSupport i hi)
    have hv (i : J) : z i x = 0 := image_eq_zero_of_notMem_tsupport (hOff i)
    have hd (i : J) (a : Index) : energyPartial a (z i) x = 0 := by
      change fderiv ℝ (z i : E → ℂ) x (EuclideanSpace.single a 1) = 0
      rw [fderiv_of_notMem_tsupport ℝ (hOff i), ContinuousLinearMap.zero_apply]
    simp only [principalVariationDensity, hv, hd, mul_zero, zero_mul, add_zero, Finset.sum_const_zero]

private theorem principalVariationDensity_add_smooth_test {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℂ) (z : J → SchwartzMap E ℂ)
    (u v : J → E → ℂ) (hu : ∀ i, Differentiable ℝ (u i)) (hv : ∀ i, Differentiable ℝ (v i)) :
    principalVariationDensity C z (u + v) =
      principalVariationDensity C z u + principalVariationDensity C z v := by
  funext x
  have hD (i : J) (a : Index) :
      fderiv ℝ (u i + v i) x (EuclideanSpace.single a 1) =
        fderiv ℝ (u i) x (EuclideanSpace.single a 1) +
          fderiv ℝ (v i) x (EuclideanSpace.single a 1) := by
    rw [fderiv_add (hu i x) (hv i x), ContinuousLinearMap.add_apply]
  simp only [principalVariationDensity, Pi.add_apply, hD, add_mul, mul_add, Finset.sum_add_distrib]
  abel

private def compactRealCoefficient (q : E → ℝ)
    (hs : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) : SchwartzMap E ℂ :=
  (hc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hs)

/-- With the fixed infrared test, the coefficient freezing error retains the
homogeneous patch-scale bound and gains only an order-zero cubic placement. -/
theorem exists_fixedInfrared_coefficient_freezing_bound {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ)
    (hSmooth : ∀ a d i j k, ContDiff ℝ ∞ (C a d i j k))
    (hSymm : ∀ a d i j k, C a d i j k = C d a i k j)
    (R L M : ℝ) (hR : 0 < R) (hL : 0 ≤ L)
    (hGrad : ∀ a d i j k x, ‖fderiv ℝ (C a d i j k) x‖ ≤ L)
    (hValue : ∀ a d i j k x, ‖C a d i j k x‖ ≤ M)
    (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (D : ℝ) (hD : 0 ≤ D) :
    ∃ A B : ℝ≥0∞, A < ⊤ ∧ B < ⊤ ∧
      ∀ (c : E) (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
        (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) →
        (∀ ξ, b (-ξ) = -b ξ) →
        (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
        ∀ (ℓ : ℝ), 0 < ℓ → ∀ z : RealEnergyField J,
          tsupport (fieldValueArray z.val) ⊆ ball c (R * ℓ) →
          let β := fixedInfraredSymbol cut 0 b
          let w (i : J) (x : E) := (-Complex.I) * radianAction β (z.val i) x
          let F := principalVariationDensity (fun a d i j k x => (C a d i j k x : ℂ)) z.val w
          let F₀ := principalVariationDensity (fun a d i j k _ => (C a d i j k c : ℂ)) z.val w
          let X := euclideanFieldGradientNorm z.val
          let Y := eLpNorm (fieldValueArray z.val) (ENNReal.ofReal 3) volume
          Integrable F ∧ Integrable F₀ ∧
            ‖(∫ x, (F x).re) - (∫ x, (F₀ x).re)‖ₑ ≤
              A * ENNReal.ofReal ℓ * X ^ 3 + B * Y * X ^ 2 := by
  obtain ⟨_, A, _, _, hA, hFreeze⟩ := exists_actual_frozen_cubic_coefficient_bound C hSmooth hSymm R L hR hL hGrad
  obtain ⟨χ, _, _, _, _, hWindows, _⟩ := exists_nested_localized_coefficient_difference R hR.le
  obtain ⟨K, hK, hIR⟩ := exists_frozen_fixed_infrared_difference_W13 cut 0 hcut (fun _ => by simp) D hD
  let P : ℝ≥0∞ := Fintype.card (Index × Index × J × J × J) * ENNReal.ofReal (2 * M)
  have hP : P < ⊤ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ENNReal.ofReal_lt_top
  refine ⟨A * ENNReal.ofReal D, P * (3 * K), ENNReal.mul_lt_top hA ENNReal.ofReal_lt_top,
    ENNReal.mul_lt_top hP (ENNReal.mul_lt_top (by norm_num) hK), ?_⟩
  intro c b hb hom odd hJets ℓ hℓ z hz β w F F₀ X Y
  let Cvar (a d : Index) (i j k : J) (x : E) := (C a d i j k x : ℂ)
  let Cc (a d : Index) (i j k : J) (_ : E) := (C a d i j k c : ℂ)
  let θ (x : E) := χ (ℓ⁻¹ • (x - c))
  obtain ⟨hθ, hθc, hOne, _, _, _, hθJet, _⟩ := hWindows c ℓ hℓ
  have hPatch (x : E) (hx : x ∈ ball c (R * ℓ)) : θ x = 1 :=
    hOne x (ball_subset_closedBall.trans (closedBall_subset_closedBall (by nlinarith)) hx)
  let localize (q : E → ℝ) (hq : ContDiff ℝ ∞ q) : SchwartzMap E ℂ :=
    compactRealCoefficient (θ * q) (hθ.mul hq) hθc.mul_right
  have hLoc (q : E → ℝ) (hq : ContDiff ℝ ∞ q) (x : E) :
      localize q hq x = (θ x * q x : ℝ) := rfl
  let S (a d : Index) (i j k : J) := localize (C a d i j k) (hSmooth a d i j k)
  let S₀ (a d : Index) (i j k : J) := localize (fun _ => C a d i j k c) contDiff_const
  have equalOnPatch (q : E → ℝ) (hq : ContDiff ℝ ∞ q) (x : E) (hx : x ∈ ball c (R * ℓ)) :
      (q x : ℂ) = localize q hq x := by rw [hLoc q hq x, hPatch x hx, one_mul]
  have hWJet (i : J) : BoundedCoordinateJet (w i) :=
    fixedInfraredTest_global_coordinateBounds cut hcut b hb hom (z.val i)
  have intF : Integrable F := by
    change Integrable (principalVariationDensity Cvar z.val w)
    rw [principalVariationDensity_congr_on_field_support Cvar (fun a d i j k => S a d i j k) z.val w _ hz
      (fun a d i j k x hx => equalOnPatch (C a d i j k) (hSmooth a d i j k) x hx)]
    exact principal_variation_density_integrable S z.val w hWJet
  have intF₀ : Integrable F₀ := by
    change Integrable (principalVariationDensity Cc z.val w)
    rw [principalVariationDensity_congr_on_field_support Cc (fun a d i j k => S₀ a d i j k) z.val w _ hz
      (fun a d i j k x hx => equalOnPatch (fun _ => C a d i j k c) contDiff_const x hx)]
    exact principal_variation_density_integrable S₀ z.val w hWJet
  let Q (u : SchwartzMap E ℂ) := (-Complex.I) • (radianAction β u - radianAction b u)
  have hQ : SchwartzOrderZeroJetBound Q K 0 := by
    have h := hIR b hb hom (fun n hn => hJets n (hn.trans (by decide)))
    have hI : ‖(-Complex.I)‖ₑ = 1 := by rw [← ofReal_norm, norm_neg, Complex.norm_I, ENNReal.ofReal_one]
    simpa only [Q, hI, one_mul] using schwartz_order_zero_jet_bound_const_mul _ K 0 h (-Complex.I)
  let v (i : J) := Q (z.val i)
  let wHom (i : J) := radianSkewAction b (z.val i)
  have hWdiff : wHom = w - v := by
    funext i x
    change (-Complex.I) * radianAction b (z.val i) x =
      (-Complex.I) * radianAction β (z.val i) x -
        (-Complex.I) * (radianAction β (z.val i) x - radianAction b (z.val i) x)
    ring
  have hV (i : J) : Differentiable ℝ (v i) := (hQ (z.val i)).2.2.1
  have hHom (i : J) : Differentiable ℝ (wHom i) := by
    rw [hWdiff, Pi.sub_apply]
    exact (hWJet i).1.sub (hV i)
  have hWadd : w = wHom + v := by rw [hWdiff, sub_add_cancel]
  let Cdiff (a d : Index) (i j k : J) (x : E) := C a d i j k x - C a d i j k c
  let T (a d : Index) (i j k : J) := localize (Cdiff a d i j k) ((hSmooth a d i j k).sub contDiff_const)
  have hT (a d : Index) (i j k : J) : eLpNorm (T a d i j k : E → ℂ) ⊤ volume ≤ ENNReal.ofReal (2 * M) := by
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_bound
    refine Eventually.of_forall fun x => ?_
    rw [hLoc (Cdiff a d i j k) ((hSmooth a d i j k).sub contDiff_const) x, Complex.norm_real, norm_mul]
    have hdiff : ‖Cdiff a d i j k x‖ ≤ 2 * M :=
      (norm_sub_le _ _).trans (by linarith only [hValue a d i j k x, hValue a d i j k c])
    simpa only [one_mul] using mul_le_mul ((hθJet x).1) hdiff (norm_nonneg _) (show 0 ≤ (1 : ℝ) by norm_num)
  let Err := principalVariationDensity (fun a d i j k => T a d i j k) z.val v
  have hErr : principalVariationDensity Cvar z.val v - principalVariationDensity Cc z.val v = Err := by
    have hDiff : principalVariationDensity Cvar z.val v - principalVariationDensity Cc z.val v =
        principalVariationDensity (fun a d i j k x => (Cdiff a d i j k x : ℂ)) z.val v := by
      funext x
      simp only [principalVariationDensity, Cvar, Cc, Cdiff, Complex.ofReal_sub, Pi.sub_apply,
        sub_mul, Finset.sum_sub_distrib]
    rw [hDiff]
    exact principalVariationDensity_congr_on_field_support _ _ z.val v _ hz
      (fun a d i j k x hx => equalOnPatch (Cdiff a d i j k) ((hSmooth a d i j k).sub contDiff_const) x hx)
  obtain ⟨hZ, hDZ, _⟩ := separated_field_component_L3_bounds z.val
  have hErrBound := principalVariation_cutoff_error_integral_bound T z.val v (ENNReal.ofReal (2 * M))
    Y X (K * Y) (K * X) hT hZ (fun a i => hDZ (a,i))
    (fun i => ⟨(hQ (z.val i)).1, (hQ (z.val i)).2.1.trans (mul_le_mul_left' (hZ i) K)⟩)
    (fun a i => ⟨((hQ (z.val i)).2.2.2 a).1,
      (((hQ (z.val i)).2.2.2 a).2.trans_eq (by rw [zero_mul, add_zero])).trans
        (mul_le_mul_left' (hDZ (a,i)) K)⟩)
  let HomErr := principalVariationDensity Cvar z.val wHom - principalVariationDensity Cc z.val wHom
  have hSplit : F - F₀ = HomErr + Err := by
    change principalVariationDensity Cvar z.val w - principalVariationDensity Cc z.val w = _
    rw [hWadd, principalVariationDensity_add_smooth_test Cvar z.val wHom v hHom hV,
      principalVariationDensity_add_smooth_test Cc z.val wHom v hHom hV, ← hErr]
    dsimp only [HomErr]
    abel
  have intHom : Integrable HomErr := by
    have he : HomErr = F - F₀ - Err := by rw [hSplit, add_sub_cancel_right]
    rw [he]
    exact (intF.sub intF₀).sub hErrBound.1
  have hRaw : ‖∫ x, HomErr x‖ₑ ≤ A * ENNReal.ofReal D * ENNReal.ofReal ℓ * X ^ 3 :=
    (hFreeze c ℓ hℓ).2 b hb hom odd D hD hJets z.val z.property hz
  have hRegular : ‖∫ x, Err x‖ₑ ≤ P * (3 * K) * Y * X ^ 2 :=
    hErrBound.2.trans_eq (by dsimp only [P]; ring)
  refine ⟨intF, intF₀, ?_⟩
  have hRe : ‖(∫ x, (F x).re) - (∫ x, (F₀ x).re)‖ₑ ≤ ‖∫ x, (F - F₀) x‖ₑ := by
    have hReF : (∫ x, (F x).re) = (∫ x, F x).re := integral_re intF
    have hReF₀ : (∫ x, (F₀ x).re) = (∫ x, F₀ x).re := integral_re intF₀
    have hSub : (∫ x, (F - F₀) x) = (∫ x, F x) - ∫ x, F₀ x := integral_sub intF intF₀
    rw [hReF, hReF₀, ← Complex.sub_re, hSub, ← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm _)
  refine hRe.trans ?_
  have hSum : (∫ x, (HomErr + Err) x) = (∫ x, HomErr x) + ∫ x, Err x := integral_add intHom hErrBound.1
  rw [hSplit, hSum]
  exact (enorm_add_le _ _).trans (add_le_add hRaw hRegular)

end Burnett.V03.Palatini
