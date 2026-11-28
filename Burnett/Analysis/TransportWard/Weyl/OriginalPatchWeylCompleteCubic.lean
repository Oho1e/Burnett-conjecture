import Burnett.Analysis.PrincipalEnergy.Freezing.FiniteModeEnergyLinearity
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedWeylSymbolFreezeEnergy
import Burnett.Analysis.TransportWard.Weyl.AffinePatchWeylWindow
import Burnett.Analysis.TransportWard.Weyl.FixedInfraredCoefficientFreezing
import Burnett.Analysis.CubicEnergy.CompleteEnergy.UniformWeightedEuclidean

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4600

noncomputable section

namespace Burnett.V03.Palatini

open Filter Function Metric MeasureTheory Set Burnett.A03 Burnett.A02.FrequencySplit Burnett.RicciSymbol
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open Burnett.Analysis.TransportWardSymbol Burnett.C02
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff ENNReal BigOperators Topology Burnett.A03

open private principal_variation_density_integrable from Burnett.Analysis.PrincipalEnergy.Freezing.FiniteModeEnergyLinearity
open private principalVariationDensity_add_smooth_test from Burnett.Analysis.TransportWard.Weyl.FixedInfraredCoefficientFreezing

private theorem abs_cubic_freezing_of_enorm {J : Type} [Fintype J]
    (z : J → SchwartzMap E ℂ) (r ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (A D : ℝ≥0∞) (hA : A < ⊤) (hD : D < ⊤)
    (h : ‖r‖ₑ ≤ A * ENNReal.ofReal ℓ * euclideanFieldGradientNorm z ^ 3 +
      D * eLpNorm (fieldValueArray z) (ENNReal.ofReal 3) volume * euclideanFieldGradientNorm z ^ 2) :
    |r| ≤ A.toReal * ℓ * euclideanFieldGradientL3 z ^ 3 +
      D.toReal * euclideanFieldValueL3 z * euclideanFieldGradientL3 z ^ 2 := by
  have hX := euclideanFieldGradientNorm_lt_top z
  have hY := (fieldValueArray_memLp z (ENNReal.ofReal 3)).eLpNorm_lt_top
  have hLeft : A * ENNReal.ofReal ℓ * euclideanFieldGradientNorm z ^ 3 < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top hA ENNReal.ofReal_lt_top) (ENNReal.pow_lt_top hX)
  have hRight : D * eLpNorm (fieldValueArray z) (ENNReal.ofReal 3) volume * euclideanFieldGradientNorm z ^ 2 < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top hD hY) (ENNReal.pow_lt_top hX)
  have hn := ENNReal.toReal_mono (ENNReal.add_lt_top.mpr ⟨hLeft, hRight⟩).ne h
  simpa only [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg r),
    ENNReal.toReal_add hLeft.ne hRight.ne, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hℓ,
    euclideanFieldGradientL3, euclideanFieldValueL3] using hn

/-- Freeze the original Weyl symbol and the actual localized Euler coefficient
on the same C03 patch. The target is the complete energy with the prescribed
fixed infrared symbol at that center and the original field on the patch. -/
theorem exists_actualWeyl_completeCubic_patch_freezing
    (g : E → OrderedPair → ℝ) (ρ : E → ℝ) {U K₀ : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hMetric : ∀ x ∈ U, assembleMetricComponents frozenActionOrderedBasis (g x) ∈ nonsingularMetricDomain)
    (hρ : ContDiff ℝ ∞ ρ) (hρU : tsupport ρ ⊆ U) (hρc : HasCompactSupport ρ)
    (hOne : ∀ x ∈ K₀, ρ x = 1)
    (a : E → E → ℝ) (cut : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (K : Set E) (hK : IsCompact K)
    (hβ : ContDiff ℝ ∞ (uncurry fun x => fixedInfraredSymbol cut 0 (a x)))
    (hOff : ∀ x ∉ K, ∀ ξ, fixedInfraredSymbol cut 0 (a x) ξ = 0)
    (hHigh : ∀ x ξ, 1 < ‖ξ‖ → fixedInfraredSymbol cut 0 (a x) ξ = a x ξ)
    (hOdd : ∀ x ξ, a x (-ξ) = -a x ξ)
    (hHom : ∀ x (t : ℝ), 0 < t → ∀ ξ, a x (t • ξ) = t * a x ξ)
    (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ c ∈ K₀, ContDiffOn ℝ ∞ (a c) {ξ | ξ ≠ 0})
    (hJets : ∀ c ∈ K₀, ∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n (a c) ξ‖ ≤ D)
    (hβOdd : ∀ c ∈ K₀, ∀ ξ, fixedInfraredSymbol cut 0 (a c) (-ξ) = -fixedInfraredSymbol cut 0 (a c) ξ)
    (B : SchwartzMap E ℂ → E → ℂ)
    (hB : ∀ u, ∃ v : SchwartzMap E ℂ, (v : E → ℂ) = B u)
    (hCompare : ∀ (Θ : SchwartzMap E ℂ) (η : E → SchwartzMap E ℂ) (ℓ : ℝ), 0 < ℓ →
      (∀ c x, η c x = Θ (ℓ⁻¹ • (x - c))) →
      ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ c, SchwartzOrderZeroJetBound
        (fun u => (-Complex.I) •
          (sandwichedScalarTest (η c) (fun v => B v - radianAction (fixedInfraredSymbol cut 0 (a c)) v) u -
            radianLeftQuantization (localizedFrozenPrincipalSymbol a c (η c)) u)) A A) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 →
      ∃ Dℓ : ℝ, 0 ≤ Dℓ ∧ ∀ c ∈ K₀, ∀ z : RealEnergyField OrderedPair,
        tsupport (fieldValueArray z.val) ⊆ closedBall c (4 * ℓ) →
        let C (d e : Index) (i j k : OrderedPair) (x : E) :=
          Complex.ofReal (localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis g ρ d e i j k x)
        let F := principalVariationDensity C z.val (fun i x => (-Complex.I) * B (z.val i) x)
        let G := assembleMetricComponents frozenActionOrderedBasis (g c)
        let β := fixedInfraredSymbol cut 0 (a c)
        let X := euclideanFieldGradientL3 z.val
        let Y := euclideanFieldValueL3 z.val
        Integrable F ∧ |(∫ x, (F x).re) -
          completeCubicEnergy (frozenActionCubicLinear G) (frozenActionCubicQuadratic G) β z| ≤
            A * ℓ * X ^ 3 + Dℓ * Y * X ^ 2 := by
  let J := OrderedPair
  let C := localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis g ρ
  obtain ⟨hSmooth, hSupport, hSwap, _, _⟩ :=
    localizedEulerPrincipalVariationCoefficient_properties frozenActionOrderedBasis g ρ hU hg hMetric hρ hρU hρc hOne
  have hCompact (d e : Index) (i j k : J) : HasCompactSupport (C d e i j k) :=
    hρc.of_isClosed_subset isClosed_closure (hSupport d e i j k)
  let S (d e : Index) (i j k : J) : SchwartzMap E ℂ :=
    ((hCompact d e i j k).comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (hSmooth d e i j k))
  have hS (d e : Index) (i j k : J) (x : E) : S d e i j k x = (C d e i j k x : ℂ) := rfl
  have hSymm (d e : Index) (i j k : J) : S d e i j k = S e d i k j := by
    ext x
    rw [hS, hS]
    exact congrArg (fun f : E → ℝ => (f x : ℂ)) (hSwap d e i j k)
  let I := Index × Index × J × J × J
  let s (j : I) := SchwartzMap.seminorm ℝ 0 0 (S j.1 j.2.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2)
  let M : ℝ := ∑ j : I, s j
  have hSup (d e : Index) (i j k : J) : eLpNorm (S d e i j k : E → ℂ) ⊤ volume ≤ ENNReal.ofReal M := by
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_bound
    refine Eventually.of_forall fun x => ?_
    have hSem : ‖S d e i j k x‖ ≤ s (d,e,i,j,k) := by
      simpa only [s, pow_zero, one_mul, norm_iteratedFDeriv_zero] using SchwartzMap.le_seminorm ℝ 0 0 (S d e i j k) x
    exact hSem.trans (Finset.single_le_sum (f := s) (fun _ _ => apply_nonneg _ _) (Finset.mem_univ (d,e,i,j,k)))
  obtain ⟨φ, Θ, η, hφ, hφSupp, _, hη⟩ := exists_affineWeylPatchWindow
  let β (c ξ : E) := fixedInfraredSymbol cut 0 (a c) ξ
  let B₀ (c : E) := radianAction (β c)
  have hRem (ℓ : ℝ) (hℓ : 0 < ℓ) := hCompare Θ (fun c => η c ℓ) ℓ hℓ
    (fun c x => (hη c ℓ hℓ).1 x)
  obtain ⟨A, hA, hFreezeSymbol⟩ := exists_localizedWeyl_frozen_symbol_energy_bound S hSymm
    (ENNReal.ofReal M) ENNReal.ofReal_lt_top hSup a β K hK hβ hOff hHigh hOdd hHom φ hφ 6 7 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hφSupp η
    (fun c ℓ x hℓ => (hη c ℓ hℓ).2.1 x) B B₀ hRem
  obtain ⟨A₀, D₀, hA₀, hD₀, hFreezeCoef⟩ :=
    exists_localizedEulerPrincipalVariation_fixedInfrared_freezing_bound g ρ hU hg hMetric hρ hρU hρc
      hOne a cut hcut 5 D (by norm_num) hD hb (fun c _ => hHom c) (fun c _ => hOdd c) hJets hβOdd
  refine ⟨A + A₀.toReal, add_nonneg hA ENNReal.toReal_nonneg, ?_⟩
  intro ℓ hℓ hℓ₁
  obtain ⟨D₁, hD₁, hFreeze⟩ := hFreezeSymbol ℓ hℓ hℓ₁
  refine ⟨D₁.toReal + D₀.toReal, add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg, ?_⟩
  intro c hc z hz Cvar F G βc X Y
  let q (u : SchwartzMap E ℂ) (x : E) := (-Complex.I) * (B u x - B₀ c u x)
  let χ := η c ℓ
  have hCore : closedBall c (4 * ℓ) ⊆ ball c (5 * ℓ) := closedBall_subset_ball (by linarith)
  have hz₅ := hz.trans hCore
  obtain ⟨_, _, hχS, hχOne⟩ := hη c ℓ hℓ
  have hχc : HasCompactSupport (χ : E → ℂ) :=
    (isCompact_closedBall c (6 * ℓ)).of_isClosed_subset isClosed_closure (hχS.trans ball_subset_closedBall)
  have hCont (u : SchwartzMap E ℂ) : ContDiff ℝ ∞ (B u) := by
    rw [← (hB u).choose_spec]
    exact (hB u).choose.smooth _
  have hRaw (ξ : E) : ‖a c ξ‖ ≤ ‖ξ‖ * D := by
    have h := norm_symbol_shift_sub_le (a c) (hb c hc) (hHom c) D hD (hJets c hc 1 (by decide)) ξ 0
    simpa only [zero_add, homogeneous_value_zero (hHom c), sub_zero] using h
  have hLow (ξ : E) : ‖fixedRadianProfile cut ξ‖ ≤ SchwartzMap.seminorm ℝ 0 0 cut :=
    (Complex.abs_re_le_norm _).trans (by
      simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
        SchwartzMap.le_seminorm ℝ 0 0 cut (tau⁻¹ • ξ))
  have hGrowth (ξ : E) : ‖β c ξ‖ ≤ ((1 + SchwartzMap.seminorm ℝ 0 0 cut) * D) * ‖ξ‖ := by
    simp only [β, fixedInfraredSymbol, fixedRadianProfile, SchwartzMap.zero_apply, Complex.zero_re, add_zero,
      norm_mul]
    have hFactor : ‖1 - fixedRadianProfile cut ξ‖ ≤ 1 + SchwartzMap.seminorm ℝ 0 0 cut :=
      (norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add_left (hLow ξ) 1)
    exact (mul_le_mul hFactor (hRaw ξ) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hCont₀ (u : SchwartzMap E ℂ) : ContDiff ℝ ∞ (B₀ c u) :=
    contDiff_radianAction_of_linear_growth (β c) (hβ.continuous.comp (continuous_const.prodMk continuous_id))
      _ hGrowth u
  let W (i : J) : E → ℂ := (-Complex.I) • (B (z.val i) : E → ℂ)
  let W₀ (i : J) : E → ℂ := (-Complex.I) • (B₀ c (z.val i) : E → ℂ)
  let H := principalVariationDensity Cvar z.val W₀
  let Wloc (i : J) : E → ℂ := (χ : E → ℂ) * q (energyProduct χ (z.val i))
  have hWloc (i : J) : ContDiff ℝ ∞ (Wloc i) := (χ.smooth _).mul
    (contDiff_const.mul ((hCont _).sub (hCont₀ _)))
  let w (i : J) : SchwartzMap E ℂ := (hχc.mul_right (f' := q (energyProduct χ (z.val i)))).toSchwartzMap (hWloc i)
  have hw (i : J) (x : E) : w i x = (-Complex.I) * sandwichedScalarTest χ (fun v => B v - B₀ c v) (z.val i) x := by
    change χ x * ((-Complex.I) * (B _ x - B₀ c _ x)) = _
    simp only [sandwichedScalarTest, Pi.sub_apply]
    ring
  have hV := hFreeze c z.val z.property hz₅ w hw
  have hW₀ (i : J) : Differentiable ℝ (W₀ i) := (hCont₀ _).differentiable (by simp) |>.const_smul _
  have hq (i : J) : Differentiable ℝ (q (z.val i)) :=
    ((hCont _).sub (hCont₀ _)).differentiable (by simp) |>.const_mul _
  have hWV : W = W₀ + fun i => q (z.val i) := by
    funext i x
    change (-Complex.I) * B (z.val i) x = (-Complex.I) * B₀ c (z.val i) x +
      (-Complex.I) * (B (z.val i) x - B₀ c (z.val i) x)
    ring
  have hWval (i : J) : (w i : E → ℂ) = fun x =>
      (-Complex.I) * sandwichedScalarTest χ (fun v => B v - B₀ c v) (z.val i) x := funext (hw i)
  have hSplit : F - H = principalVariationDensity Cvar z.val (fun i => w i) := by
    change principalVariationDensity Cvar z.val W - principalVariationDensity Cvar z.val W₀ = _
    rw [hWV, principalVariationDensity_add_smooth_test Cvar z.val W₀ _ hW₀ hq, add_sub_cancel_left]
    exact (principalVariationDensity_eq_affinePatchSandwich Cvar z.val (fun v => B v - B₀ c v)
      χ c ℓ hℓ hz hχOne).trans (congrArg (principalVariationDensity Cvar z.val) (funext hWval).symm)
  have hAsSchwartz (i : J) : (↑((-Complex.I) • (hB (z.val i)).choose) : E → ℂ) = W i := by
    funext x
    change (-Complex.I) * (hB (z.val i)).choose x = (-Complex.I) * B (z.val i) x
    rw [congrFun (hB (z.val i)).choose_spec x]
  have hWjet (i : J) : BoundedCoordinateJet (W i) := by
    rw [← hAsSchwartz i]
    exact schwartz_bounded_coordinate_jet _
  have hWV₀ (i : J) : BoundedCoordinateJet (W₀ i) :=
    fixedInfraredTest_global_coordinateBounds cut hcut (a c) (hb c hc) (hHom c) (z.val i)
  have hCoeff : Cvar = fun d e i j k => (S d e i j k : E → ℂ) := by
    funext d e i j k x
    exact (hS d e i j k x).symm
  have hIntF : Integrable F := by
    change Integrable (principalVariationDensity Cvar z.val W)
    rw [hCoeff]
    exact principal_variation_density_integrable S z.val W hWjet
  have hIntH : Integrable H := by
    dsimp only [H]
    rw [hCoeff]
    exact principal_variation_density_integrable S z.val W₀ hWV₀
  have hI : (∫ x, (F - H) x) = principalPatchTestEnergy S z.val (fun i => w i) := by
    rw [hSplit, hCoeff, principalPatchTestEnergy,
      (principal_variation_action_derivatives S z.val _ (fun i => schwartz_bounded_coordinate_jet (w i))).1.deriv]
  have hReal : ‖(∫ x, (F x).re) - (∫ x, (H x).re)‖ₑ ≤ ‖principalPatchTestEnergy S z.val (fun i => w i)‖ₑ := by
    have hRF : (∫ x, (F x).re) = (∫ x, F x).re := integral_re hIntF
    have hRH : (∫ x, (H x).re) = (∫ x, H x).re := integral_re hIntH
    have hI₀ : (∫ x, (F - H) x) = (∫ x, F x) - ∫ x, H x := integral_sub hIntF hIntH
    rw [hRF, hRH, ← Complex.sub_re, ← hI₀, ← hI, ← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm _)
  have hX := euclideanFieldGradientNorm_lt_top z.val
  have head : ENNReal.ofReal (A * ℓ * euclideanFieldGradientL3 z.val ^ 3) =
      ENNReal.ofReal A * ENNReal.ofReal ℓ * euclideanFieldGradientNorm z.val ^ 3 := by
    rw [ENNReal.ofReal_mul (mul_nonneg hA hℓ.le), ENNReal.ofReal_mul hA, euclideanFieldGradientL3,
      ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hX.ne]
  rw [head] at hV
  have hSymbolReal := abs_cubic_freezing_of_enorm z.val _ ℓ hℓ.le _ D₁ ENNReal.ofReal_lt_top hD₁ (hReal.trans hV)
  rw [ENNReal.toReal_ofReal hA] at hSymbolReal
  have hCoef := (hFreezeCoef c hc ℓ hℓ z hz₅).2
  have hCoeffReal := abs_cubic_freezing_of_enorm z.val _ ℓ hℓ.le A₀ D₀ hA₀ hD₀ hCoef
  let Q := completeCubicEnergy (frozenActionCubicLinear G) (frozenActionCubicQuadratic G) βc z
  change |(∫ x, (H x).re) - Q| ≤ _ at hCoeffReal
  refine ⟨hIntF, ?_⟩
  change |(∫ x, (F x).re) - Q| ≤ _
  rw [show (∫ x, (F x).re) - Q = ((∫ x, (F x).re) - ∫ x, (H x).re) + ((∫ x, (H x).re) - Q) by ring]
  exact (abs_add_le _ _).trans ((add_le_add hSymbolReal hCoeffReal).trans_eq (by dsimp only [X, Y]; ring))

end Burnett.V03.Palatini
