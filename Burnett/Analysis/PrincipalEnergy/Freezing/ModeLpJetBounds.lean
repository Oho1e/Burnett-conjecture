import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedModeEnergy

set_option autoImplicit false
set_option maxHeartbeats 1350000
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal

/-- The physical complex (L^3) space on the original Euclidean chart. -/
abbrev PatchLp3 := Lp ℂ (ENNReal.ofReal 3) (volume : Measure E)

scoped instance patchLp3Fact : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

open scoped Burnett.A03

/-- The actual coordinate derivative in the Fourier construction. -/
def separatedModeCoordinateDerivative (f : SchwartzMap E ℂ) (b : E → ℝ)
    (u : SchwartzMap E ℂ) (a : Index) (x : E) : ℂ :=
  fderiv ℝ (separatedSkewAction f b u) x (EuclideanSpace.single a 1)

structure SeparatedModeLpJet (f : SchwartzMap E ℂ) (b : E → ℝ) (u : SchwartzMap E ℂ) : Prop where
  value : MemLp (separatedSkewAction f b u) (ENNReal.ofReal 3) volume
  coordinate (a : Index) : MemLp (separatedModeCoordinateDerivative f b u a) (ENNReal.ofReal 3) volume

def SeparatedModeLpJet.valueLp {f u : SchwartzMap E ℂ} {b : E → ℝ}
    (h : SeparatedModeLpJet f b u) : PatchLp3 :=
  h.value.toLp _

def SeparatedModeLpJet.coordinateLp {f u : SchwartzMap E ℂ} {b : E → ℝ}
    (h : SeparatedModeLpJet f b u) (a : Index) : PatchLp3 :=
  (h.coordinate a).toLp _

private theorem mode_gradient_norm_lt_top (u : SchwartzMap E ℂ) : energyGradientNorm u < ⊤ :=
  ((SchwartzMap.fderivCLM ℝ u).memLp _ volume).eLpNorm_lt_top

private theorem mode_profile_second_lt_top (f : SchwartzMap E ℂ) :
    eLpNorm (iteratedFDeriv ℝ 2 (f : E → ℂ)) ⊤ volume < ⊤ := by
  rw [eLpNorm_exponent_top]
  obtain ⟨A, _, h⟩ := f.decay 0 2
  exact eLpNormEssSup_lt_top_of_ae_bound (Filter.Eventually.of_forall fun x =>
    by simpa only [pow_zero, one_mul] using h x)

private theorem mode_profile_value_real (f : SchwartzMap E ℂ) :
    (eLpNorm (f : E → ℂ) ⊤ volume).toReal = schwartzProfileJetLInfinity 0 f := by
  unfold schwartzProfileJetLInfinity
  congr 1
  exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun _ => norm_iteratedFDeriv_zero.symm)

private theorem mode_profile_first_real (f : SchwartzMap E ℂ) :
    (eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume).toReal = schwartzProfileJetLInfinity 1 f := by
  unfold schwartzProfileJetLInfinity
  congr 1
  apply eLpNorm_congr_norm_ae
  apply Filter.Eventually.of_forall
  intro x
  simpa only [norm_iteratedFDeriv_zero, zero_add] using
    (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := (f : E → ℂ)) (x := x) (n := 0))

private theorem norm_lp3_from_two_terms {g : E → ℂ}
    (hg : MemLp g (ENNReal.ofReal 3) volume) (K A X B Y : ℝ≥0∞)
    (hK : K < ⊤) (hA : A < ⊤) (hX : X < ⊤) (hB : B < ⊤) (hY : Y < ⊤)
    (D : ℝ) (hD : 0 ≤ D)
    (bound : eLpNorm g (ENNReal.ofReal 3) volume ≤ K * ENNReal.ofReal D * (A * X + B * Y)) :
    ‖hg.toLp g‖ ≤ K.toReal * D * (A.toReal * X.toReal + B.toReal * Y.toReal) := by
  have hAX := ENNReal.mul_lt_top hA hX
  have hBY := ENNReal.mul_lt_top hB hY
  have fin : K * ENNReal.ofReal D * (A * X + B * Y) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top hK ENNReal.ofReal_lt_top)
    (ENNReal.add_lt_top.mpr ⟨hAX, hBY⟩)
  simpa only [Lp.norm_toLp, ENNReal.toReal_mul, ENNReal.toReal_ofReal hD,
    ENNReal.toReal_add hAX.ne hBY.ne] using ENNReal.toReal_mono fin.ne bound

/-- Fixed-test (L^3) bounds for the actual mode output and its four true
first derivatives. The gradient of the differentiated input occurs only
in the derivative convergence estimate. -/
theorem exists_separated_mode_Lp_jet_bound :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ f u : SchwartzMap E ℂ, ∃ h : SeparatedModeLpJet f b u,
        let F₀ := schwartzProfileJetLInfinity 0 f
        let F₁ := schwartzProfileJetLInfinity 1 f
        let F₂ := schwartzProfileJetLInfinity 2 f
        let X := (energyGradientNorm u).toReal
        let Y := (eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume).toReal
        ‖h.valueLp‖ ≤ K * D * (F₀ * X + F₁ * Y) ∧
        ∀ a : Index, let U := energyPartial a u
          let Xₐ := (energyGradientNorm U).toReal
          let Yₐ := (eLpNorm (U : E → ℂ) (ENNReal.ofReal 3) volume).toReal
          ‖h.coordinateLp a‖ ≤ K * D * (F₀ * Xₐ + F₁ * (Yₐ + X) + F₂ * Y) := by
  obtain ⟨V, hV, value⟩ := separated_skew_action_L3_sphere_bound
  obtain ⟨W, hW, commutator⟩ := separated_skew_coordinate_commutator_L3_sphere_bound
  let K := V.toReal + W.toReal
  have hK : 0 ≤ K := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  refine ⟨K, hK, ?_⟩
  intro b hb hom D hD jet f u
  let P := ENNReal.ofReal 3
  let F₀ := eLpNorm (f : E → ℂ) ⊤ volume
  let F₁ := eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume
  let F₂ := eLpNorm (iteratedFDeriv ℝ 2 (f : E → ℂ)) ⊤ volume
  let X := (energyGradientNorm u).toReal
  let Y := (eLpNorm (u : E → ℂ) P volume).toReal
  let U := energyPartial
  have hF₀ : F₀ < ⊤ := (f.memLp ⊤ volume).eLpNorm_lt_top
  have hF₁ : F₁ < ⊤ := ((SchwartzMap.fderivCLM ℝ f).memLp ⊤ volume).eLpNorm_lt_top
  have hF₂ : F₂ < ⊤ := mode_profile_second_lt_top f
  have valueReal (v : SchwartzMap E ℂ) :=
    norm_lp3_from_two_terms (value b hb hom D hD jet f v).1 V F₀ (energyGradientNorm v) F₁
      (eLpNorm (v : E → ℂ) P volume) hV hF₀ (mode_gradient_norm_lt_top v) hF₁
      (v.memLp P volume).eLpNorm_lt_top D hD (value b hb hom D hD jet f v).2
  let T (a : Index) (x : E) := separatedModeCoordinateDerivative f b u a x - separatedSkewAction f b (U a u) x
  have commMem (a : Index) : MemLp (T a) P volume :=
    (commutator b hb hom D hD jet f u a).1
  have commReal (a : Index) :=
    norm_lp3_from_two_terms (commMem a) W F₁ (energyGradientNorm u) F₂
      (eLpNorm (u : E → ℂ) P volume) hW hF₁ (mode_gradient_norm_lt_top u) hF₂
      (u.memLp P volume).eLpNorm_lt_top D hD (commutator b hb hom D hD jet f u a).2
  have hEq (a : Index) : separatedModeCoordinateDerivative f b u a =
      separatedSkewAction f b (U a u) + T a := by
    funext x
    simp only [T, Pi.add_apply]
    ring
  have grad (a : Index) : MemLp (separatedModeCoordinateDerivative f b u a) P volume := by
    rw [hEq a]
    exact (value b hb hom D hD jet f (U a u)).1.add (commMem a)
  let h : SeparatedModeLpJet f b u := ⟨(value b hb hom D hD jet f u).1, grad⟩
  refine ⟨h, ?_⟩
  simp only [← mode_profile_value_real f, ← mode_profile_first_real f]
  constructor
  · refine (valueReal u).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ENNReal.toReal_nonneg) hD
  · intro a
    have hLpEq : h.coordinateLp a =
        ((value b hb hom D hD jet f (U a u)).1.toLp _) + (commMem a).toLp _ := by
      rw [← MemLp.toLp_add]
      exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun (hEq a) x)
    rw [hLpEq]
    have estimate := (norm_add_le _ _).trans (add_le_add (valueReal (U a u)) (commReal a))
    refine estimate.trans ?_
    let Xₐ := (energyGradientNorm (U a u)).toReal
    let Yₐ := (eLpNorm (U a u : E → ℂ) P volume).toReal
    calc
      _ ≤ K * D * (F₀.toReal * Xₐ + F₁.toReal * Yₐ) +
          K * D * (F₁.toReal * X + F₂.toReal * Y) := by
        exact add_le_add (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ENNReal.toReal_nonneg) hD) (by positivity))
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ENNReal.toReal_nonneg) hD) (by positivity))
      _ = _ := by
        change _ = K * D * (F₀.toReal * Xₐ + F₁.toReal * (Yₐ + X) + F₂.toReal * Y)
        ring

end Burnett.A03
