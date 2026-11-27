import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedLeftPrincipalFreezing

set_option autoImplicit false
set_option maxHeartbeats 6700000

noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview
open scoped ContDiff ENNReal BigOperators ComplexConjugate Topology Burnett.A03

private theorem field_support_sub_patch {J : Type} [Fintype J]
    (z : J → SchwartzMap E ℂ) (U : Set E) (hU : tsupport (fieldValueArray z) ⊆ U) (i : J) :
    tsupport (z i : E → ℂ) ⊆ U := by
  apply (closure_mono ?_).trans hU
  intro x hx
  change z i x ≠ 0 at hx
  change fieldValueArray z x ≠ 0
  intro H
  exact hx (congrArg (fun u => u i) H)

/-- Localize the coefficient difference and replace the homogeneous frozen
test by the symmetric separated test. The retained integrand has exactly
the original three placements and agrees pointwise over the whole chart. -/
theorem frozen_coefficient_energy_eq_localized {J : Type} [Fintype J]
    (C C₀ : Index → Index → J → J → J → E → ℂ)
    (d : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (f : SchwartzMap E ℂ) (b : E → ℝ) (U : Set E) (hU : IsOpen U)
    (hz : tsupport (fieldValueArray z) ⊆ U) (hf : ∀ x ∈ U, f x = 1)
    (hd : ∀ a v i j k, ∀ x ∈ U, d a v i j k x = C a v i j k x - C₀ a v i j k x) :
    principalVariationDensity C z (fun i => radianSkewAction b (z i)) -
      principalVariationDensity C₀ z (fun i => radianSkewAction b (z i)) =
      principalVariationDensity (fun a v i j k => d a v i j k) z (fun i => separatedSkewAction f b (z i)) := by
  classical
  have hSupport := field_support_sub_patch z U hz
  have hInput (i : J) : energyProduct f (z i) = z i := by
    ext x
    rw [energyProduct_apply]
    by_cases hx : x ∈ U
    · rw [hf x hx, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hSupport i h)), mul_zero]
  funext x
  change principalVariationDensity C z (fun i => radianSkewAction b (z i)) x -
    principalVariationDensity C₀ z (fun i => radianSkewAction b (z i)) x = _
  by_cases hx : x ∈ U
  · have hLocal (i : J) : separatedSkewAction f b (z i) =ᶠ[𝓝 x] radianSkewAction b (z i) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      rw [separatedSkewAction, hInput i, hf y hy, one_mul, ← two_mul]
      ring
    have hVal (i : J) : separatedSkewAction f b (z i) x = radianSkewAction b (z i) x :=
      (hLocal i).self_of_nhds
    have hD (i : J) : fderiv ℝ (separatedSkewAction f b (z i)) x = fderiv ℝ (radianSkewAction b (z i)) x :=
      (hLocal i).fderiv_eq
    simp only [principalVariationDensity, hVal, hD,
      fun a v i j k => hd a v i j k x hx, sub_mul, Finset.sum_sub_distrib]
  · have off (i : J) : x ∉ tsupport (z i : E → ℂ) := fun h => hx (hSupport i h)
    have hv (i : J) : z i x = 0 := image_eq_zero_of_notMem_tsupport (off i)
    have hd0 (i : J) (j : Index) : energyPartial j (z i) x = 0 := by
      change fderiv ℝ (z i : E → ℂ) x (EuclideanSpace.single j 1) = 0
      rw [fderiv_of_notMem_tsupport ℝ (off i), ContinuousLinearMap.zero_apply]
    simp only [principalVariationDensity, hv, hd0, zero_mul, mul_zero, add_zero, Finset.sum_const_zero, sub_zero]

private theorem frozen_coefficient_cubic_budget (U C₁ V W L P X Y F₀ F₁ F₂ : ℝ≥0∞)
    (hF₀ : F₀ ≤ 1) (hF₁ : F₁ * L ≤ V) (hF₂ : F₂ * L ^ 2 ≤ W) (hY : Y ≤ P * L * X) :
    separatedCubicBoundRhs (U * L) C₁ F₀ F₁ F₂ X Y ≤
      (U + (U * V + C₁) * P + U * W * P ^ 2) * L * X ^ 3 := by
  have hv : U * L * F₀ * X ^ 3 ≤ U * L * X ^ 3 := by
    simpa only [mul_one] using mul_le_mul' (mul_le_mul_left' hF₀ (U * L)) (le_rfl (a := X ^ 3))
  have hd : (U * L * F₁ + C₁ * F₀) * Y * X ^ 2 ≤ (U * V + C₁) * P * L * X ^ 3 := by
    have h₁ : U * L * F₁ ≤ U * V := by
      calc
        _ = U * (F₁ * L) := by ring
        _ ≤ _ := mul_le_mul_left' hF₁ U
    have h₀ : C₁ * F₀ ≤ C₁ := by simpa only [mul_one] using mul_le_mul_left' hF₀ C₁
    calc
      _ ≤ (U * V + C₁) * (P * L * X) * X ^ 2 := mul_le_mul' (mul_le_mul' (add_le_add h₁ h₀) hY) le_rfl
      _ = _ := by ring
  have hdd : U * L * F₂ * Y ^ 2 * X ≤ U * W * P ^ 2 * L * X ^ 3 := by
    calc
      _ ≤ U * L * F₂ * (P * L * X) ^ 2 * X := mul_le_mul' (mul_le_mul_left' (pow_le_pow_left' hY 2) _) le_rfl
      _ = U * (F₂ * L ^ 2) * P ^ 2 * L * X ^ 3 := by ring
      _ ≤ _ := mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul_left' hF₂ U) le_rfl) le_rfl) le_rfl
  exact (add_le_add (add_le_add hv hd) hdd).trans_eq (by ring)

/-- Freeze the actual coefficient entries at the same patch center using
only the first differentiated coefficient and the patch-scale jets. -/
theorem exists_frozen_coefficient_principal_energy_bound {J : Type} [Fintype J] :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) →
      (∀ ξ, b (-ξ) = -b ξ) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (C : Index → Index → J → J → J → E → ℂ)
        (d : Index → Index → J → J → J → SchwartzMap E ℂ)
        (z : J → SchwartzMap E ℂ) (f : SchwartzMap E ℂ) (c : E) (R ℓ : ℝ),
      0 < R → 0 < ℓ → tsupport (fieldValueArray z) ⊆ ball c (R * ℓ) →
      (∀ x ∈ ball c (R * ℓ), f x = 1) → (∀ x, conj (f x) = f x) →
      (∀ j x, conj (z j x) = z j x) → (∀ a v i j k, d a v i j k = d v a i k j) →
      (∀ a v i j k, ∀ x ∈ ball c (R * ℓ), d a v i j k x = C a v i j k x - C a v i j k c) →
      ∀ U B V W : ℝ≥0∞,
      (∀ a v i j k, eLpNorm (d a v i j k : E → ℂ) ⊤ volume ≤ U * ENNReal.ofReal ℓ) →
      (∀ a v i j k l, eLpNorm (energyPartial l (d a v i j k) : E → ℂ) ⊤ volume ≤ B) →
      eLpNorm (f : E → ℂ) ⊤ volume ≤ 1 →
      eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume * ENNReal.ofReal ℓ ≤ V →
      eLpNorm (iteratedFDeriv ℝ 2 (f : E → ℂ)) ⊤ volume * ENNReal.ofReal ℓ ^ 2 ≤ W →
      let w (i : J) := radianSkewAction b (z i)
      let Cc a v i j k (_ : E) := C a v i j k c
      let P := ENNReal.ofReal (3 * R)
      ‖∫ x, principalVariationDensity C z w x - principalVariationDensity Cc z w x‖ₑ ≤
        K * ENNReal.ofReal D * (U + (U * V + B) * P + U * W * P ^ 2) *
          ENNReal.ofReal ℓ * euclideanFieldGradientNorm z ^ 3 := by
  obtain ⟨K, hK, bound⟩ := separated_principal_variation_bound (J := J)
  refine ⟨K, hK, ?_⟩
  intro b hb hHom hOdd D hD hJets C d z f c R ℓ hR hℓ hz hf hReal hzReal hSymm hd
    U B V W hValue hDeriv hF₀ hF₁ hF₂ w Cc P
  have hP := euclidean_field_local_poincare_eLpNorm z c (R * ℓ) (mul_pos hR hℓ) hz
  have hScale : ENNReal.ofReal (3 * (R * ℓ)) = P * ENNReal.ofReal ℓ := by
    dsimp only [P]
    rw [← mul_assoc, ENNReal.ofReal_mul (by positivity : 0 ≤ 3 * R)]
  rw [hScale] at hP
  have hEq := frozen_coefficient_energy_eq_localized C Cc d z f b (ball c (R * ℓ)) isOpen_ball hz hf hd
  change ‖∫ x, (principalVariationDensity C z w - principalVariationDensity Cc z w) x‖ₑ ≤ _
  rw [hEq]
  exact (bound b hb hHom hOdd D hD hJets f d z _ _ hValue hDeriv hReal hSymm hzReal).trans
    ((mul_le_mul_left' (frozen_coefficient_cubic_budget U B V W _ P _ _ _ _ _ hF₀ hF₁ hF₂ hP) _).trans_eq (by ring))

end Burnett.A03
