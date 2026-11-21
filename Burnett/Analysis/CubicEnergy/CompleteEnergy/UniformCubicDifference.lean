import Burnett.Analysis.CubicEnergy.CompleteEnergy.UniformCompleteCubic

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Metric Burnett.RicciSymbol
open scoped ContDiff ENNReal

private def triple {F : Type} (a b c : F) : Fin 3 → F :=
  Fin.cons a (Fin.cons b (fun _ : Fin 1 => c))

@[simp] private theorem triple_zero {F : Type} (a b c : F) : triple a b c 0 = a := rfl
@[simp] private theorem triple_one {F : Type} (a b c : F) : triple a b c 1 = b := rfl
@[simp] private theorem triple_two {F : Type} (a b c : F) : triple a b c 2 = c := rfl

private theorem triple_diag {F : Type} (u : F) : triple u u u = fun _ => u := by
  funext i
  fin_cases i <;> rfl

private theorem update_triple_zero {F : Type} (a b c d : F) :
    Function.update (triple a b c) 0 d = triple d b c := by
  funext i
  fin_cases i <;> rfl

private theorem update_triple_one {F : Type} (a b c d : F) :
    Function.update (triple a b c) 1 d = triple a d c := by
  funext i
  fin_cases i <;> rfl

private theorem update_triple_two {F : Type} (a b c d : F) :
    Function.update (triple a b c) 2 d = triple a b d := by
  funext i
  fin_cases i <;> rfl

private theorem trilinear_diag_sub {F : Type} [AddCommGroup F] [Module ℝ F]
    (T : MultilinearMap ℝ (fun _ : Fin 3 => F) ℝ) (u v : F) :
    T (fun _ => u) - T (fun _ => v) =
      T (triple (u-v) u u) + T (triple v (u-v) u) + T (triple v v (u-v)) := by
  have h₀ := T.map_update_sub (triple u u u) (0 : Fin 3) u v
  have h₁ := T.map_update_sub (triple v u u) (1 : Fin 3) u v
  have h₂ := T.map_update_sub (triple v v u) (2 : Fin 3) u v
  rw [update_triple_zero,update_triple_zero,update_triple_zero] at h₀
  rw [update_triple_one,update_triple_one,update_triple_one] at h₁
  rw [update_triple_two,update_triple_two,update_triple_two] at h₂
  rw [← triple_diag u,← triple_diag v,h₀,h₁,h₂]
  ring

/-- The original energy difference is controlled uniformly by the symbol
sphere jet bound, on the same real field space and actual diagonal. -/
theorem complete_cubic_energy_difference_sphere_bound
    {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (hc : ∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l)
    (q : Index → Index → J → J → J → ℝ) :
    ∃ C₀ : ℝ≥0∞, C₀ < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) → ∀ (D : ℝ), 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ u v : RealEnergyField J,
      ‖completeCubicEnergy c q b u - completeCubicEnergy c q b v‖ₑ ≤
        (C₀ * ENNReal.ofReal D) * fieldEnergyGradientNorm (↑(u-v) : J → SchwartzMap E ℂ) *
          (fieldEnergyGradientNorm (u : J → SchwartzMap E ℂ) +
            fieldEnergyGradientNorm (v : J → SchwartzMap E ℂ))^2 := by
  obtain ⟨C₀,hC₀,est⟩ := complete_cubic_map_L3_sphere_bound c hc q
  refine ⟨C₀,hC₀,?_⟩
  intro b hb hom D hD jet u v
  let C := C₀ * ENNReal.ofReal D
  have estimate := est b hb hom D hD jet
  let T := completeSymmetricCubicMap c q b hb hom
  let U := fieldEnergyGradientNorm (u : J → SchwartzMap E ℂ)
  let V := fieldEnergyGradientNorm (v : J → SchwartzMap E ℂ)
  let N := fieldEnergyGradientNorm (↑(u-v) : J → SchwartzMap E ℂ)
  rw [← complete_cubic_map_diag c q b hb hom u,← complete_cubic_map_diag c q b hb hom v,trilinear_diag_sub]
  have head : ‖T (triple (u-v) u u)‖ₑ ≤ C * (N*U*U) := by
    simpa only [Fin.prod_univ_three,triple_zero,triple_one,triple_two] using estimate (triple (u-v) u u)
  have middle : ‖T (triple v (u-v) u)‖ₑ ≤ C * (V*N*U) := by
    simpa only [Fin.prod_univ_three,triple_zero,triple_one,triple_two] using estimate (triple v (u-v) u)
  have last : ‖T (triple v v (u-v))‖ₑ ≤ C * (V*V*N) := by
    simpa only [Fin.prod_univ_three,triple_zero,triple_one,triple_two] using estimate (triple v v (u-v))
  change ‖T (triple (u-v) u u) + T (triple v (u-v) u) + T (triple v v (u-v))‖ₑ ≤
    C*N*(U+V)^2
  calc
    _ ≤ C*(N*U*U) + C*(V*N*U) + C*(V*V*N) :=
      (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans (add_le_add head middle)) last)
    _ ≤ C*(N*U*U) + C*(V*N*U) + C*(V*V*N) + C*(V*N*U) :=
      le_add_of_nonneg_right (zero_le _)
    _ = _ := by ring

end Burnett.A02.FrequencySplit
