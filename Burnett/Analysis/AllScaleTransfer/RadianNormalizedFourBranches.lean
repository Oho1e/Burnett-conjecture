import Burnett.Analysis.AllScaleTransfer.RadianFourBranchProperties

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.A05

open MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier
open Burnett.Analysis.ProjectiveNullCaps

private theorem radianCycle_pairedFrequency (A : E ≃L[ℝ] E) (p : Joint) :
    radianCycle (pairedFrequencyEquiv A p) = pairedFrequencyEquiv A (radianCycle p) := by
  apply Prod.ext
  · rfl
  · change -(A p.1+A p.2) = A (-(p.1+p.2))
    rw [map_neg,map_add]

/-- The same four physical branches are summed after the common
parabolic change. In particular the cutoff still uses physical ratios. -/
theorem radianTrilinearForm_normalized_bound_of_four_branches
    (A : E ≃L[ℝ] E) (ϑ : ℝ → ℝ) (hϑ : Measurable ϑ)
    (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1) (κ : ℝ)
    (m : Joint → ℂ) (hm : Measurable m) (B : ℝ) (hB : ∀ p, ‖m p‖ ≤ B)
    (f g h : SchwartzMap E ℂ) (C₀ C₁ C₂ C₃ : ℝ)
    (h0 : ‖radianTrilinearForm (radianFourBranchSymbol ϑ κ m 0 ∘ pairedFrequencyEquiv A) f g h‖ ≤
      C₀ * (triLpMass f g h 3 3 3).toReal)
    (h1 : ‖radianTrilinearForm
        (radianFourBranchSymbol ϑ κ (m ∘ radianCycle.symm) 0 ∘ pairedFrequencyEquiv A) g h f‖ ≤
      C₁ * (triLpMass g h f 3 3 3).toReal)
    (h2 : ‖radianTrilinearForm
        (radianFourBranchSymbol ϑ κ (m ∘ radianCycle) 0 ∘ pairedFrequencyEquiv A) h f g‖ ≤
      C₂ * (triLpMass h f g 3 3 3).toReal)
    (h3 : ‖radianTrilinearForm (radianFourBranchSymbol ϑ κ m 3 ∘ pairedFrequencyEquiv A) f g h‖ ≤
      C₃ * (triLpMass f g h 3 3 3).toReal) :
    ‖radianTrilinearForm (m ∘ pairedFrequencyEquiv A) f g h‖ ≤
      (C₀+C₁+C₂+C₃) * (triLpMass f g h 3 3 3).toReal := by
  let e := pairedFrequencyEquiv A
  let N (i : Fin 4) := radianFourBranchSymbol ϑ κ m i ∘ e
  let R₁ := radianFourBranchSymbol ϑ κ (m ∘ radianCycle.symm) 0 ∘ e
  let R₂ := radianFourBranchSymbol ϑ κ (m ∘ radianCycle) 0 ∘ e
  have eq1 : R₁ ∘ radianCycle = N 1 := by
    funext p
    have eq : e (radianCycle p) = radianCycle (e p) := (radianCycle_pairedFrequency A p).symm
    change radianFourBranchSymbol ϑ κ (m ∘ radianCycle.symm) 0 (e (radianCycle p)) =
      radianFourBranchSymbol ϑ κ m 1 (e p)
    rw [eq]
    let x := e p
    change radianFourBranchSymbol ϑ κ (m ∘ radianCycle.symm) 0 (radianCycle x) =
      radianFourBranchSymbol ϑ κ m 1 x
    have third : -((radianCycle x).1+(radianCycle x).2) = x.1 := by
      change -(x.2+ -(x.1+x.2)) = x.1
      abel
    simp only [radianFourBranchSymbol,radianFourBranchWeight,Function.comp_apply,
      Matrix.cons_val_zero,MeasurableEquiv.symm_apply_apply,third]
    rfl
  have eq2 : N 2 ∘ radianCycle = R₂ := by
    funext p
    have eq : e (radianCycle p) = radianCycle (e p) := (radianCycle_pairedFrequency A p).symm
    change radianFourBranchSymbol ϑ κ m 2 (e (radianCycle p)) =
      radianFourBranchSymbol ϑ κ (m ∘ radianCycle) 0 (e p)
    rw [eq]
    let x := e p
    change radianFourBranchSymbol ϑ κ m 2 (radianCycle x) =
      radianFourBranchSymbol ϑ κ (m ∘ radianCycle) 0 x
    have third : -((radianCycle x).1+(radianCycle x).2) = x.1 := by
      change -(x.2+ -(x.1+x.2)) = x.1
      abel
    simp only [radianFourBranchSymbol,radianFourBranchWeight,Function.comp_apply,
      Matrix.cons_val_zero,third]
    rfl
  have h₁ := radianTrilinearForm_cycle R₁ g h f
  have h₂ := radianTrilinearForm_cycle (N 2) f g h
  rw [eq1] at h₁
  rw [eq2] at h₂
  let T (i : Fin 4) := radianTrilinearForm (N i) f g h
  let mass := (triLpMass f g h 3 3 3).toReal
  have b₀ : ‖T 0‖ ≤ C₀ * mass := h0
  have b₁ : ‖T 1‖ ≤ C₁ * mass := by
    change ‖radianTrilinearForm (N 1) f g h‖ ≤ _
    rw [h₁]
    simpa only [mass,triLpMass,mul_assoc,mul_comm] using h1
  have b₂ : ‖T 2‖ ≤ C₂ * mass := by
    change ‖radianTrilinearForm (N 2) f g h‖ ≤ _
    rw [← h₂]
    simpa only [mass,triLpMass,mul_assoc,mul_comm,mul_left_comm] using h2
  have b₃ : ‖T 3‖ ≤ C₃ * mass := h3
  have normWeight (i : Fin 4) (p : Joint) : ‖radianFourBranchWeight ϑ κ i p‖ ≤ 4 := by
    have low (x y z : E) : ‖lowSlotWeight ϑ κ x y z‖ ≤ 1 := hRange _ (by positivity)
    fin_cases i
    · exact (low _ _ _).trans (by norm_num)
    · exact (low _ _ _).trans (by norm_num)
    · exact (low _ _ _).trans (by norm_num)
    · change ‖comparableSlotWeight ϑ κ p.1 p.2 (-(p.1+p.2))‖ ≤ 4
      unfold comparableSlotWeight
      let ℓ (x y z : E) := lowSlotWeight ϑ κ x y z
      let r := -(p.1+p.2)
      change ‖1-ℓ p.1 p.2 r-ℓ p.2 r p.1-ℓ r p.1 p.2‖ ≤ 4
      have tri := (norm_sub_le (1-ℓ p.1 p.2 r-ℓ p.2 r p.1) (ℓ r p.1 p.2)).trans
        (add_le_add_right ((norm_sub_le (1-ℓ p.1 p.2 r) (ℓ p.2 r p.1)).trans
          (add_le_add_right (norm_sub_le 1 (ℓ p.1 p.2 r)) _)) _)
      have ea : ‖ℓ p.1 p.2 r‖ ≤ 1 := low _ _ _
      have eb : ‖ℓ p.2 r p.1‖ ≤ 1 := low _ _ _
      have ec : ‖ℓ r p.1 p.2‖ ≤ 1 := low _ _ _
      rw [norm_one] at tri
      linarith only [tri,ea,eb,ec]
  have ite (i : Fin 4) : Integrable (radianTrilinearWeight (N i) f g h) := by
    have meas : Measurable (N i) :=
      (measurable_radianFourBranchSymbol ϑ hϑ κ m hm i).comp e.continuous.measurable
    refine integrable_radianTrilinearWeight_of_bounded _ meas.aestronglyMeasurable (4*B) (fun p => ?_) f g h
    change ‖radianFourBranchSymbol ϑ κ m i (e p)‖ ≤ _
    simp only [radianFourBranchSymbol,norm_mul,Complex.norm_real]
    exact mul_le_mul (normWeight i (e p)) (hB (e p)) (norm_nonneg _) (by norm_num)
  have symbol : (fun p => ∑ i : Fin 4, N i p) = m ∘ e :=
    funext fun p => radianFourBranchSymbol_sum ϑ κ m (e p)
  rw [← symbol,radianTrilinearForm_sum Finset.univ _ f g h (fun i _ => ite i)]
  change ‖∑ i : Fin 4, T i‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change ‖T 0‖ + (‖T 1‖ + (‖T 2‖ + ‖T 3‖)) ≤ (C₀+C₁+C₂+C₃)*mass
  nlinarith only [b₀,b₁,b₂,b₃]

end Burnett.A05
