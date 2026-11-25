import Burnett.Analysis.FrozenTransport.CubicCoefficientFunctional

set_option autoImplicit false
set_option maxRecDepth 5800
set_option maxHeartbeats 11000000
noncomputable section

namespace Burnett.A02.FrequencySplit

open Filter MeasureTheory Metric Burnett.RicciSymbol
open scoped BigOperators ContDiff ENNReal

private def coefficientAtom {I : Type} (i : I) : I → ℝ := by
  classical
  exact fun j => if i = j then 1 else 0

private theorem sum_coefficientAtom {I : Type} [Fintype I] (w : I → ℝ) (j : I) :
    (∑ i, w i * coefficientAtom i j) = w j := by
  classical
  simp [coefficientAtom, mul_ite]

private def linearCoefficientSwap {J : Type} (x : CubicLinearIndex J) : CubicLinearIndex J :=
  (((x.1.1.2, x.1.1.1), (x.1.2.2, x.1.2.1)), x.2)

private theorem linearCoefficientSwap_involutive {J : Type} (x : CubicLinearIndex J) :
    linearCoefficientSwap (linearCoefficientSwap x) = x := rfl

private def symmetricCoefficientAtom {J : Type} (i : CubicLinearIndex J) : CubicLinearIndex J → ℝ :=
  fun j => (coefficientAtom i j + coefficientAtom i (linearCoefficientSwap j)) / 2

private theorem symmetricCoefficientAtom_swap {J : Type} (i x : CubicLinearIndex J) :
    symmetricCoefficientAtom i (linearCoefficientSwap x) = symmetricCoefficientAtom i x := by
  rw [symmetricCoefficientAtom, symmetricCoefficientAtom, linearCoefficientSwap_involutive, add_comm]

private def linearEnergyAtom {J : Type} (a : CubicLinearIndex J) : EnergyIndex J → J → ℝ :=
  fun k l => symmetricCoefficientAtom a (k, l)

private theorem linearEnergyAtom_symmetry {J : Type} (x : CubicLinearIndex J) (a d : Index) (i j l : J) :
    linearEnergyAtom x ((a,d),(i,j)) l = linearEnergyAtom x ((d,a),(j,i)) l :=
  (symmetricCoefficientAtom_swap x (((a,d),(i,j)),l)).symm

private def quadraticEnergyAtom {J : Type} (t : CubicQuadraticIndex J) :
    Index → Index → J → J → J → ℝ :=
  fun a d i j k => coefficientAtom t (k, ((a,i),(d,j)))

private theorem symmetric_coefficient_expansion {J : Type} [Fintype J]
    (w : CubicLinearIndex J → ℝ) (hw : ∀ j, w (linearCoefficientSwap j) = w j) :
    w = ∑ i, w i • symmetricCoefficientAtom i := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    w j = (w j + w (linearCoefficientSwap j)) / 2 := by rw [hw]; ring
    _ = ((∑ i, w i * coefficientAtom i j) +
        (∑ i, w i * coefficientAtom i (linearCoefficientSwap j))) / 2 := by
      rw [sum_coefficientAtom, sum_coefficientAtom]
    _ = _ := by
      rw [← Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by unfold symmetricCoefficientAtom; ring

private theorem coefficient_evaluation_sum {J : Type} [Fintype J]
    (F : ((CubicLinearIndex J → ℝ) × (CubicQuadraticIndex J → ℝ)) →ₗ[ℝ] ℝ)
    (w₁ : CubicLinearIndex J → ℝ) (w₂ : CubicQuadraticIndex J → ℝ)
    (hw : ∀ j, w₁ (linearCoefficientSwap j) = w₁ j) :
    F (w₁, w₂) = (∑ i, w₁ i * F (symmetricCoefficientAtom i, 0)) +
      (∑ i, w₂ i * F (0, coefficientAtom i)) := by
  let FL := F.comp (LinearMap.inl ℝ (CubicLinearIndex J → ℝ) (CubicQuadraticIndex J → ℝ))
  let FQ := F.comp (LinearMap.inr ℝ (CubicLinearIndex J → ℝ) (CubicQuadraticIndex J → ℝ))
  have hSplit : F (w₁, w₂) = FL w₁ + FQ w₂ := by
    change F (w₁, w₂) = F (w₁, 0) + F (0, w₂)
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have hL : FL w₁ = ∑ i, w₁ i * F (symmetricCoefficientAtom i, 0) := calc
    _ = FL (∑ i, w₁ i • symmetricCoefficientAtom i) := congrArg FL (symmetric_coefficient_expansion w₁ hw)
    _ = _ := by simp [map_sum, FL, smul_eq_mul]
  have hExpansion : w₂ = ∑ i, w₂ i • coefficientAtom i := by
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (sum_coefficientAtom w₂ j).symm
  have hQ : FQ w₂ = ∑ i, w₂ i * F (0, coefficientAtom i) := calc
    _ = FQ (∑ i, w₂ i • coefficientAtom i) := congrArg FQ hExpansion
    _ = _ := by simp [map_sum, FQ, smul_eq_mul]
  rw [hSplit, hL, hQ]

/-- The same fixed-infrared complete energy has a continuity constant
uniform over bounded arrays of both coefficients. The exchange symmetry is
preserved separately by every quasilinear atom. -/
theorem fixed_infrared_complete_uniform_coefficient_box {J : Type} [Fintype J]
    (cut add : SchwartzMap E ℂ) (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ), 0 ≤ B →
      ∀ (c : EnergyIndex J → J → ℝ) (q : Index → Index → J → J → J → ℝ),
      (∀ a d i j l, c ((a,d),(i,j)) l = c ((d,a),(j,i)) l) →
      (∀ k l, |c k l| ≤ B) → (∀ a d i j k, |q a d i j k| ≤ B) →
      ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ u v : RealEnergyField J,
        |completeCubicEnergy c q (fixedInfraredSymbol cut add b) u -
          completeCubicEnergy c q (fixedInfraredSymbol cut add b) v| ≤
          (C * B * (D + 1)) * euclideanFieldW13 (↑(u-v) : J → SchwartzMap E ℂ) *
            (euclideanFieldW13 (u : J → SchwartzMap E ℂ) + euclideanFieldW13 (v : J → SchwartzMap E ℂ))^2 := by
  let c0 : EnergyIndex J → J → ℝ := 0
  let q0 : Index → Index → J → J → J → ℝ := 0
  choose CL hCL hLin using fun i : CubicLinearIndex J =>
    fixed_infrared_complete_continuity_euclidean (linearEnergyAtom i) (linearEnergyAtom_symmetry i)
      q0 cut add hcut hadd
  choose CQ hCQ hQuad using fun i : CubicQuadraticIndex J =>
    fixed_infrared_complete_continuity_euclidean c0 (fun _ _ _ _ _ => rfl) (quadraticEnergyAtom i)
      cut add hcut hadd
  obtain ⟨_, _, _, _, _, _, hMem⟩ := fixedInfraredSymbol_W1p_bound cut add hcut hadd 3 (by norm_num)
  let C := (∑ i, CL i) + ∑ i, CQ i
  have hC : 0 ≤ C := add_nonneg (Finset.sum_nonneg fun i _ => hCL i) (Finset.sum_nonneg fun i _ => hCQ i)
  refine ⟨C, hC, ?_⟩
  intro B hB c q hc hcBound hqBound b hb hom D hD jets u v
  let m := fixedInfraredSymbol cut add b
  have hm (f : SchwartzMap E ℂ) : MemLp (radianAction m f) (ENNReal.ofReal 3) volume :=
    (hMem b hb hom D hD (fun n hn => jets n (hn.trans (by norm_num))) f).1
  let F := cubicCoefficientFunctional m u hm - cubicCoefficientFunctional m v hm
  let X := euclideanFieldW13 (↑(u-v) : J → SchwartzMap E ℂ)
  let Y := (euclideanFieldW13 (u : J → SchwartzMap E ℂ) + euclideanFieldW13 (v : J → SchwartzMap E ℂ))^2
  have hLinAtom (i : CubicLinearIndex J) :
      |F (symmetricCoefficientAtom i, 0)| ≤ CL i * (D + 1) * X * Y := by
    have h := hLin i b hb hom D hD jets u v
    rw [completeCubicEnergy_eq_coefficientFunctional _ _ _ _ hm,
      completeCubicEnergy_eq_coefficientFunctional _ _ _ _ hm] at h
    exact h
  have hQuadAtom (i : CubicQuadraticIndex J) :
      |F (0, coefficientAtom i)| ≤ CQ i * (D + 1) * X * Y := by
    have h := hQuad i b hb hom D hD jets u v
    rw [completeCubicEnergy_eq_coefficientFunctional _ _ _ _ hm,
      completeCubicEnergy_eq_coefficientFunctional _ _ _ _ hm] at h
    exact h
  have hSwap (j : CubicLinearIndex J) :
      cubicLinearEntries c (linearCoefficientSwap j) = cubicLinearEntries c j := by
    rcases j with ⟨⟨⟨a, d⟩, ⟨i, k⟩⟩, l⟩
    exact (hc a d i k l).symm
  have hLinear (i : CubicLinearIndex J) :
      |cubicLinearEntries c i * F (symmetricCoefficientAtom i, 0)| ≤ B * (CL i * (D + 1) * X * Y) := by
    rw [abs_mul]
    exact mul_le_mul (hcBound i.1 i.2) (hLinAtom i) (abs_nonneg _) hB
  have hQuadratic (i : CubicQuadraticIndex J) :
      |cubicQuadraticEntries q i * F (0, coefficientAtom i)| ≤ B * (CQ i * (D + 1) * X * Y) := by
    rw [abs_mul]
    exact mul_le_mul (hqBound i.2.1.1 i.2.2.1 i.2.1.2 i.2.2.2 i.1) (hQuadAtom i) (abs_nonneg _) hB
  rw [completeCubicEnergy_eq_coefficientFunctional _ _ _ _ hm,
    completeCubicEnergy_eq_coefficientFunctional _ _ _ _ hm]
  change |F (cubicLinearEntries c, cubicQuadraticEntries q)| ≤ _
  rw [coefficient_evaluation_sum F _ _ hSwap]
  calc
    _ ≤ (∑ i, |cubicLinearEntries c i * F (symmetricCoefficientAtom i, 0)|) +
        (∑ i, |cubicQuadraticEntries q i * F (0, coefficientAtom i)|) :=
      (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ (∑ i, B * (CL i * (D + 1) * X * Y)) + ∑ i, B * (CQ i * (D + 1) * X * Y) :=
      add_le_add (Finset.sum_le_sum fun i _ => hLinear i) (Finset.sum_le_sum fun i _ => hQuadratic i)
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      dsimp only [C]
      ring

end Burnett.A02.FrequencySplit
